import KEBall.DirichletDependentDensityEnergy
import KEBall.DirichletExponentialEnergy

/-! All fixed angular-difference orders of the real Hessian for the
self-consistent equation det(ddc u) = c exp(a u). The density is not
assumed smooth on the closed ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff

namespace KEBall

theorem exists_dirichlet_exponential_iterated_hessian_lower_energy_bound {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      dirichletFlowHessianEnergy u S hS (k + 1) t ≤
        C * dirichletFlowLowerHessianEnergy u S hS (k + 1) t + C := by
  obtain ⟨B₀, hB₀, hDensity⟩ :=
    exists_exponential_density_difference_lower_hessian_energy hn hu huS hu0 a c S hS k
  have hf : ContinuousOn (fun x => c * Real.exp (a * u x)) (closedUnitBall n) :=
    (Real.continuous_exp.comp_continuousOn (hu.continuousOn.const_mul a)).const_mul c
  obtain ⟨δ, hδ, C₀, hC₀, hRaw⟩ :=
    exists_dirichlet_dependent_density_polynomial_energy_bound hn hu huS hu0 hPos hf hEq S hS k
      hB₀ (fun t ht => (hDensity t ht).trans (le_add_of_nonneg_right hB₀))
  let d : ℝ := (2 * n : ℝ) ^ 2
  have hd : 0 ≤ d := sq_nonneg _
  let A := d * C₀
  have hA : 0 ≤ A := mul_nonneg hd hC₀
  let ε := 1 / (2 * (A + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨B, hB, hRem⟩ := exists_dirichlet_determinant_remainder_tame_bound hn hu huS hu0 S hS k hε
  let C := 2 * A * (B + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCap : A * ε ≤ 1 / 2 := by
    calc
      A * ε ≤ (A + 1) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
      _ = 1 / 2 := by dsimp [ε]; field_simp [show A + 1 ≠ 0 by positivity]
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro t ht htδ
  let R := orthogonalFlow S hS t
  let r (x : E n) := dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x
  let N := ∫ x in unitBall n, ‖r x‖ ^ 2 ∂volume0 n
  let En := dirichletFlowHessianEnergy u S hS (k + 1) t
  let Low := dirichletFlowLowerHessianEnergy u S hS (k + 1) t
  have hRC : ContinuousOn r (closedUnitBall n) :=
    (dirichletDeterminantDifferenceRemainder_tame hn hu huS hu0 S hS).1 t ht
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {g : E n → ℝ} (hg : ContinuousOn g (closedUnitBall n)) :
      IntegrableOn g (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hg 1).integrable le_rfl
  have hRe : (∫ x in unitBall n, (r x).re ^ 2 ∂volume0 n) ≤ N :=
    setIntegral_mono_on (hInt ((Complex.continuous_re.comp_continuousOn hRC).pow 2))
      (hInt (hRC.norm.pow 2)) measurableSet_ball (fun x _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (r x)) 2)
  have hq := contDiffOn_dirichletIteratedOrthogonalDifference R t hu (k + 1)
  have hNorm := integral_norm_withinHessian_sq_le_entries hn hq
  have hEntries := (hRaw t ht htδ).trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hRe hC₀) le_rfl) le_rfl)
  have hEN : En ≤ A * N + A * Low + A := by
    exact (hNorm.trans (mul_le_mul_of_nonneg_left hEntries hd)).trans_eq (by dsimp only [A, Low, dirichletFlowLowerHessianEnergy, dirichletFlowHessianEnergy]; ring)
  have hRN : N ≤ ε * En + B * Low + B := hRem t ht
  have hWeighted := mul_le_mul_of_nonneg_left hRN hA
  have hAbsorb := mul_le_mul_of_nonneg_right hCap (dirichletFlowHessianEnergy_nonneg u S hS (k + 1) t)
  change En ≤ C * Low + C
  change A * ε * En ≤ 1 / 2 * En at hAbsorb
  dsimp only [C]
  nlinarith only [hEN, hWeighted, hAbsorb]

theorem exists_dirichlet_exponential_all_order_uniform_hessian_bound {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      ∀ j ≤ k, dirichletFlowHessianEnergy u S hS j t ≤ C := by
  induction k with
  | zero =>
    refine ⟨1, zero_lt_one, ∫ x in unitBall n, ‖dirichletWithinRealHessian u x‖ ^ 2 ∂volume0 n,
      integral_nonneg (fun _ => sq_nonneg _), ?_⟩
    intro t ht htδ j hj
    have hj0 : j = 0 := by omega
    subst j
    exact le_rfl
  | succ k ih =>
    obtain ⟨δ₀, hδ₀, B, hB, hPrev⟩ := ih
    obtain ⟨δ₁, hδ₁, A, hA, hNext⟩ :=
      exists_dirichlet_exponential_iterated_hessian_lower_energy_bound hn hu huS hu0 hPos a c hEq S hS k
    let C := max B (A * ((k + 1 : ℝ) * B) + A)
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, C, hB.trans (le_max_left _ _), ?_⟩
    intro t ht htδ j hj
    have ht₀ := htδ.trans_le (min_le_left _ _)
    have ht₁ := htδ.trans_le (min_le_right _ _)
    by_cases he : j = k + 1
    · subst j
      have hLow : dirichletFlowLowerHessianEnergy u S hS (k + 1) t ≤ (k + 1 : ℝ) * B := by
        calc
          _ ≤ ∑ j ∈ Finset.range (k + 1), B := Finset.sum_le_sum (fun j hj =>
            hPrev t ht ht₀ j (by have h := Finset.mem_range.mp hj; omega))
          _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      exact ((hNext t ht ht₁).trans (add_le_add (mul_le_mul_of_nonneg_left hLow hA) le_rfl)).trans (le_max_right _ _)
    · exact (hPrev t ht ht₀ j (by omega)).trans (le_max_left _ _)

theorem exists_dirichlet_exponential_orthogonal_iterated_difference_uniform_hessian_bound {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = c * Real.exp (a * u x))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n,
        ‖dirichletWithinRealHessian
          (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u k) x‖ ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨δ, hδ, C, hC, hBound⟩ := exists_dirichlet_exponential_all_order_uniform_hessian_bound hn hu huS hu0 hPos a c hEq S hS k
  exact ⟨δ, hδ, C, hC, fun t ht htδ => hBound t ht htδ k le_rfl⟩


end KEBall
