import KEBall.DirichletIteratedPotentialEquation
import KEBall.DirichletFunctionalPerturbation

/-! The actual global energy estimate for each fixed positive difference order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem contDiffOn_dirichletIteratedOrthogonalDifference_ball {n : ℕ} {m : ℕ∞ω}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ m u (unitBall n)) (k : ℕ) :
    ContDiffOn ℝ m (dirichletIteratedOrthogonalDifference R τ u k) (unitBall n) := by
  induction k with
  | zero => exact hu
  | succ k ih => exact contDiffOn_dirichletOrthogonalDifference_ball R τ ih

theorem exists_integral_dirichlet_iterated_density_difference_bound {n : ℕ}
    (hn : 0 < n) {f : E n → ℝ} (hf : SmoothNear (closedUnitBall n) f)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n,
        (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t f k x) ^ 2 ∂volume0 n) ≤ C := by
  simpa only [dirichletIteratedFieldDifference_real, Real.norm_eq_abs, sq_abs] using
    exists_integral_dirichlet_smooth_field_iterated_difference_sq_bound hn
      (fun x hx => hf.contDiffAt hx) S hS k

theorem exists_dirichlet_iterated_potential_error_energy_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian
          (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u (k + 1)) x
            (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * (∫ x in unitBall n,
          (dirichletIteratedPotentialDeterminantError (orthogonalFlow S hS t) t u k x) ^ 2 ∂volume0 n) + C := by
  obtain ⟨ε, hε, A, hA, hEstimate⟩ :=
    exists_dirichlet_closedBall_functional_perturbation_estimate hn hu huS hu0 hPos
  obtain ⟨B, hB, hDensity⟩ := exists_integral_dirichlet_iterated_density_difference_bound hn hf S hS (k + 1)
  obtain ⟨δ, hδ, hNear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_dirichletDeterminantLeadingField_close hu S hS k hε)
  let C := 2 * A + 2 * A * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro t ht htδ
  let R := orthogonalFlow S hS t
  let q := dirichletIteratedOrthogonalDifference R t u (k + 1)
  let F := dirichletIteratedOrthogonalDifference R t f (k + 1)
  let e := dirichletIteratedPotentialDeterminantError R t u k
  let g (x : E n) := F x - e x
  have hq := contDiffOn_dirichletIteratedOrthogonalDifference R t hu (k + 1)
  have hqS := contDiffOn_dirichletIteratedOrthogonalDifference_ball R t huS (k + 1)
  have hq0 := dirichletIteratedOrthogonalDifference_zero_on_sphere R t hu0 (k + 1)
  have hF : ContinuousOn F (closedUnitBall n) :=
    continuousOn_dirichletIteratedOrthogonalDifference R t
      (fun x hx => (hf.contDiffAt hx).continuousAt.continuousWithinAt) (k + 1)
  have he : ContinuousOn e (closedUnitBall n) :=
    continuousOn_dirichletIteratedPotentialDeterminantError R t hu k
  have hg : ContinuousOn g (closedUnitBall n) := hF.sub he
  have hNearT := hNear (show dist t 0 < δ by simpa only [dist_zero_right, Real.norm_eq_abs] using htδ)
  have hEnergy := hEstimate hq hqS hq0 hg
    (fun x hx => (hNearT x (ball_subset_closedBall hx)).le)
    (fun x hx => dirichlet_iterated_potential_determinant_equation R t hu hEq k hx)
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {h : E n → ℝ} (hh : ContinuousOn h (closedUnitBall n)) :
      IntegrableOn h (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hh 1).integrable le_rfl
  have hG : (∫ x in unitBall n, (g x) ^ 2 ∂volume0 n) ≤
      2 * (∫ x in unitBall n, (F x) ^ 2 ∂volume0 n) +
      2 * (∫ x in unitBall n, (e x) ^ 2 ∂volume0 n) := by
    have h := setIntegral_mono_on (hInt (hg.pow 2))
      (hInt (((hF.pow 2).const_mul 2).add ((he.pow 2).const_mul 2))) measurableSet_ball
      (fun x _ => by dsimp [g]; nlinarith only [sq_nonneg (F x + e x)])
    have hAdd := integral_add ((hInt (hF.pow 2)).const_mul 2) ((hInt (he.pow 2)).const_mul 2)
    simp only [Pi.add_apply, Pi.pow_apply] at h
    simp only [Pi.pow_apply] at hAdd
    rw [hAdd, integral_const_mul, integral_const_mul] at h
    exact h
  have hEr : 0 ≤ ∫ x in unitBall n, (e x) ^ 2 ∂volume0 n := integral_nonneg (fun _ => sq_nonneg _)
  have hCap : 2 * A ≤ C := by dsimp [C]; nlinarith only [mul_nonneg hA hB]
  have hBase : 2 * A * B ≤ C := by dsimp [C]; nlinarith only [hA]
  have hBound := hEnergy.trans (mul_le_mul_of_nonneg_left hG hA)
  have hDen := mul_le_mul_of_nonneg_left (hDensity t ht) (by positivity : 0 ≤ 2 * A)
  have hErr := mul_le_mul_of_nonneg_right hCap hEr
  change (∫ x in unitBall n, ∑ i, ∑ j,
    (dirichletWithinRealHessian q x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
      C * (∫ x in unitBall n, (e x) ^ 2 ∂volume0 n) + C
  nlinarith only [hBound, hDen, hErr, hBase]

end KEBall
