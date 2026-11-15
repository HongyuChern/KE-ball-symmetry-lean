import KEBall.DirichletPolynomialRemainderEnergy
import KEBall.DirichletRemainderTame

/-! Energy estimates for a continuous density whose actual differences
are bounded by lower Hessian energies of the unknown potential. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_dirichlet_dependent_density_error_energy_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : ContinuousOn f (closedUnitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hDensity : ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n,
        (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t f (k + 1) x) ^ 2 ∂volume0 n) ≤
      B * dirichletFlowLowerHessianEnergy u S hS (k + 1) t + B) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian
          (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u (k + 1)) x
            (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * (∫ x in unitBall n,
          (dirichletIteratedPotentialDeterminantError (orthogonalFlow S hS t) t u k x) ^ 2 ∂volume0 n) +
        C * dirichletFlowLowerHessianEnergy u S hS (k + 1) t + C := by
  obtain ⟨ε, hε, A, hA, hEstimate⟩ :=
    exists_dirichlet_closedBall_functional_perturbation_estimate hn hu huS hu0 hPos
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
    continuousOn_dirichletIteratedOrthogonalDifference R t hf (k + 1)
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
      C * (∫ x in unitBall n, (e x) ^ 2 ∂volume0 n) +
        C * dirichletFlowLowerHessianEnergy u S hS (k + 1) t + C
  have hLow0 : 0 ≤ dirichletFlowLowerHessianEnergy u S hS (k + 1) t :=
    Finset.sum_nonneg (fun j _ => dirichletFlowHessianEnergy_nonneg u S hS j t)
  have hLow := mul_le_mul_of_nonneg_right hBase hLow0
  nlinarith only [hBound, hDen, hErr, hBase, hLow]


theorem exists_dirichlet_dependent_density_polynomial_energy_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : ContinuousOn f (closedUnitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hDensity : ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n,
        (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t f (k + 1) x) ^ 2 ∂volume0 n) ≤
      B * dirichletFlowLowerHessianEnergy u S hS (k + 1) t + B) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u (k + 1)) x
          (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * (∫ x in unitBall n,
          ((dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x).re) ^ 2 ∂volume0 n) +
        C * (∑ j ∈ Finset.range (k + 1), ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n) + C := by
  obtain ⟨δ₀, hδ₀, A, hA, hEnergy⟩ :=
    exists_dirichlet_dependent_density_error_energy_bound hn hu huS hu0 hPos hf hEq S hS k hB hDensity
  obtain ⟨δ₁, hδ₁, M, hM, hLeading⟩ := exists_dirichlet_iterated_leading_field_uniform_bound hu S hS k
  let K : ℝ := 3 * (M * (1 + 2 * ‖S‖) ^ (k + 1)) ^ 2 * (k + 1 : ℝ)
  let T : ℝ := 3 * (M * (2 * (k + 1 : ℝ) * ‖S‖)) ^ 2 * (2 * n : ℝ) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hc : ContinuousAt (fun t : ℝ => A * T * t ^ 2) 0 := by fun_prop
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, A * T * t ^ 2 < 1 / 2 :=
    hc.eventually (gt_mem_nhds (by norm_num : A * T * (0 : ℝ) ^ 2 < 1 / 2))
  obtain ⟨δ₂, hδ₂, hTime⟩ := Metric.eventually_nhds_iff.mp hsmall
  let C : ℝ := 8 * A + 2 * A * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁ hδ₂), C, hC, ?_⟩
  intro t ht htδ
  dsimp only
  have ht₀ : |t| < δ₀ := htδ.trans_le (min_le_left _ _)
  have ht₁ : |t| < δ₁ := htδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht₂ : |t| < δ₂ := htδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let R := orthogonalFlow S hS t
  let E := ∫ x in unitBall n, ∑ i, ∑ j,
    (dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u (k + 1)) x
      (e[n] i) (e[n] j)) ^ 2 ∂volume0 n
  let P := ∫ x in unitBall n,
    ((dirichletDeterminantDifferenceRemainder R t (dirichletWithinComplexHessian u) k x).re) ^ 2 ∂volume0 n
  let L := ∑ j ∈ Finset.range (k + 1), ∫ x in unitBall n,
    ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n
  have hE0 : 0 ≤ E := integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hP0 : 0 ≤ P := integral_nonneg (fun _ => sq_nonneg _)
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hErr := integral_dirichlet_iterated_potential_error_sq_le hn hu S hS k hM ht (hLeading t ht₁)
  have hE := (hEnergy t ht ht₀).trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hErr hA) le_rfl) le_rfl)
  have hs : A * T * t ^ 2 ≤ 1 / 2 :=
    (hTime (show dist t 0 < δ₂ by simpa only [dist_zero_right, Real.norm_eq_abs] using ht₂)).le
  have hsE := mul_le_mul_of_nonneg_right hs hE0
  have hp : 6 * A * P ≤ C * P := mul_le_mul_of_nonneg_right
    (show 6 * A ≤ C by dsimp [C]; nlinarith only [hA, mul_nonneg hA hK]) hP0
  have hl : (2 * A * K + 2 * A) * L ≤ C * L := mul_le_mul_of_nonneg_right
    (show 2 * A * K + 2 * A ≤ C by dsimp [C]; linarith) hL0
  have hb : 2 * A ≤ C := by dsimp [C]; nlinarith only [hA, mul_nonneg hA hK]
  change E ≤ C * P + C * L + C
  change E ≤ A * (3 * P + K * L + T * t ^ 2 * E) + A * L + A at hE
  nlinarith only [hE, hsE, hp, hl, hb]


end KEBall
