import KEBall.DirichletSecondDiscreteEnergy
import KEBall.DirichletDiscreteHessianQuartic

/-!
# Uniform L2 bounds for second unitary differences of the actual potential

The quartic term is absorbed using a small continuous Hessian remainder.
No third or fourth boundary derivative of the potential is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem dirichletFieldDifference_real {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (f : E n → ℝ) :
    dirichletFieldDifference R τ f = dirichletOrthogonalDifference R τ f := by
  funext x
  simp only [dirichletFieldDifference, dirichletOrthogonalDifference,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem integral_norm_withinHessian_sq_le_entries {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    (∫ x in unitBall n, ‖dirichletWithinRealHessian u x‖ ^ 2 ∂volume0 n) ≤
      (2 * n : ℝ) ^ 2 * ∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian u x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n := by
  let H := dirichletWithinRealHessian u
  have hH := continuousOn_dirichletWithinRealHessian hu
  have hSum : ContinuousOn (fun x => ∑ i, ∑ j, (H x (e[n] i) (e[n] j)) ^ 2)
      (closedUnitBall n) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((hH.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have h := setIntegral_mono_on (hInt (hH.norm.pow 2))
    (hInt (hSum.const_mul ((2 * n : ℝ) ^ 2))) measurableSet_ball
    (fun x _ => norm_dirichlet_bilinear_sq_le_sum_entries (H x))
  rw [integral_const_mul] at h
  exact h

theorem exists_integral_dirichlet_second_difference_density_bound {n : ℕ}
    (hn : 0 < n) {f : E n → ℝ}
    (hf : SmoothNear (closedUnitBall n) f)
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n,
        (dirichletOrthogonalDifference (orthogonalFlow S hS t) t
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t f) x) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨A, _, B, hB, hBounds⟩ :=
    exists_dirichlet_smooth_field_difference_bounds (fun x hx => hf.contDiffAt hx) S hS
  refine ⟨B ^ 2, sq_nonneg _, ?_⟩
  intro t ht
  let R := orthogonalFlow S hS t
  let F := dirichletOrthogonalDifference R t (dirichletOrthogonalDifference R t f)
  have hfC : ContinuousOn f (closedUnitBall n) :=
    fun x hx => (hf.contDiffAt hx).continuousAt.continuousWithinAt
  have hF : ContinuousOn F (closedUnitBall n) :=
    continuousOn_dirichletOrthogonalDifference R t
      (continuousOn_dirichletOrthogonalDifference R t hfC)
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt := (dirichlet_memLp_of_continuousOn hn (hF.pow 2) 1).integrable le_rfl
  have h := setIntegral_mono_on hInt (integrable_const (B ^ 2)) measurableSet_ball
    (fun x hx => by
      have h := (hBounds t ht x (ball_subset_closedBall hx)).2
      rw [dirichletFieldDifference_real, dirichletFieldDifference_real, Real.norm_eq_abs] at h
      change (F x) ^ 2 ≤ B ^ 2
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (F x)) h 2)
  simpa only [Pi.pow_apply, F, R, integral_const, probReal_univ, one_smul] using h

theorem exists_dirichlet_unitary_second_difference_uniform_hessian_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t
            (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u)) x
              (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤ C := by
  have hfC : ContinuousOn f (closedUnitBall n) :=
    fun x hx => (hf.contDiffAt hx).continuousAt.continuousWithinAt
  have hf1 : ContDiffOn ℝ 1 f (closedUnitBall n) := by
    intro x hx
    exact ((hf.contDiffAt hx).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).contDiffWithinAt
  obtain ⟨δ₀, hδ₀, A, hA, B, hB, hEnergy⟩ :=
    exists_dirichlet_unitary_second_difference_energy_bound hn hu huS hu0 hPos hfC hEq S hS hJ
  obtain ⟨δ₁, hδ₁, C₀, hC₀, hFirst⟩ :=
    exists_dirichlet_unitary_difference_uniform_hessian_bound_of_C1_density
      hn hu huS hu0 hPos hf1 hEq S hS hJ
  obtain ⟨F₀, hF₀, hDensity⟩ :=
    exists_integral_dirichlet_second_difference_density_bound hn hf S hS
  let d : ℝ := (2 * n : ℝ) ^ 2
  have hd : 0 ≤ d := sq_nonneg _
  let ε := (2 * B * d + 1)⁻¹
  have hDen : 0 < 2 * B * d + 1 := by positivity
  have hε : 0 < ε := inv_pos.mpr hDen
  have hMargin : B * ε * d ≤ (1 / 2 : ℝ) := by
    have he : (2 * B * d + 1) * ε = 1 := mul_inv_cancel₀ hDen.ne'
    nlinarith only [he, hε.le]
  obtain ⟨K, hK, hQuartic⟩ :=
    exists_dirichlet_discrete_hessian_quartic_small_coefficient hn hu huS hu0 S hS hε
  let D := A * F₀ + B * (K * (d * C₀) + K)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, 2 * D, by positivity, ?_⟩
  intro t ht hSmall
  let R := orthogonalFlow S hS t
  let q := dirichletOrthogonalDifference R t u
  let p := dirichletOrthogonalDifference R t q
  let N₁ := ∫ x in unitBall n, ‖dirichletWithinRealHessian q x‖ ^ 2 ∂volume0 n
  let N₂ := ∫ x in unitBall n, ‖dirichletWithinRealHessian p x‖ ^ 2 ∂volume0 n
  let E₁ := ∫ x in unitBall n, ∑ i, ∑ j,
    (dirichletWithinRealHessian q x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n
  let E₂ := ∫ x in unitBall n, ∑ i, ∑ j,
    (dirichletWithinRealHessian p x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n
  let Q := ∫ x in unitBall n, ‖dirichletWithinRealHessian q x‖ ^ 4 ∂volume0 n
  let F := ∫ x in unitBall n,
    (dirichletOrthogonalDifference R t (dirichletOrthogonalDifference R t f) x) ^ 2 ∂volume0 n
  have hE : E₂ ≤ A * F + B * Q := hEnergy t ht (lt_of_lt_of_le hSmall (min_le_left _ _))
  have hQ : Q ≤ ε * N₂ + K * N₁ + K := hQuartic t ht
  have hE₁ : E₁ ≤ C₀ := hFirst t ht (lt_of_lt_of_le hSmall (min_le_right _ _))
  have hF : F ≤ F₀ := hDensity t ht
  have hq : ContDiffOn ℝ 2 q (closedUnitBall n) := contDiffOn_dirichletOrthogonalDifference R t hu
  have hp : ContDiffOn ℝ 2 p (closedUnitBall n) := contDiffOn_dirichletOrthogonalDifference R t hq
  have hN₁ : N₁ ≤ d * C₀ := (integral_norm_withinHessian_sq_le_entries hn hq).trans
    (mul_le_mul_of_nonneg_left hE₁ hd)
  have hN₂ : N₂ ≤ d * E₂ := integral_norm_withinHessian_sq_le_entries hn hp
  have hE₂ : 0 ≤ E₂ := integral_nonneg (fun _ =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hQBound : Q ≤ ε * (d * E₂) + K * (d * C₀) + K :=
    hQ.trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hN₂ hε.le) (mul_le_mul_of_nonneg_left hN₁ hK)) le_rfl)
  have hFinal := hE.trans (add_le_add (mul_le_mul_of_nonneg_left hF hA)
    (mul_le_mul_of_nonneg_left hQBound hB))
  have hAbsorb := mul_le_mul_of_nonneg_right hMargin hE₂
  change E₂ ≤ 2 * D
  dsimp only [D]
  nlinarith only [hFinal, hAbsorb]

end KEBall
