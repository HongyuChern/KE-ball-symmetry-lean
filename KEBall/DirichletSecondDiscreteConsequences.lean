import KEBall.DirichletSecondDiscreteHessianEstimate

/-!
# Uniform quartic and spatial second-difference consequences

All differences are formed from the same actual closed-ball C2 potential.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_dirichlet_unitary_difference_uniform_hessian_quartic_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n,
        ‖dirichletWithinRealHessian
          (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) x‖ ^ 4 ∂volume0 n) ≤ C := by
  have hf1 : ContDiffOn ℝ 1 f (closedUnitBall n) := by
    intro x hx
    exact ((hf.contDiffAt hx).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).contDiffWithinAt
  obtain ⟨δ₁, hδ₁, C₁, hC₁, hFirst⟩ :=
    exists_dirichlet_unitary_difference_uniform_hessian_bound_of_C1_density
      hn hu huS hu0 hPos hf1 hEq S hS hJ
  obtain ⟨δ₂, hδ₂, C₂, hC₂, hSecond⟩ :=
    exists_dirichlet_unitary_second_difference_uniform_hessian_bound
      hn hu huS hu0 hPos hf hEq S hS hJ
  obtain ⟨K, hK, hQuartic⟩ :=
    exists_dirichlet_discrete_hessian_quartic_small_coefficient hn hu huS hu0 S hS
      (by norm_num : (0 : ℝ) < 1)
  let d : ℝ := (2 * n : ℝ) ^ 2
  have hd : 0 ≤ d := sq_nonneg _
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, d * C₂ + K * (d * C₁) + K, by positivity, ?_⟩
  intro t ht hSmall
  let R := orthogonalFlow S hS t
  let q := dirichletOrthogonalDifference R t u
  let p := dirichletOrthogonalDifference R t q
  have hq := contDiffOn_dirichletOrthogonalDifference R t hu
  have hp := contDiffOn_dirichletOrthogonalDifference R t hq
  have hN₁ : (∫ x in unitBall n, ‖dirichletWithinRealHessian q x‖ ^ 2 ∂volume0 n) ≤ d * C₁ :=
    (integral_norm_withinHessian_sq_le_entries hn hq).trans
      (mul_le_mul_of_nonneg_left (hFirst t ht (lt_of_lt_of_le hSmall (min_le_left _ _))) hd)
  have hN₂ : (∫ x in unitBall n, ‖dirichletWithinRealHessian p x‖ ^ 2 ∂volume0 n) ≤ d * C₂ :=
    (integral_norm_withinHessian_sq_le_entries hn hp).trans
      (mul_le_mul_of_nonneg_left (hSecond t ht (lt_of_lt_of_le hSmall (min_le_right _ _))) hd)
  have hQ := hQuartic t ht
  rw [one_mul] at hQ
  exact hQ.trans (add_le_add (add_le_add hN₂ (mul_le_mul_of_nonneg_left hN₁ hK)) le_rfl)

theorem exists_dirichlet_unitary_second_cofactor_error_uniform_L2_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n,
        (dirichletSecondDiscreteCofactorError (orthogonalFlow S hS t) t u x) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨δ, hδ, C, hC, hQuartic⟩ :=
    exists_dirichlet_unitary_difference_uniform_hessian_quartic_bound
      hn hu huS hu0 hPos hf hEq S hS hJ
  obtain ⟨K, hK, hError⟩ := exists_integral_dirichlet_second_error_sq_bound hn hu
  refine ⟨δ, hδ, K * C, mul_nonneg hK hC, ?_⟩
  intro t ht hSmall
  exact (hError (orthogonalFlow S hS t) t ht).trans
    (mul_le_mul_of_nonneg_left (hQuartic t ht hSmall) hK)

theorem exists_dirichlet_unitary_spatial_second_hessian_uniform_L2_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (∫ x in unitBall n,
        ‖dirichletFieldDifference (orthogonalFlow S hS t) t
          (dirichletFieldDifference (orthogonalFlow S hS t) t
            (dirichletWithinRealHessian u)) x‖ ^ 2 ∂volume0 n) ≤ C := by
  have hf1 : ContDiffOn ℝ 1 f (closedUnitBall n) := by
    intro x hx
    exact ((hf.contDiffAt hx).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).contDiffWithinAt
  obtain ⟨δ₁, hδ₁, C₁, hC₁, hFirst⟩ :=
    exists_dirichlet_unitary_difference_uniform_hessian_bound_of_C1_density
      hn hu huS hu0 hPos hf1 hEq S hS hJ
  obtain ⟨δ₂, hδ₂, C₂, hC₂, hSecond⟩ :=
    exists_dirichlet_unitary_second_difference_uniform_hessian_bound
      hn hu huS hu0 hPos hf hEq S hS hJ
  let d : ℝ := (2 * n : ℝ) ^ 2
  have hd : 0 ≤ d := sq_nonneg _
  let N₀ := ∫ x in unitBall n, ‖dirichletWithinRealHessian u x‖ ^ 2 ∂volume0 n
  have hN₀ : 0 ≤ N₀ := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂,
    3 * (d * C₂) + 48 * ‖S‖ ^ 2 * (d * C₁) + 48 * ‖S‖ ^ 4 * N₀, by positivity, ?_⟩
  intro t ht hSmall
  let R := orthogonalFlow S hS t
  let q := dirichletOrthogonalDifference R t u
  let p := dirichletOrthogonalDifference R t q
  let H₀ := dirichletWithinRealHessian u
  let H₁ := dirichletWithinRealHessian q
  let H₂ := dirichletWithinRealHessian p
  let DDH := dirichletFieldDifference R t (dirichletFieldDifference R t H₀)
  have hq := contDiffOn_dirichletOrthogonalDifference R t hu
  have hp := contDiffOn_dirichletOrthogonalDifference R t hq
  have hH₀ := continuousOn_dirichletWithinRealHessian hu
  have hH₁ := continuousOn_dirichletWithinRealHessian hq
  have hH₂ := continuousOn_dirichletWithinRealHessian hp
  have hDDH := continuousOn_dirichletFieldDifference R t
    (continuousOn_dirichletFieldDifference R t hH₀)
  have hN₁ : (∫ x in unitBall n, ‖H₁ x‖ ^ 2 ∂volume0 n) ≤ d * C₁ :=
    (integral_norm_withinHessian_sq_le_entries hn hq).trans
      (mul_le_mul_of_nonneg_left (hFirst t ht (lt_of_lt_of_le hSmall (min_le_left _ _))) hd)
  have hN₂ : (∫ x in unitBall n, ‖H₂ x‖ ^ 2 ∂volume0 n) ≤ d * C₂ :=
    (integral_norm_withinHessian_sq_le_entries hn hp).trans
      (mul_le_mul_of_nonneg_left (hSecond t ht (lt_of_lt_of_le hSmall (min_le_right _ _))) hd)
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hC : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hC 1).integrable le_rfl
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      ‖DDH x‖ ^ 2 ≤ 3 * ‖H₂ x‖ ^ 2 + 48 * ‖S‖ ^ 2 * ‖H₁ x‖ ^ 2 +
        48 * ‖S‖ ^ 4 * ‖H₀ x‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (DDH x))
      (norm_dirichletFieldSecondDifference_withinHessian_le hu S hS ht (ball_subset_closedBall hx)) 2
    have h₁ := sq_nonneg (‖H₂ x‖ - 4 * ‖S‖ * ‖H₁ x‖)
    have h₂ := sq_nonneg (‖H₂ x‖ - 4 * ‖S‖ ^ 2 * ‖H₀ x‖)
    have h₃ := sq_nonneg (4 * ‖S‖ * ‖H₁ x‖ - 4 * ‖S‖ ^ 2 * ‖H₀ x‖)
    nlinarith only [h, h₁, h₂, h₃]
  have h := setIntegral_mono_on (hInt (hDDH.norm.pow 2))
    (hInt ((((hH₂.norm.pow 2).const_mul 3).add
      ((hH₁.norm.pow 2).const_mul (48 * ‖S‖ ^ 2))).add
        ((hH₀.norm.pow 2).const_mul (48 * ‖S‖ ^ 4)))) measurableSet_ball hPoint
  have hAdd₀ := integral_add (((hInt (hH₂.norm.pow 2)).const_mul 3).add
    ((hInt (hH₁.norm.pow 2)).const_mul (48 * ‖S‖ ^ 2)))
    ((hInt (hH₀.norm.pow 2)).const_mul (48 * ‖S‖ ^ 4))
  have hAdd₁ := integral_add ((hInt (hH₂.norm.pow 2)).const_mul 3)
    ((hInt (hH₁.norm.pow 2)).const_mul (48 * ‖S‖ ^ 2))
  simp only [Pi.add_apply, Pi.pow_apply] at h hAdd₀ hAdd₁
  rw [hAdd₀, hAdd₁, integral_const_mul, integral_const_mul, integral_const_mul] at h
  exact h.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hN₂ (by norm_num))
    (mul_le_mul_of_nonneg_left hN₁ (by positivity))) le_rfl)

end KEBall
