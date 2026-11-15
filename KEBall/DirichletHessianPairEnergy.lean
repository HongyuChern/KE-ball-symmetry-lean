import KEBall.DirichletHessianProperProductAbsorption

/-! Lower-order energy for the actual Hessian paired with its smooth-reference residual. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

theorem dirichletIteratedFieldDifference_prod {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F : E n → V) (G : E n → W) (k : ℕ) :
    dirichletIteratedFieldDifference R τ (fun x => (F x, G x)) k =
      fun x => (dirichletIteratedFieldDifference R τ F k x, dirichletIteratedFieldDifference R τ G k x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dirichletIteratedFieldDifference, ih]
    rfl

theorem integral_dirichlet_pair_norm_sq_le {n : ℕ} (hn : 0 < n) {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : E n → V} {G : E n → W}
    (hF : ContinuousOn F (closedUnitBall n)) (hG : ContinuousOn G (closedUnitBall n)) :
    (∫ x in unitBall n, ‖(F x, G x)‖ ^ 2 ∂volume0 n) ≤
      (∫ x in unitBall n, ‖F x‖ ^ 2 ∂volume0 n) +
      (∫ x in unitBall n, ‖G x‖ ^ 2 ∂volume0 n) := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) := volume0_restrict_isProbability n
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hf 1).integrable le_rfl
  have h := setIntegral_mono_on (hInt ((hF.prodMk hG).norm.pow 2))
    (hInt ((hF.norm.pow 2).add (hG.norm.pow 2))) measurableSet_ball (fun x _ => by
      simp only [Pi.add_apply, Pi.pow_apply]
      rw [Prod.norm_def]
      rcases le_total ‖F x‖ ‖G x‖ with hle | hle
      · rw [max_eq_right hle]
        nlinarith only [sq_nonneg ‖F x‖]
      · rw [max_eq_left hle]
        nlinarith only [sq_nonneg ‖G x‖])
  have hAdd := integral_add (hInt (hF.norm.pow 2)) (hInt (hG.norm.pow 2))
  simp only [Pi.add_apply, Pi.pow_apply] at h hAdd
  rw [hAdd] at h
  exact h

theorem exists_dirichlet_hessian_pair_difference_energy_bound {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {V : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hV : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ V x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (m : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n,
        ‖dirichletIteratedFieldDifference R t
          (fun y => (dirichletWithinRealHessian u y, dirichletWithinRealHessian u y - V y)) m x‖ ^ 2
            ∂volume0 n) ≤
        C * (∑ j ∈ Finset.range (m + 1), ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n) + C := by
  obtain ⟨C₀, hC₀, hE₀⟩ := exists_integral_dirichlet_hessian_reference_difference_bound hn hu
    (V := fun _ => 0) (fun _ _ => contDiffAt_const) S hS m
  simp only [sub_zero] at hE₀
  obtain ⟨C₁, hC₁, hE₁⟩ := exists_integral_dirichlet_hessian_reference_difference_bound hn hu hV S hS m
  let K : ℝ := 2 * (m + 1 : ℝ) * ((1 + 2 * ‖S‖) ^ m) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C : ℝ := 2 * K + C₀ + C₁
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  dsimp only
  let R := orthogonalFlow S hS t
  have hH := continuousOn_dirichletWithinRealHessian hu
  have hZ := hH.sub (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
  have hPair := integral_dirichlet_pair_norm_sq_le hn
    (continuousOn_dirichletIteratedFieldDifference R t hH m)
    (continuousOn_dirichletIteratedFieldDifference R t hZ m)
  rw [dirichletIteratedFieldDifference_prod]
  have hSum0 : 0 ≤ ∑ j ∈ Finset.range (m + 1), ∫ x in unitBall n,
      ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hCap : 2 * K ≤ C := by dsimp [C]; linarith
  have hCapSum := mul_le_mul_of_nonneg_right hCap hSum0
  have hBase : C₀ + C₁ ≤ C := by dsimp [C]; linarith
  have hBound := hPair.trans (add_le_add (hE₀ t ht) (hE₁ t ht))
  change _ ≤ K * _ + C₀ + (K * _ + C₁) at hBound
  refine hBound.trans ?_
  calc
    _ = 2 * K * (∑ j ∈ Finset.range (m + 1), ∫ x in unitBall n,
      ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n) +
      (C₀ + C₁) := by ring
    _ ≤ _ := add_le_add hCapSum hBase

theorem exists_dirichlet_hessian_pair_lower_energy_bound {n k m : ℕ}
    (hn : 0 < n) (hm : m < k) {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {V : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hV : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ V x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      let R := orthogonalFlow S hS t
      (∫ x in unitBall n,
        ‖dirichletIteratedFieldDifference R t
          (fun y => (dirichletWithinRealHessian u y, dirichletWithinRealHessian u y - V y)) m x‖ ^ 2
            ∂volume0 n) ≤
        C * (∑ j ∈ Finset.range k, ∫ x in unitBall n,
          ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference R t u j) x‖ ^ 2 ∂volume0 n) + C := by
  obtain ⟨C, hC, hBound⟩ := exists_dirichlet_hessian_pair_difference_energy_bound hn hu hV S hS m
  refine ⟨C, hC, ?_⟩
  intro t ht
  dsimp only
  refine (hBound t ht).trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ hC
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun j _ _ => integral_nonneg (fun _ => sq_nonneg _))

end KEBall
