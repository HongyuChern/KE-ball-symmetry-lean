import KEBall.DirichletUniformDiscreteCofactor

/-!
# Spatial differences of the actual closed-ball Hessian

The Hessian of a potential difference includes pullback in both tensor
arguments. These identities separate that pullback from spatial scalar
differences, with bounds independent of the nonzero flow step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped ContDiff

namespace KEBall

noncomputable def dirichletFieldDifference {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F : E n → V) : E n → V :=
  fun x => τ⁻¹ • (F (R x) - F x)

theorem dirichletFieldDifference_add {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F G : E n → V) :
    dirichletFieldDifference R τ (fun x => F x + G x) =
      fun x => dirichletFieldDifference R τ F x + dirichletFieldDifference R τ G x := by
  funext x
  simp only [dirichletFieldDifference, smul_sub, smul_add]
  abel

theorem dirichletFieldDifference_clm {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (L : V →L[ℝ] W) (F : E n → V) :
    dirichletFieldDifference R τ (fun x => L (F x)) =
      fun x => L (dirichletFieldDifference R τ F x) := by
  funext x
  simp only [dirichletFieldDifference, map_smul, map_sub]

theorem dirichletFieldDifference_congr_closed {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {F G : E n → V}
    (h : EqOn F G (closedUnitBall n)) :
    EqOn (dirichletFieldDifference R τ F) (dirichletFieldDifference R τ G)
      (closedUnitBall n) := by
  intro x hx
  have hRx : R x ∈ closedUnitBall n := by
    simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hx
  simp only [dirichletFieldDifference, h hx, h hRx]

theorem continuousOn_dirichletFieldDifference {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {F : E n → V}
    (hF : ContinuousOn F (closedUnitBall n)) :
    ContinuousOn (dirichletFieldDifference R τ F) (closedUnitBall n) := by
  have hMaps : MapsTo R (closedUnitBall n) (closedUnitBall n) := by
    intro x hx
    simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hx
  exact ((hF.comp R.continuous.continuousOn hMaps).sub hF).const_smul τ⁻¹

theorem dirichletFieldDifference_bilinear_apply {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ)
    (H : E n → E n →L[ℝ] E n →L[ℝ] ℝ) (x a b : E n) :
    dirichletFieldDifference R τ H x a b =
      dirichletOrthogonalDifference R τ (fun y => H y a b) x := by
  simp only [dirichletFieldDifference, dirichletOrthogonalDifference,
    _root_.smul_apply, _root_.sub_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem dirichletWithinRealHessian_orthogonal_difference {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u) x =
      τ⁻¹ • (dirichletBilinearPullback R (dirichletWithinRealHessian u (R x)) -
        dirichletWithinRealHessian u x) := by
  have hMaps : MapsTo R (closedUnitBall n) (closedUnitBall n) := by
    intro y hy
    simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hy
  have hMapsB : MapsTo R (unitBall n) (unitBall n) := by
    intro y hy
    simpa only [unitBall, mem_ball_zero_iff, R.norm_map] using hy
  have hH := continuousOn_dirichletWithinRealHessian hu
  have hLeft := continuousOn_dirichletWithinRealHessian
    (contDiffOn_dirichletOrthogonalDifference R τ hu)
  have hRight := (((dirichletBilinearPullbackCLM R).continuous.comp_continuousOn
    (hH.comp R.continuous.continuousOn hMaps)).sub hH).const_smul τ⁻¹
  have hEq : EqOn
      (dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u))
      (fun y => τ⁻¹ • (dirichletBilinearPullback R (dirichletWithinRealHessian u (R y)) -
        dirichletWithinRealHessian u y)) (unitBall n) := by
    intro y hy
    change dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u) y =
      τ⁻¹ • (dirichletBilinearPullback R (dirichletWithinRealHessian u (R y)) -
        dirichletWithinRealHessian u y)
    rw [dirichletWithinRealHessian_eq_on_ball _ hy,
      dirichletWithinRealHessian_eq_on_ball u (hMapsB hy),
      dirichletWithinRealHessian_eq_on_ball u hy,
      realHessian_dirichletOrthogonalDifference R τ
        ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hy))
        ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds (hMapsB hy))),
      realHessian_comp_eq_dirichletBilinearPullback]
  exact hEq.of_subset_closure hLeft hRight ball_subset_closedBall
    (by rw [unitBall, closedUnitBall, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]) hx

noncomputable def dirichletBilinearPullbackIncrement {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] (E n →L[ℝ] E n →L[ℝ] ℝ) :=
  τ⁻¹ • (dirichletBilinearPullbackCLM R - ContinuousLinearMap.id ℝ _)

theorem dirichletFieldDifference_withinHessian {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    dirichletFieldDifference R τ (dirichletWithinRealHessian u) x =
      dirichletBilinearPullbackCLM R.symm
        (dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u) x) +
      dirichletBilinearPullbackIncrement R.symm τ (dirichletWithinRealHessian u x) := by
  rw [dirichletWithinRealHessian_orthogonal_difference R τ hu hx]
  simp only [map_smul, map_sub, dirichletBilinearPullbackCLM_apply,
    dirichletBilinearPullback_symm, dirichletBilinearPullbackIncrement,
    _root_.smul_apply, _root_.sub_apply,
    ContinuousLinearMap.id_apply, dirichletFieldDifference, smul_sub]
  abel

theorem dirichletFieldSecondDifference_withinHessian {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    let L := dirichletBilinearPullbackCLM R.symm
    let C := dirichletBilinearPullbackIncrement R.symm τ
    let q := dirichletOrthogonalDifference R τ u
    let p := dirichletOrthogonalDifference R τ q
    dirichletFieldDifference R τ (dirichletFieldDifference R τ (dirichletWithinRealHessian u)) x =
      L (L (dirichletWithinRealHessian p x) + C (dirichletWithinRealHessian q x)) +
      C (L (dirichletWithinRealHessian q x) + C (dirichletWithinRealHessian u x)) := by
  dsimp only
  have hEq : EqOn (dirichletFieldDifference R τ (dirichletWithinRealHessian u))
      (fun y => dirichletBilinearPullbackCLM R.symm
        (dirichletWithinRealHessian (dirichletOrthogonalDifference R τ u) y) +
        dirichletBilinearPullbackIncrement R.symm τ (dirichletWithinRealHessian u y))
      (closedUnitBall n) := fun y hy => dirichletFieldDifference_withinHessian R τ hu hy
  rw [dirichletFieldDifference_congr_closed R τ hEq hx,
    dirichletFieldDifference_add, dirichletFieldDifference_clm,
    dirichletFieldDifference_clm]
  dsimp only
  rw [dirichletFieldDifference_withinHessian R τ
      (contDiffOn_dirichletOrthogonalDifference R τ hu) hx,
    dirichletFieldDifference_withinHessian R τ hu hx]

theorem norm_dirichletBilinearPullbackIncrement_flow_symm_le {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0) :
    ‖dirichletBilinearPullbackIncrement (orthogonalFlow S hS t).symm t‖ ≤ 2 * ‖S‖ := by
  rw [dirichletBilinearPullbackIncrement, orthogonalFlow_symm_eq_neg, norm_smul,
    norm_inv, Real.norm_eq_abs]
  have h := norm_dirichletBilinearPullbackCLM_flow_sub_id_le S hS (-t)
  rw [abs_neg] at h
  calc
    _ ≤ |t|⁻¹ * (2 * ‖S‖ * |t|) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (abs_nonneg t))
    _ = 2 * ‖S‖ := by field_simp

theorem norm_dirichletFieldSecondDifference_withinHessian_le {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    let R := orthogonalFlow S hS t
    let q := dirichletOrthogonalDifference R t u
    let p := dirichletOrthogonalDifference R t q
    ‖dirichletFieldDifference R t (dirichletFieldDifference R t (dirichletWithinRealHessian u)) x‖ ≤
      ‖dirichletWithinRealHessian p x‖ + 4 * ‖S‖ * ‖dirichletWithinRealHessian q x‖ +
        4 * ‖S‖ ^ 2 * ‖dirichletWithinRealHessian u x‖ := by
  dsimp only
  rw [dirichletFieldSecondDifference_withinHessian _ _ hu hx]
  let R := orthogonalFlow S hS t
  let L := dirichletBilinearPullbackCLM R.symm
  let C := dirichletBilinearPullbackIncrement R.symm t
  have hL (H : E n →L[ℝ] E n →L[ℝ] ℝ) : ‖L H‖ ≤ ‖H‖ :=
    norm_dirichletBilinearPullback_le R.symm H
  have hC (H : E n →L[ℝ] E n →L[ℝ] ℝ) : ‖C H‖ ≤ 2 * ‖S‖ * ‖H‖ :=
    (C.le_opNorm H).trans (mul_le_mul_of_nonneg_right
      (norm_dirichletBilinearPullbackIncrement_flow_symm_le S hS ht) (norm_nonneg H))
  let H₀ := dirichletWithinRealHessian u x
  let H₁ := dirichletWithinRealHessian (dirichletOrthogonalDifference R t u) x
  let H₂ := dirichletWithinRealHessian
    (dirichletOrthogonalDifference R t (dirichletOrthogonalDifference R t u)) x
  change ‖L (L H₂ + C H₁) + C (L H₁ + C H₀)‖ ≤
    ‖H₂‖ + 4 * ‖S‖ * ‖H₁‖ + 4 * ‖S‖ ^ 2 * ‖H₀‖
  calc
    _ ≤ ‖L (L H₂ + C H₁)‖ + ‖C (L H₁ + C H₀)‖ := norm_add_le _ _
    _ ≤ ‖L H₂ + C H₁‖ + 2 * ‖S‖ * ‖L H₁ + C H₀‖ := add_le_add (hL _) (hC _)
    _ ≤ (‖H₂‖ + 2 * ‖S‖ * ‖H₁‖) + 2 * ‖S‖ * (‖H₁‖ + 2 * ‖S‖ * ‖H₀‖) := by
      apply add_le_add
      · exact (norm_add_le _ _).trans (add_le_add (hL _) (hC _))
      · exact mul_le_mul_of_nonneg_left
          ((norm_add_le _ _).trans (add_le_add (hL _) (hC _))) (by positivity)
    _ = _ := by ring

end KEBall
