import KEBall.DirichletBoundaryRemainderDerivative
import KEBall.DirichletBoundaryTraceContinuity

/-! Quantitative nearest-sphere estimates for the actual extended first jet. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped ContDiff

namespace KEBall

theorem norm_dirichlet_extended_jet_sub_nearest_le {n : ℕ}
    {q a : E n → ℝ} {Q : E n → E n →L[ℝ] ℝ} {B C H α β : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hq : ∀ x ∈ unitBall n, DifferentiableAt ℝ q x)
    (hQi : ∀ x ∈ unitBall n, Q x = fderiv ℝ q x)
    (hQb : ∀ p ∈ unitSphere n,
      Q p = a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p)
    (hBound : ∀ p ∈ unitSphere n, |a p| ≤ B)
    (hTrace : ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ x ∈ dirichletBoundaryCap p r,
        |q x / dirichletBoundaryDistanceProxy x - a p| ≤ C * r ^ α)
    (hHolder : ∀ x ∈ unitBall n, ∀ r : ℝ, r = 1 - ‖x‖ → r ≤ 1 / 2 →
      ∀ y ∈ ball x (r / 8), ∀ z ∈ ball x (r / 8),
        ‖fderiv ℝ q y - fderiv ℝ q z‖ ≤ (H / r ^ β) * ‖y - z‖ ^ β)
    {x p : E n} (hx : x ∈ closedUnitBall n) (hxSmall : 1 - ‖x‖ ≤ 1 / 2)
    (hp : p ∈ unitSphere n) (hNear : dist x p = 1 - ‖x‖) :
    ‖Q x - Q p‖ ≤
      (16 * (C * (2 : ℝ) ^ (1 + α)) + (H + B) / (8 : ℝ) ^ β + B) *
        (1 - ‖x‖) ^ (α * β / 2) := by
  let r : ℝ := 1 - ‖x‖
  have hr0 : 0 ≤ r := sub_nonneg.mpr (mem_closedBall_zero_iff.mp hx)
  by_cases hr : r = 0
  · have hxp : x = p := dist_eq_zero.mp (hNear.trans hr)
    rw [hxp, sub_self, norm_zero]
    simp only [mem_sphere_zero_iff_norm.mp hp, sub_self,
      Real.zero_rpow (by positivity : α * β / 2 ≠ 0), mul_zero, le_refl]
  have hr : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
  have hxOpen : x ∈ unitBall n := mem_ball_zero_iff.mpr (by dsimp [r] at hr; linarith)
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [norm_nonneg x]
  have hInside : closedBall x (r / 2) ⊆ unitBall n :=
    closedBall_subset_dirichlet_unitBall_of_margin (by dsimp [r] at *; linarith)
  have hSub : ball x (r / 8) ⊆ unitBall n :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hInside)
  have hRemainder := norm_dirichlet_boundary_remainder_fderiv_le hC hH hB
    hα hβ hβ1 (hBound p hp) hp hr hxSmall hInside hNear.le
    (fun y hy => hq y (hSub hy)) (hHolder x hxOpen r rfl hxSmall)
    (hTrace p hp (2 * r) (by positivity) (by dsimp [r]; linarith))
  have hη1 : α * β / 2 ≤ 1 := by nlinarith
  have hηα : α * β / 2 ≤ α / 2 := by nlinarith
  have hPow : r ^ (α / 2) ≤ r ^ (α * β / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 hηα
  have hSelf : r ≤ r ^ (α * β / 2) := Real.self_le_rpow_of_le_one hr.le hr1 hη1
  have hNormal : ‖a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) x -
      a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p‖ ≤ B * r := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    apply mul_le_mul (hBound p hp) _ (norm_nonneg _) hB
    calc
      _ ≤ ‖x - p‖ := norm_fderiv_dirichletBoundaryDistanceProxy_sub_le x p
      _ = r := by rw [← dist_eq_norm, hNear]
  rw [hQi x hxOpen, hQb p hp]
  calc
    _ ≤ ‖fderiv ℝ q x - a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) x‖ +
        ‖a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) x -
          a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (16 * (C * (2 : ℝ) ^ (1 + α)) * r ^ (α / 2) +
        ((H + B) / (8 : ℝ) ^ β) * r ^ (α * β / 2)) + B * r :=
      add_le_add hRemainder hNormal
    _ ≤ (16 * (C * (2 : ℝ) ^ (1 + α)) + (H + B) / (8 : ℝ) ^ β + B) *
        r ^ (α * β / 2) := by
      have h₁ := mul_le_mul_of_nonneg_left hPow
        (by positivity : 0 ≤ 16 * (C * (2 : ℝ) ^ (1 + α)))
      have h₂ := mul_le_mul_of_nonneg_left hSelf hB
      nlinarith only [h₁, h₂]

theorem norm_dirichlet_normal_jet_sub_le_of_holder_trace {n : ℕ}
    {a : E n → ℝ} {B K α : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hBound : ∀ p ∈ unitSphere n, |a p| ≤ B)
    (hTrace : ∀ p ∈ unitSphere n, ∀ q ∈ unitSphere n,
      |a p - a q| ≤ K * dist p q ^ α)
    {p q : E n} (hp : p ∈ unitSphere n) (hq : q ∈ unitSphere n) :
    ‖a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p -
      a q • fderiv ℝ (@dirichletBoundaryDistanceProxy n) q‖ ≤
      (K + 2 * B) * dist p q ^ α := by
  have hpNorm : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hqNorm : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp hq
  have hdist : dist p q ≤ 2 := by
    rw [dist_eq_norm]
    exact (norm_sub_le p q).trans (by rw [hpNorm, hqNorm]; norm_num)
  have hSelf : dist p q ≤ 2 * dist p q ^ α := by
    by_cases hnear : dist p q ≤ 1
    · have h := Real.self_le_rpow_of_le_one dist_nonneg hnear hα1
      nlinarith [Real.rpow_nonneg (dist_nonneg : 0 ≤ dist p q) α]
    · have h := Real.one_le_rpow (le_of_lt (lt_of_not_ge hnear)) hα
      linarith
  have hρ : ‖fderiv ℝ (@dirichletBoundaryDistanceProxy n) p‖ ≤ 1 := by
    rw [fderiv_dirichletBoundaryDistanceProxy, norm_neg]
    exact ((innerSL ℝ).le_opNorm p).trans (by
      rw [hpNorm, mul_one]
      exact norm_innerSL_le ℝ)
  have he : a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p -
      a q • fderiv ℝ (@dirichletBoundaryDistanceProxy n) q =
      (a p - a q) • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p +
        a q • (fderiv ℝ (@dirichletBoundaryDistanceProxy n) p -
          fderiv ℝ (@dirichletBoundaryDistanceProxy n) q) := by
    rw [sub_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ |a p - a q| * ‖fderiv ℝ (@dirichletBoundaryDistanceProxy n) p‖ +
        |a q| * ‖fderiv ℝ (@dirichletBoundaryDistanceProxy n) p -
          fderiv ℝ (@dirichletBoundaryDistanceProxy n) q‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        ((a p - a q) • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p)
        (a q • (fderiv ℝ (@dirichletBoundaryDistanceProxy n) p -
          fderiv ℝ (@dirichletBoundaryDistanceProxy n) q))
    _ ≤ (K * dist p q ^ α) * 1 + B * (2 * dist p q ^ α) := by
      apply add_le_add
      · exact mul_le_mul (hTrace p hp q hq) hρ (norm_nonneg _) (by positivity)
      · exact mul_le_mul (hBound q hq)
          ((norm_fderiv_dirichletBoundaryDistanceProxy_sub_le p q).trans
            (by simpa only [dist_eq_norm] using hSelf)) (norm_nonneg _) hB
    _ = _ := by ring

end KEBall
