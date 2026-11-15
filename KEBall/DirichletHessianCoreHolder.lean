import KEBall.DirichletHessianScaledHolder
import KEBall.DirichletCoreAnnulusHolder

/-!
# A quantitative Holder bound on a fixed interior core

The constant below uses only the supplied bound and scaled modulus.  No
bound for third derivatives is selected by compactness.  This keeps the
interior part of a boundary estimate suitable for a family of potentials.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

theorem dirichlet_core_holder_bound_of_scaled {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {f : E n → F} {α H B : ℝ}
    (hα : 0 ≤ α) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hBound : ∀ x ∈ unitBall n, ‖f x‖ ≤ B)
    (hScaled : ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 →
      closedBall x₀ (2 * R) ⊆ unitBall n →
      ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
        ‖f x - f y‖ ≤ (H * (4 / R : ℝ) ^ α) * ‖x - y‖ ^ α) :
    ∀ x ∈ closedBall (0 : E n) (3 / 4 : ℝ),
      ∀ y ∈ closedBall (0 : E n) (3 / 4 : ℝ),
        ‖f x - f y‖ ≤
          (H * (64 : ℝ) ^ α + 2 * B / (1 / 32 : ℝ) ^ α) * ‖x - y‖ ^ α := by
  let C : ℝ := H * (64 : ℝ) ^ α + 2 * B / (1 / 32 : ℝ) ^ α
  have hNearC : H * (64 : ℝ) ^ α ≤ C := le_add_of_nonneg_right (by positivity)
  have hFarC : 2 * B / (1 / 32 : ℝ) ^ α ≤ C := le_add_of_nonneg_left (by positivity)
  have hCore : closedBall (0 : E n) (3 / 4 : ℝ) ⊆ unitBall n :=
    closedBall_subset_ball (by norm_num)
  intro x hx y hy
  by_cases hd : dist x y < 1 / 32
  · have hMargin : closedBall x (2 * (1 / 16 : ℝ)) ⊆ unitBall n := by
      intro z hz
      apply mem_ball_zero_iff.mpr
      have hxN := mem_closedBall_zero_iff.mp hx
      have hzN := mem_closedBall.mp hz
      have ht := norm_sub_norm_le z x
      rw [← dist_eq_norm] at ht
      linarith
    have he := hScaled x (1 / 16) (by norm_num) (by norm_num) hMargin
      x (mem_ball_self (by norm_num)) y (by
        rw [mem_ball, dist_comm]
        norm_num
        exact hd)
    norm_num only [show (4 / (1 / 16 : ℝ)) = 64 by norm_num] at he
    exact he.trans (mul_le_mul_of_nonneg_right hNearC
      (Real.rpow_nonneg (norm_nonneg _) _))
  · have hp : (1 / 32 : ℝ) ^ α ≤ ‖x - y‖ ^ α := by
      apply Real.rpow_le_rpow (by norm_num) _ hα
      simpa only [dist_eq_norm] using le_of_not_gt hd
    have hP : 0 < (1 / 32 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
    calc
      ‖f x - f y‖ ≤ 2 * B :=
        (norm_sub_le _ _).trans (by linarith [hBound x (hCore hx), hBound y (hCore hy)])
      _ = (2 * B / (1 / 32 : ℝ) ^ α) * (1 / 32 : ℝ) ^ α := by
        field_simp [hP.ne']
      _ ≤ (2 * B / (1 / 32 : ℝ) ^ α) * ‖x - y‖ ^ α :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ C * ‖x - y‖ ^ α :=
        mul_le_mul_of_nonneg_right hFarC (Real.rpow_nonneg (norm_nonneg _) _)

theorem exists_dirichlet_realHessian_core_holder_of_oscillation {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G) :
    ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧
      HasDirichletHolderOn α (realHessian w)
        (closedBall (0 : E n) (3 / 4 : ℝ)) := by
  obtain ⟨α, H, hα, hα1, hH, hScaled⟩ :=
    exists_dirichlet_realHessian_scaled_holder_of_oscillation hD hG hDecay
  have hBound (x : E n) (hx : x ∈ unitBall n) : ‖realHessian w x‖ ≤ L := by
    rw [← fderiv_dirichlet_firstJet_eq_realHessian hD hx]
    exact norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hG
  let C : ℝ := H * (64 : ℝ) ^ α + 2 * (L : ℝ) / (1 / 32 : ℝ) ^ α
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨⟨α, hα.le⟩, hα, hα1, ⟨⟨C, hC⟩, ?_⟩⟩
  exact dirichlet_holderOnWith_of_norm_bound hC hα.le
    (dirichlet_core_holder_bound_of_scaled hα.le hH L.coe_nonneg hBound hScaled)

end KEBall
