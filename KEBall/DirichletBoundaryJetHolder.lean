import KEBall.DirichletBoundaryJetPower
import KEBall.DirichletBoundaryHolderGluing

/-! A closed-ball Holder bound for the full jet obtained from quotient decay. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped ContDiff NNReal

namespace KEBall

theorem exists_dirichlet_closedBall_holder_extended_jet {n : ℕ} (hn : 0 < n)
    {q a : E n → ℝ} {Q : E n → E n →L[ℝ] ℝ} {B C H K α β : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hQC : ContinuousOn Q (closedUnitBall n))
    (hq : ∀ x ∈ unitBall n, DifferentiableAt ℝ q x)
    (hQi : ∀ x ∈ unitBall n, Q x = fderiv ℝ q x)
    (hQb : ∀ p ∈ unitSphere n,
      Q p = a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p)
    (hBound : ∀ p ∈ unitSphere n, |a p| ≤ B)
    (hTrace : ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ x ∈ dirichletBoundaryCap p r,
        |q x / dirichletBoundaryDistanceProxy x - a p| ≤ C * r ^ α)
    (hBoundary : ∀ p ∈ unitSphere n, ∀ q ∈ unitSphere n,
      |a p - a q| ≤ K * dist p q ^ α)
    (hHolder : ∀ x ∈ unitBall n, ∀ r : ℝ, r = 1 - ‖x‖ →
      ∀ y ∈ ball x (r / 8), ∀ z ∈ ball x (r / 8),
        ‖fderiv ℝ q y - fderiv ℝ q z‖ ≤ (H / r ^ β) * ‖y - z‖ ^ β) :
    ∃ θ : ℝ≥0, (θ : ℝ) = min (α * β / 2) (min α β) / 2 ∧
      0 < θ ∧ θ < 1 ∧ ∃ M : ℝ≥0, HolderOnWith M θ Q (closedUnitBall n) := by
  obtain ⟨BQ, hBQ⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hQC
  let C₁ : ℝ := 16 * (C * (2 : ℝ) ^ (1 + α)) + (H + B) / (8 : ℝ) ^ β + B
  refine exists_dirichlet_closedBall_holder_of_boundary_power hn
    (B := max BQ 0) (C := C₁) (H := H) (K := K + 2 * B)
    (le_max_right _ _) (by dsimp [C₁]; positivity) hH (by positivity)
    hα hα1 hβ (by positivity : 0 < α * β / 2) ?_ ?_ ?_ ?_
  · intro x hx
    exact (hBQ x hx).trans (le_max_left _ _)
  · intro p hp q hq
    rw [hQb p hp, hQb q hq]
    exact norm_dirichlet_normal_jet_sub_le_of_holder_trace hB hK hα.le hα1
      hBound hBoundary hp hq
  · intro x hx hSmall p hp hNear
    exact norm_dirichlet_extended_jet_sub_nearest_le hB hC hH hα hα1 hβ hβ1
      hq hQi hQb hBound hTrace (fun x hx r hr _ => hHolder x hx r hr)
      hx hSmall hp hNear
  · intro x hx y hy
    let r : ℝ := 1 - ‖x‖
    have hr : 0 < r := sub_pos.mpr (mem_ball_zero_iff.mp hx)
    have hInside : closedBall x (r / 2) ⊆ unitBall n :=
      closedBall_subset_dirichlet_unitBall_of_margin (by dsimp [r] at *; linarith)
    have hyOpen : y ∈ unitBall n := hInside
      (ball_subset_closedBall ((ball_subset_ball (by linarith : r / 8 ≤ r / 2)) hy))
    rw [hQi x hx, hQi y hyOpen]
    simpa only [dist_eq_norm] using hHolder x hx r rfl x
      (mem_ball_self (by positivity)) y hy

end KEBall
