import KEBall.DirichletBoundaryTraceExtension
import KEBall.DirichletBoundaryDistanceDifferential

/-!
# Value estimates for the true boundary remainder q-a rho

The interior ball has radius one eighth of the boundary-distance scale.
Every point of it lies in the cap where the quotient trace is controlled.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set

namespace KEBall

theorem dirichletBoundaryDistanceProxy_le_dist_sphere {n : ℕ}
    {p x : E n} (hp : p ∈ unitSphere n) (hx : x ∈ closedUnitBall n) :
    dirichletBoundaryDistanceProxy x ≤ dist x p := by
  apply (dirichletBoundaryDistanceProxy_bounds hx).2.trans
  have h := norm_sub_norm_le p x
  rw [mem_sphere_zero_iff_norm.mp hp, ← dist_eq_norm, dist_comm p x] at h
  exact h

theorem closedBall_subset_dirichlet_unitBall_of_margin {n : ℕ} {x : E n} {r : ℝ}
    (hr : r < 1 - ‖x‖) : closedBall x r ⊆ unitBall n := by
  intro y hy
  apply mem_ball_zero_iff.mpr
  have h := norm_add_le (y - x) x
  rw [sub_add_cancel] at h
  have hy' : ‖y - x‖ ≤ r := by simpa only [dist_eq_norm] using mem_closedBall.mp hy
  linarith

theorem dirichlet_small_ball_subset_boundary_cap {n : ℕ} {x p : E n} {r : ℝ}
    (hr : 0 < r) (hInside : closedBall x (r / 2) ⊆ unitBall n)
    (hNear : dist x p ≤ r) : ball x (r / 8) ⊆ dirichletBoundaryCap p (2 * r) := by
  intro y hy
  refine ⟨hInside ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hy),
    mem_ball.mpr ?_⟩
  have h := dist_triangle y x p
  have hsmall := mem_ball.mp hy
  linarith

theorem abs_dirichlet_boundary_remainder_le {n : ℕ} {q : E n → ℝ}
    {a C α : ℝ} (hC : 0 ≤ C) {x p : E n} (hp : p ∈ unitSphere n)
    {r : ℝ} (hr : 0 < r) (hInside : closedBall x (r / 2) ⊆ unitBall n)
    (hNear : dist x p ≤ r)
    (hTrace : ∀ y ∈ dirichletBoundaryCap p (2 * r),
      |q y / dirichletBoundaryDistanceProxy y - a| ≤ C * (2 * r) ^ α) :
    ∀ y ∈ ball x (r / 8),
      |q y - a * dirichletBoundaryDistanceProxy y| ≤
        (C * (2 : ℝ) ^ (1 + α)) * r ^ (1 + α) := by
  intro y hy
  have hcap := dirichlet_small_ball_subset_boundary_cap hr hInside hNear hy
  have hρ := dirichletBoundaryDistanceProxy_pos hcap.1
  have hρR : dirichletBoundaryDistanceProxy y ≤ 2 * r :=
    (dirichletBoundaryDistanceProxy_le_dist_sphere hp (ball_subset_closedBall hcap.1)).trans
      (mem_ball.mp hcap.2).le
  have he : q y - a * dirichletBoundaryDistanceProxy y =
      (q y / dirichletBoundaryDistanceProxy y - a) * dirichletBoundaryDistanceProxy y := by
    field_simp [hρ.ne']
  rw [he, abs_mul, abs_of_pos hρ]
  calc
    _ ≤ (C * (2 * r) ^ α) * (2 * r) :=
      mul_le_mul (hTrace y hcap) hρR hρ.le (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    _ = C * (2 * r) ^ (1 + α) := by
      rw [Real.rpow_add (by positivity : 0 < 2 * r), Real.rpow_one]
      ring
    _ = (C * (2 : ℝ) ^ (1 + α)) * r ^ (1 + α) := by
      rw [Real.mul_rpow (by norm_num) hr.le]
      ring

end KEBall
