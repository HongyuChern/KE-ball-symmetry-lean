import KEBall.DirichletBoundaryRemainder
import KEBall.DirichletBoundaryInterpolation

/-!
# A vanishing derivative bound for q-a rho

The interpolation scale is r*r^(alpha/2)/8, strictly inside the ball of
radius r/8.  The two resulting exponents are alpha/2 and alpha*beta/2,
both positive.  No boundary second derivative is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped ContDiff

namespace KEBall

theorem norm_dirichlet_boundary_remainder_fderiv_le {n : ℕ} {q : E n → ℝ}
    {a C H B α β : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hα : 0 < α) (hβ : 0 < β) (hβ1 : β ≤ 1) (ha : |a| ≤ B)
    {x p : E n} (hp : p ∈ unitSphere n) {r : ℝ} (hr : 0 < r) (hrSmall : r ≤ 1 / 2)
    (hInside : closedBall x (r / 2) ⊆ unitBall n) (hNear : dist x p ≤ r)
    (hq : ∀ y ∈ ball x (r / 8), DifferentiableAt ℝ q y)
    (hHolder : ∀ y ∈ ball x (r / 8), ∀ z ∈ ball x (r / 8),
      ‖fderiv ℝ q y - fderiv ℝ q z‖ ≤ (H / r ^ β) * ‖y - z‖ ^ β)
    (hTrace : ∀ y ∈ dirichletBoundaryCap p (2 * r),
      |q y / dirichletBoundaryDistanceProxy y - a| ≤ C * (2 * r) ^ α) :
    ‖fderiv ℝ q x - a • fderiv ℝ (@dirichletBoundaryDistanceProxy n) x‖ ≤
      16 * (C * (2 : ℝ) ^ (1 + α)) * r ^ (α / 2) +
        ((H + B) / (8 : ℝ) ^ β) * r ^ (α * β / 2) := by
  let F : E n → ℝ := fun z => q z - a * dirichletBoundaryDistanceProxy z
  let A : ℝ := C * (2 : ℝ) ^ (1 + α)
  let ε : ℝ := r * r ^ (α / 2) / 8
  have hr1 : r ≤ 1 := by linarith
  have hpβ : 0 < r ^ β := Real.rpow_pos_of_pos hr _
  have hpβ1 : r ^ β ≤ 1 := Real.rpow_le_one hr.le hr1 hβ.le
  have hε : 0 < ε := (dirichlet_boundary_interpolation_scale hr hr1 hα.le).1
  have hεr : ε < r / 8 := by
    apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 8)
    exact mul_lt_of_lt_one_right hr (Real.rpow_lt_one hr.le (by linarith) (by positivity))
  have hDiam (y : E n) (hy : y ∈ ball x (r / 8)) (z : E n) (hz : z ∈ ball x (r / 8)) :
      ‖y - z‖ ≤ 1 := by
    rw [← dist_eq_norm]
    have h := dist_triangle y x z
    rw [dist_comm x z] at h
    have hy' := mem_ball.mp hy
    have hz' := mem_ball.mp hz
    linarith
  have hHolderF := dirichlet_sub_boundaryProxy_derivative_holder hq hβ1 hHolder hDiam a
  have hCoeff : H / r ^ β + |a| ≤ (H + B) / r ^ β := by
    have hab : |a| ≤ B / r ^ β := (le_div_iff₀ hpβ).mpr
      ((mul_le_mul ha hpβ1 hpβ.le hB).trans_eq (mul_one B))
    calc
      H / r ^ β + |a| ≤ H / r ^ β + B / r ^ β := add_le_add le_rfl hab
      _ = (H + B) / r ^ β := by ring
  have hFHolder (y : E n) (hy : y ∈ ball x (r / 8)) (z : E n) (hz : z ∈ ball x (r / 8)) :
      ‖fderiv ℝ F y - fderiv ℝ F z‖ ≤ ((H + B) / r ^ β) * ‖y - z‖ ^ β :=
    (hHolderF y hy z hz).trans (mul_le_mul_of_nonneg_right hCoeff
      (Real.rpow_nonneg (norm_nonneg _) _))
  have hρ (z : E n) :=
    ((contDiff_dirichletBoundaryDistanceProxy (n := n)).differentiable (by simp) z).hasFDerivAt
  have hFD (y : E n) (hy : y ∈ ball x (r / 8)) : DifferentiableAt ℝ F y :=
    (hq y hy).sub ((hρ y).differentiableAt.const_mul a)
  have hValue (y : E n) (hy : y ∈ ball x (r / 8)) : ‖F y‖ ≤ A * r ^ (1 + α) := by
    simpa only [F, A, Real.norm_eq_abs] using
      abs_dirichlet_boundary_remainder_le hC hp hr hInside hNear hTrace y hy
  have hEstimate := norm_dirichlet_fderiv_le_at_scale
    (M := A * r ^ (1 + α)) (H := (H + B) / r ^ β) (β := β)
    (by dsimp [A]; positivity) (by positivity) hβ.le hε hεr hFD hFHolder hValue
  have hx : x ∈ ball x (r / 8) := mem_ball_self (by positivity)
  have he : fderiv ℝ F x =
      fderiv ℝ q x - a • fderiv ℝ (@dirichletBoundaryDistanceProxy n) x :=
    ((hq x hx).hasFDerivAt.sub ((hρ x).const_mul a)).fderiv
  rw [he] at hEstimate
  exact hEstimate.trans_eq (dirichlet_boundary_interpolation_error_identity (A := A) (H := H + B) hr)

end KEBall
