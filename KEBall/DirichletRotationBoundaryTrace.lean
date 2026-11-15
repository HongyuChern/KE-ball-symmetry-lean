import KEBall.DirichletBoundaryQuotientTrace
import KEBall.DirichletRotationCofactorEquation

/-!
# The rotation quotient trace is the actual mixed Hessian

For a zero-boundary potential and a tangent linear field T, differentiating
Du(x)(T x) in the outward normal direction gives D2u(p)(p,T p).
The inward quotient by rho therefore has the negative of this trace.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem fderiv_dirichlet_linearFieldDerivative_of_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (T : E n →L[ℝ] E n) (v : E n) :
    fderiv ℝ (fun y => fderiv ℝ u y (T y)) x v =
      realHessian u x v (T x) + fderiv ℝ u x (T v) := by
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h := hd.clm_apply (T.hasFDerivAt (x := x))
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    realHessian, add_comm]

theorem dirichlet_rotation_normalDerivative_eq_mixed {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ p ∈ unitSphere n, u p = 0)
    (T : E n →L[ℝ] E n) (hT : ∀ p ∈ unitSphere n, inner ℝ p (T p) = 0)
    {p : E n} (hp : p ∈ unitSphere n) :
    fderiv ℝ (fun x => fderiv ℝ u x (T x)) p p = realHessian u p p (T p) := by
  rw [fderiv_dirichlet_linearFieldDerivative_of_C2
    ((hu.contDiffAt (sphere_subset_closedBall hp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    dirichlet_linearFieldDerivative_zero_on_sphere hu hu0 T hT hp, add_zero]

theorem tendsto_dirichlet_rotation_quotient_radial {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ p ∈ unitSphere n, u p = 0)
    (T : E n →L[ℝ] E n) (hT : ∀ p ∈ unitSphere n, inner ℝ p (T p) = 0)
    {p : E n} (hp : p ∈ unitSphere n) :
    Tendsto (fun s : ℝ => fderiv ℝ u ((1 - s) • p) (T ((1 - s) • p)) /
      dirichletBoundaryDistanceProxy ((1 - s) • p))
      (𝓝[>] (0 : ℝ)) (𝓝 (-realHessian u p p (T p))) := by
  have hq := smoothNear_dirichlet_linearFieldDerivative hu T
  have hD := ((hq.contDiffAt (sphere_subset_closedBall hp)).differentiableAt (by simp)).hasFDerivAt
  have h := tendsto_dirichlet_boundary_quotient_radial hp hD
    (dirichlet_linearFieldDerivative_zero_on_sphere hu hu0 T hT hp)
  rwa [dirichlet_rotation_normalDerivative_eq_mixed hu hu0 T hT hp] at h

theorem abs_dirichlet_rotation_quotient_add_mixed_le_oscillation {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ p ∈ unitSphere n, u p = 0)
    (T : E n →L[ℝ] E n) (hT : ∀ p ∈ unitSphere n, inner ℝ p (T p) = 0)
    {B : ℝ} (hB : ∀ x ∈ unitBall n,
      |fderiv ℝ u x (T x) / dirichletBoundaryDistanceProxy x| ≤ B)
    {p : E n} (hp : p ∈ unitSphere n) {r : ℝ} (hr : 0 < r)
    {x : E n} (hx : x ∈ dirichletBoundaryCap p r) :
    |fderiv ℝ u x (T x) / dirichletBoundaryDistanceProxy x + realHessian u p p (T p)| ≤
      dirichletBoundaryOscillation
        (fun y => fderiv ℝ u y (T y) / dirichletBoundaryDistanceProxy y) p r := by
  have hq := smoothNear_dirichlet_linearFieldDerivative hu T
  have hD := ((hq.contDiffAt (sphere_subset_closedBall hp)).differentiableAt (by simp)).hasFDerivAt
  have h := abs_dirichlet_quotient_add_normal_le_oscillation hp hD
    (dirichlet_linearFieldDerivative_zero_on_sphere hu hu0 T hT hp) hB hr hx
  rwa [dirichlet_rotation_normalDerivative_eq_mixed hu hu0 T hT hp] at h

theorem abs_dirichlet_rotation_mixed_sub_le_of_power {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hu0 : ∀ p ∈ unitSphere n, u p = 0)
    (T : E n →L[ℝ] E n) (hT : ∀ p ∈ unitSphere n, inner ℝ p (T p) = 0)
    {B C α : ℝ} (hC : 0 ≤ C)
    (hB : ∀ x ∈ unitBall n, |fderiv ℝ u x (T x) / dirichletBoundaryDistanceProxy x| ≤ B)
    (hPower : ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      dirichletBoundaryOscillation
        (fun x => fderiv ℝ u x (T x) / dirichletBoundaryDistanceProxy x) p r ≤ C * r ^ α)
    {p p' : E n} (hp : p ∈ unitSphere n) (hp' : p' ∈ unitSphere n)
    (hDist : dist p p' ≤ 1 / 2) :
    |realHessian u p p (T p) - realHessian u p' p' (T p')| ≤
      C * (2 * dist p p') ^ α := by
  have hq := smoothNear_dirichlet_linearFieldDerivative hu T
  have hD (p : E n) (hp : p ∈ unitSphere n) :=
    ((hq.contDiffAt (sphere_subset_closedBall hp)).differentiableAt (by simp)).hasFDerivAt
  have h := abs_dirichlet_boundary_normal_sub_le_of_power hD
    (fun p hp => dirichlet_linearFieldDerivative_zero_on_sphere hu hu0 T hT hp)
    hC hB hPower hp hp' hDist
  rwa [dirichlet_rotation_normalDerivative_eq_mixed hu hu0 T hT hp,
    dirichlet_rotation_normalDerivative_eq_mixed hu hu0 T hT hp'] at h

end KEBall
