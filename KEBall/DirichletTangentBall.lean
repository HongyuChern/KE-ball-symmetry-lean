import KEBall.DirichletAnnularComparison

/-!
# Tangent balls and the smooth boundary distance proxy

The radial parameter is the actual Euclidean distance to the unit sphere.
The proxy `(1 - norm(x)^2)/2` has a fixed polynomial Hessian and is comparable
to that distance in the closed unit ball.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped BigOperators ContDiff

noncomputable section

namespace KEBall

def dirichletTangentBallCenter {n : ℕ} (p : E n) (R : ℝ) : E n := (1 - R) • p

theorem norm_dirichletTangentBallCenter {n : ℕ} {p : E n} (hp : p ∈ unitSphere n)
    {R : ℝ} (hR : R ≤ 1) : ‖dirichletTangentBallCenter p R‖ = 1 - R := by
  rw [dirichletTangentBallCenter, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hR), mem_sphere_zero_iff_norm.mp hp, mul_one]

theorem dirichlet_tangent_closedBall_subset {n : ℕ} {p : E n} (hp : p ∈ unitSphere n)
    {R : ℝ} (hR : R ≤ 1) : closedBall (dirichletTangentBallCenter p R) R ⊆ closedUnitBall n := by
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  have h := norm_add_le (x - dirichletTangentBallCenter p R) (dirichletTangentBallCenter p R)
  rw [sub_add_cancel, norm_dirichletTangentBallCenter hp hR] at h
  have hx' : ‖x - dirichletTangentBallCenter p R‖ ≤ R := by
    simpa only [dist_eq_norm] using mem_closedBall.mp hx
  linarith

theorem dirichlet_tangent_ball_subset {n : ℕ} {p : E n} (hp : p ∈ unitSphere n)
    {R : ℝ} (hR : R ≤ 1) : ball (dirichletTangentBallCenter p R) R ⊆ unitBall n := by
  intro x hx
  apply mem_ball_zero_iff.mpr
  have h := norm_add_le (x - dirichletTangentBallCenter p R) (dirichletTangentBallCenter p R)
  rw [sub_add_cancel, norm_dirichletTangentBallCenter hp hR] at h
  have hx' : ‖x - dirichletTangentBallCenter p R‖ < R := by
    simpa only [dist_eq_norm] using mem_ball.mp hx
  linarith

theorem norm_dirichlet_radial_point {n : ℕ} {p : E n} (hp : p ∈ unitSphere n)
    {s : ℝ} (hs : s ≤ 1) : ‖(1 - s) • p‖ = 1 - s := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs),
    mem_sphere_zero_iff_norm.mp hp, mul_one]

theorem dist_dirichlet_radial_point_tangent_center {n : ℕ}
    {p : E n} (hp : p ∈ unitSphere n) {s R : ℝ} (hs : s ≤ R) :
    dist ((1 - s) • p) (dirichletTangentBallCenter p R) = R - s := by
  rw [dist_eq_norm, dirichletTangentBallCenter, ← sub_smul]
  have he : (1 - s) - (1 - R) = R - s := by ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs),
    mem_sphere_zero_iff_norm.mp hp, mul_one]

def dirichletBoundaryDistanceProxy {n : ℕ} (x : E n) : ℝ := (1 - ‖x‖ ^ 2) / 2

theorem dirichletBoundaryDistanceProxy_bounds {n : ℕ} {x : E n}
    (hx : x ∈ closedUnitBall n) :
    (1 - ‖x‖) / 2 ≤ dirichletBoundaryDistanceProxy x ∧
      dirichletBoundaryDistanceProxy x ≤ 1 - ‖x‖ := by
  have h0 := norm_nonneg x
  have h1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  unfold dirichletBoundaryDistanceProxy
  constructor <;> nlinarith

theorem dirichletBoundaryDistanceProxy_pos {n : ℕ} {x : E n} (hx : x ∈ unitBall n) :
    0 < dirichletBoundaryDistanceProxy x := by
  have h := (dirichletBoundaryDistanceProxy_bounds (ball_subset_closedBall hx)).1
  have hn : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  linarith

theorem dirichletBoundaryDistanceProxy_zero_on_sphere {n : ℕ} {x : E n}
    (hx : x ∈ unitSphere n) : dirichletBoundaryDistanceProxy x = 0 := by
  simp [dirichletBoundaryDistanceProxy, mem_sphere_zero_iff_norm.mp hx]

theorem contDiff_dirichletBoundaryDistanceProxy {n : ℕ} :
    ContDiff ℝ ∞ (@dirichletBoundaryDistanceProxy n) :=
  (contDiff_const.sub (contDiff_id.norm_sq (𝕜 := ℝ))).div_const 2

theorem realHessian_dirichletBoundaryDistanceProxy {n : ℕ} (x : E n) :
    realHessian (@dirichletBoundaryDistanceProxy n) x = -innerSL ℝ := by
  have he : (@dirichletBoundaryDistanceProxy n) =
      (-1 / 2 : ℝ) • dirichletQuadraticBarrier 1 (0 : E n) := by
    ext y
    simp only [dirichletBoundaryDistanceProxy, Pi.smul_apply, smul_eq_mul,
      dirichletQuadraticBarrier, sub_zero, one_pow]
    ring
  have hq : ContDiffAt ℝ 2 (dirichletQuadraticBarrier 1 (0 : E n)) x :=
    ((contDiff_dirichletQuadraticBarrier 1 (0 : E n)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  rw [he, dirichlet_realHessian_smul_C2 hq, realHessian_dirichletQuadraticBarrier,
    smul_smul]
  norm_num

theorem dirichletBilinearContraction_boundaryDistanceProxy {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (A : E n →L[ℝ] E n) (x : E n) :
    dirichletBilinearContraction b A (realHessian (@dirichletBoundaryDistanceProxy n) x) =
      -(∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i)) := by
  rw [realHessian_dirichletBoundaryDistanceProxy]
  simp only [dirichletBilinearContraction, _root_.neg_apply, Finset.sum_neg_distrib]
  rfl

end KEBall
