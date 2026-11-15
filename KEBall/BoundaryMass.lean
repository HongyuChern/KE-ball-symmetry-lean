import KEBall.BoundaryConormal

/-! The manuscript's mass identity as a consequence of the actual
nonzero-boundary conormal Green theorem, applied to the solution itself. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators

namespace KEBall

theorem sphere_conormal_self {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hzero : ∀ y ∈ unitSphere n, u y = 0)
    {x : E n} (hx : x ∈ unitSphere n) :
    conormalDerivative u u x = 2 * boundarySlope u x := by
  have hnormal := horizontalGradient_inner_normal (boundarySlope u) hx
  have hhopf := horizontalGradient_inner_hopf (boundarySlope u) hx
  have hi : inner ℝ (horizontalGradient (boundarySlope u) x)
      (horizontalGradient u x) = 0 := by
    rw [real_inner_comm, inner_horizontalGradient u hnormal hhopf]
    exact sphere_tangent_deriv_zero hu hzero hx hnormal
  rw [conormalDerivative, hi, zero_div, sub_zero, boundarySlope]
  ring

theorem IsSolution.mass_identity {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    (∫ x in unitBall n, (complexHessian u x).det.re ∂volume0 n) =
      ∫ x : Sphere n, boundarySlope u x.1 ^ n ∂sphere0 n := by
  have hg := hu.conormalGreen hn hu.2.1
  have hL : (∫ x in unitBall n,
      complexLaplacian u u x * (complexHessian u x).det.re ∂volume0 n) =
      (n : ℝ) * ∫ x in unitBall n, (complexHessian u x).det.re ∂volume0 n := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x hx
    dsimp only
    rw [hu.complexLaplacian_self (Metric.ball_subset_closedBall hx)]
  have hS : (∫ x : Sphere n,
      boundarySlope u x.1 ^ (n - 1) * conormalDerivative u u x.1 ∂sphere0 n) =
      2 * ∫ x : Sphere n, boundarySlope u x.1 ^ n ∂sphere0 n := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only
    rw [sphere_conormal_self hu.2.1 hu.2.2.2.2 x.2]
    have hp : boundarySlope u x.1 ^ (n - 1) * boundarySlope u x.1 =
        boundarySlope u x.1 ^ n := by
      rw [← pow_succ]
      congr 1
      omega
    nlinarith [hp]
  rw [hL, hS] at hg
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  apply (mul_left_cancel₀ hnR)
  nlinarith [hg]

#print axioms sphere_conormal_self
#print axioms IsSolution.mass_identity

end KEBall
