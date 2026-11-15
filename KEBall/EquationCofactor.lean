import KEBall.Domain
import KEBall.CofactorDivergence

/-!
# The cofactor identity for the actual KE ball equation

This consumer takes precisely `IsSolution` from the independent domain layer.
Smoothness is recovered only locally; determinant invertibility follows from
the positive right-hand side of the equation. The derivative and transpose
conventions are definitionally those used in the general Piola module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators

namespace KEBall

theorem IsSolution.cofactor_divergence {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) (j : Fin n) :
    (∑ i : Fin n, partialZ i (fun y => (complexHessian u y).adjugate j i) x) = 0 := by
  have hxclosed : x ∈ closedUnitBall n := Metric.ball_subset_closedBall hx
  have hureal : ContDiffAt ℝ ∞ u x := hu.2.1.contDiffAt hxclosed
  have hucomplex : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hureal
  have hunit : IsUnit (complexHessian u x).det := by
    rw [hu.2.2.2.1 x hx]
    apply isUnit_iff_ne_zero.mpr
    exact_mod_cast mul_ne_zero (ne_of_gt hu.1) (Real.exp_ne_zero (-u x))
  exact cofactor_divergence_at hucomplex realDirection imagDirection hunit j

#print axioms IsSolution.cofactor_divergence

end KEBall
