import KEBall.DirichletTraceEllipticity
import KEBall.DirichletPositiveOperatorNorm
import KEBall.DirichletCofactorHessian

/-! Bounds for the actual real cofactor operator from complex trace and
positive density, retaining the original normalization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff

namespace KEBall

theorem dirichletCofactorOperator_bounds_of_det_trace {n : ℕ}
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hDensity : ∀ y ∈ closedUnitBall n, a ^ n ≤ f y ∧ f y ≤ b ^ n)
    (hTrace : ∀ y ∈ closedUnitBall n, (complexHessian u y).trace.re ≤ D)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    ‖dirichletCofactorOperator u x‖ ≤ b ^ n * ((a ^ n / D ^ (n - 1))⁻¹ / 4) ∧
      ∀ v : E n,
        (a ^ n * (D⁻¹ / 4)) * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v := by
  let hp := dirichlet_posDef_on_closedBall hu hf huP hEq ha
    (fun y hy => (hDensity y (ball_subset_closedBall hy)).1) hx
  have hdet := dirichlet_det_eq_on_closedBall hu hf huP hEq hx
  have hRank := complexLaplacian_rankOne_bounds_of_det_trace hu hf huP hEq ha hD
    (fun y hy => (hDensity y hy).1) hTrace hx
  have hLow (v : E n) :
      (a ^ n * (D⁻¹ / 4)) * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v := by
    rw [dirichletCofactorOperator_inner_self hp, hdet]
    calc
      _ = a ^ n * ((D⁻¹ / 4) * ‖v‖ ^ 2) := by ring
      _ ≤ f x * ((D⁻¹ / 4) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hDensity x hx).1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hRank v).1
        ((pow_pos ha n).le.trans (hDensity x hx).1)
  have hUp (v : E n) : inner ℝ (dirichletCofactorOperator u x v) v ≤
      (b ^ n * ((a ^ n / D ^ (n - 1))⁻¹ / 4)) * ‖v‖ ^ 2 := by
    rw [dirichletCofactorOperator_inner_self hp, hdet]
    calc
      _ ≤ f x * (((a ^ n / D ^ (n - 1))⁻¹ / 4) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hRank v).2
          ((pow_pos ha n).le.trans (hDensity x hx).1)
      _ ≤ b ^ n * (((a ^ n / D ^ (n - 1))⁻¹ / 4) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hDensity x hx).2 (by positivity)
      _ = _ := by ring
  refine ⟨norm_le_of_symmetric_nonneg_quadratic_bound _ ?_ (by positivity) ?_ hUp, hLow⟩
  · intro v w
    rw [dirichletCofactorOperator_inner, dirichletCofactorOperator_inner,
      hermitianRealification_symm hp.isHermitian.adjugate v w]
  · intro v
    exact (show 0 ≤ (a ^ n * (D⁻¹ / 4)) * ‖v‖ ^ 2 by positivity).trans (hLow v)

end KEBall
