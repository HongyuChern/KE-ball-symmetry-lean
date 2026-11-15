import Drafts.KEBall.ExteriorMeasure
import Drafts.Validation.Stage10Contract

/-! Stage11 SOURCE_DRAFT_UNCOMPILED. Actual exterior products, evaluation,
Euclidean top-form measures, and the unchanged seven frozen specifications. -/
set_option autoImplicit false
open MeasureTheory

namespace KEBall.Stage11Contract

theorem exterior_geometry {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) :
    (∀ x ∈ closedUnitBall n, ∀ v w : E n,
      exteriorEvaluation ![v, w] (d0Exterior u x) =
        ((fderiv ℝ (fun y => dcZeroForm u y w) x v -
          fderiv ℝ (fun y => dcZeroForm u y v) x w : ℝ) : ℂ)) ∧
    (∀ x : E n, d0Exterior u x ^ n =
      (complexHessian u x).det • normalizedExteriorVolume n) ∧
    (d0TopMeasure u).restrict (unitBall n) =
      ((volume0 n).restrict (unitBall n)).withDensity
        (fun x => ENNReal.ofReal (μ * Real.exp (-u x))) ∧
    (d1TopMeasure (fun y => u y / 2)).restrict (unitBall n) =
      (d0TopMeasure u).restrict (unitBall n) :=
  ⟨fun _ hx v w => hu.d0Exterior_evaluates_derivative hx v w,
    d0Exterior_top u, hu.d0TopMeasure_eq, hu.d1TopMeasure_half⟩

theorem all_frozen_specifications :
    ClassificationStatement ∧ RadialExistenceStatement ∧ SolutionCountsStatement ∧
    BoundaryIdentitiesStatement ∧ LowerSlopeStatement ∧ LogarithmicFluxStatement ∧
    NormalizedClassificationStatement := Stage10Contract.all_frozen_specifications

#print axioms exterior_geometry
#print axioms all_frozen_specifications

end KEBall.Stage11Contract
