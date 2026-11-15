import Drafts.KEBall.NormalizedExterior
import Drafts.Validation.Stage13Contract

/-! Stage16 SOURCE_DRAFT_UNCOMPILED. The normalized frozen specification
and its genuine top-form probability measure are consumed together. -/
set_option autoImplicit false
open Set MeasureTheory

namespace KEBall.Stage16Contract

theorem normalized_exterior_geometry {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    γ < (n + 1 : ℝ) ∧
      IsProbabilityMeasure ((d0TopMeasure φ).restrict (unitBall n)) ∧
      (d0TopMeasure φ).restrict (unitBall n) =
        ((volume0 n).restrict (unitBall n)).withDensity
          (fun x => ENNReal.ofReal
            (Real.exp (-γ * φ x) / normalizingIntegral γ φ)) ∧
      (d1TopMeasure (fun y => φ y / 2)).restrict (unitBall n) =
        (d0TopMeasure φ).restrict (unitBall n) :=
  ⟨(hφ.boundaryPolynomial_parameter hn).1, hφ.d0TopMeasure_isProbability,
    hφ.d0TopMeasure_normalized, hφ.d1TopMeasure_half⟩

theorem all_frozen_specifications :
    ClassificationStatement ∧ RadialExistenceStatement ∧ SolutionCountsStatement ∧
    BoundaryIdentitiesStatement ∧ LowerSlopeStatement ∧ LogarithmicFluxStatement ∧
    NormalizedClassificationStatement := Stage13Contract.all_frozen_specifications

#print axioms normalized_exterior_geometry
#print axioms all_frozen_specifications

end KEBall.Stage16Contract
