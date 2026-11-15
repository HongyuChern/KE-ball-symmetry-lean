import Drafts.KEBall.AuxiliaryPAlgebra
import Drafts.KEBall.AuxiliaryPPositivity
import Drafts.KEBall.AuxiliaryPDifferential
import Drafts.KEBall.ComplexBochner

/-!
Explicit type consumers for the Stage05 source drafts. NOT kernel checked.
This is not an independent Comparator challenge and not a proof of the full
LogarithmicFluxStatement. The scalar Kato statement below concerns explicit
finite-frame algebra, not the as-yet-unidentified derivative of auxiliaryP.
-/

set_option autoImplicit false
open scoped BigOperators

namespace KEBall.Stage05Contract

theorem positivity_from_original_hypotheses {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : KEBall.E n → ℝ} (hu : KEBall.IsSolution n μ u) :
    ∀ x ∈ KEBall.closedUnitBall n, 1 < KEBall.auxiliaryP u x := by
  intro x hx
  exact hu.auxiliaryP_gt_one_closedBall hn hx

theorem weight_laplacian_from_original_hypotheses {n : ℕ}
    {μ : ℝ} {u : KEBall.E n → ℝ} (hu : KEBall.IsSolution n μ u) :
    ∀ x ∈ KEBall.closedUnitBall n,
      KEBall.complexLaplacian u (KEBall.expWeight u) x =
        KEBall.expWeight u x * (-(n : ℝ) / (n + 1 : ℝ) +
          KEBall.gradientNormSq u x / (n + 1 : ℝ) ^ 2) := by
  intro x hx
  exact hu.complexLaplacian_expWeight hx

theorem bochner_from_original_hypotheses {n : ℕ} {μ : ℝ}
    {u : KEBall.E n → ℝ} (hu : KEBall.IsSolution n μ u)
    {x : KEBall.E n} (hx : x ∈ KEBall.unitBall n) :
    KEBall.complexLaplacian u (KEBall.gradientNormSq u) x =
      (n : ℝ) + KEBall.gradientNormSq u x +
        KEBall.complexTensorNormSq u x (KEBall.covariantHessian20 u x) :=
  hu.complex_bochner_identity hx

theorem finite_frame_Kato {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℂ) (v : ι → ℂ) (e k : ℝ) :
    (e / k) ^ 2 * AuxiliaryPAlgebra.vectorNormSq (AuxiliaryPAlgebra.contract T v) ≤
      (AuxiliaryPAlgebra.pValue e k (AuxiliaryPAlgebra.vectorNormSq v) - e) *
        (e / k * AuxiliaryPAlgebra.tensorNormSq T) :=
  AuxiliaryPAlgebra.kato_inequality T v e k

end KEBall.Stage05Contract
