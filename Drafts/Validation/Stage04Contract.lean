import Drafts.KEBall.ComplexBochner

/-!
Stage04 same-author consumer. This is NOT an independent Comparator challenge.
The declarations below expose the intended complete input types for review.
-/
set_option autoImplicit false
open Set
open scoped ContDiff Manifold

namespace KEBall.Stage04Contract

theorem bochner_from_original_hypotheses {n : ℕ} {μ : ℝ} {u : KEBall.E n → ℝ}
    (hu : KEBall.IsSolution n μ u) {x : KEBall.E n}
    (hx : x ∈ KEBall.unitBall n) :
    KEBall.complexLaplacian u (KEBall.gradientNormSq u) x =
      (n : ℝ) + KEBall.gradientNormSq u x +
        KEBall.complexTensorNormSq u x (KEBall.covariantHessian20 u x) :=
  hu.complex_bochner_identity hx

theorem actual_einstein_from_original_hypotheses {n : ℕ} {μ : ℝ}
    {u : KEBall.E n → ℝ} (hu : KEBall.IsSolution n μ u)
    {p : KEBall.E n} (hp : p ∈ KEBall.unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (KEBall.E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (KEBall.E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ KEBall.unitBall n ∧
      (∀ x ∈ V, ∀ v w : KEBall.E n, g.inner x v w = KEBall.realMetricForm u x v w) ∧
      (∀ x ∈ V, ∀ v w : KEBall.E n, D.ricci x v w = g.inner x v w) :=
  hu.exists_local_einstein_metric hp

end KEBall.Stage04Contract
