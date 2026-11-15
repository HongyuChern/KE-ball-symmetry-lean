import Drafts.KEBall.BochnerNormTrace

/-!
Explicit endpoint type-check challenge for the Stage03 implementation.
Written in the same sequential session, NOT an independent Comparator run.
This named consumer proves the stated type using the implementation.
-/
set_option autoImplicit false
open Set
open scoped BigOperators Manifold

namespace KEBall.Stage03Contract

theorem endpoint_type_contract {n : ℕ} {μ : ℝ} {u : KEBall.E n → ℝ}
    (hu : KEBall.IsSolution n μ u) {p : KEBall.E n}
    (hp : p ∈ KEBall.unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (KEBall.E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (KEBall.E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ KEBall.unitBall n ∧
      (∀ x ∈ V, ∀ v w : KEBall.E n,
        g.inner x v w = KEBall.realMetricForm u x v w) ∧
      (∀ x ∈ V, KEBall.hessianDefectNormSq D u x =
        2 * KEBall.complexTensorNormSq u x (KEBall.covariantHessian20 u x)) ∧
      (∀ x ∈ V, ∀ i : Fin n, KEBall.complexConnectionTrace D x i =
        -KEBall.partialZ i (fun y => (u y : ℂ)) x) ∧
      (∀ x ∈ V, ∀ i j : Fin n,
        KEBall.partialBar j (fun y => KEBall.complexConnectionTrace D y i) x =
          -KEBall.complexHessian u x i j) ∧
      (∀ x ∈ V, 2 * KEBall.complexLaplacian u (KEBall.gradientNormSq u) x =
        2 * (n : ℝ) + 2 * KEBall.complexTensorNormSq u x
          (KEBall.covariantHessian20 u x) +
          D.ricci x (D.gradient u x) (D.gradient u x)) :=
  hu.exists_local_bochner_norm_trace hp

end KEBall.Stage03Contract
