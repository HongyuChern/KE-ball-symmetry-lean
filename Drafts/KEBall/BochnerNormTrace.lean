import Drafts.KEBall.HessianNormBridge
import Drafts.KEBall.ConnectionTrace

/-!
# A same-object consumer of the tensor norm and actual connection trace

Stage03 source draft; no current Lean kernel receipt.
The uneliminated term is the retained real Ricci evaluated on the actual
gradient. No Einstein identity is an input, a field, or a hidden instance.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

theorem IsSolution.exists_local_bochner_norm_trace {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, hessianDefectNormSq D u x =
        2 * complexTensorNormSq u x (covariantHessian20 u x)) ∧
      (∀ x ∈ V, ∀ i : Fin n, complexConnectionTrace D x i =
        -partialZ i (fun y => (u y : ℂ)) x) ∧
      (∀ x ∈ V, ∀ i j : Fin n,
        partialBar j (fun y => complexConnectionTrace D y i) x =
          -complexHessian u x i j) ∧
      (∀ x ∈ V, 2 * complexLaplacian u (gradientNormSq u) x =
        2 * (n : ℝ) + 2 * complexTensorNormSq u x (covariantHessian20 u x) +
          D.ricci x (D.gradient u x) (D.gradient u x)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg, _, _, _, hB⟩ :=
    hu.exists_local_bochner_hessian20 hp
  have huV := hu.contDiffOn_ball.mono hVB
  have hN (x : E n) (hx : x ∈ V) :
      hessianDefectNormSq D u x =
        2 * complexTensorNormSq u x (covariantHessian20 u x) :=
    hessianDefectNormSq_eq_twice_complexTensorNormSq D hV huV hg hx
      (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hx)))
  refine ⟨g, D, V, hV, hpV, hVB, hg, hN, ?_, ?_, ?_⟩
  · intro x hx i
    exact hu.complexConnectionTrace_eq D hV hVB hg hx i
  · intro x hx i j
    exact hu.partialBar_complexConnectionTrace D hV hVB hg hx i j
  · intro x hx
    rw [hB x hx, hN x hx]

end KEBall
