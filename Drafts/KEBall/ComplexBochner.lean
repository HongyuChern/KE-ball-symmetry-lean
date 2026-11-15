import Drafts.KEBall.RicciBridge
import Drafts.KEBall.BochnerNormTrace

/-!
# The manuscript's complex Bochner identity via retained real geometry

Stage04 DRAFT. The whole local source closure still requires real Lean replay.
No Einstein, Laplacian, norm, or Bochner identity is assumed by the endpoint.
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

/-- Same-object integration: apply the derived Ricci formula to the very
connection already used in the upstream Bochner calculation. -/
theorem IsSolution.exists_local_complex_bochner {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, ∀ v w : E n, D.ricci x v w = g.inner x v w) ∧
      (∀ x ∈ V, complexLaplacian u (gradientNormSq u) x =
        (n : ℝ) + gradientNormSq u x +
          complexTensorNormSq u x (covariantHessian20 u x)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg, _, _, _, hB⟩ :=
    hu.exists_local_bochner_norm_trace hp
  have hRic (x : E n) (hx : x ∈ V) (v w : E n) :
      D.ricci x v w = g.inner x v w :=
    hu.retained_ricci_eq_metric D hV hVB hg hx v w
  refine ⟨g, D, V, hV, hpV, hVB, hg, hRic, ?_⟩
  intro x hx
  have h := hB x hx
  rw [hRic x hx] at h
  rw [gradient_normSq_eq_twice_complex D
    ((hu.2.1.contDiffAt (Metric.ball_subset_closedBall (hVB hx))).differentiableAt (by simp))
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hx))) (hg x hx)] at h
  linarith

/-- Proposition 3.1, the Lq identity: exactly the original differential
operators, at every interior point. This is an UNCOMPILED source endpoint. -/
theorem IsSolution.complex_bochner_identity {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    complexLaplacian u (gradientNormSq u) x =
      (n : ℝ) + gradientNormSq u x +
        complexTensorNormSq u x (covariantHessian20 u x) := by
  obtain ⟨g, D, V, _, hxV, _, _, _, hB⟩ := hu.exists_local_complex_bochner hx
  exact hB x hxV

end KEBall
