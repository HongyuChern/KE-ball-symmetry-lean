import Drafts.KEBall.BochnerTransport

/-!
Explicit consumers of the Stage01 draft, stated directly from `IsSolution`.
Not a Comparator receipt or an independent semantic review.
Status: SOURCE_DRAFT_NOT_KERNEL_CHECKED.
-/

set_option autoImplicit false
open Set
open scoped ContDiff Manifold BigOperators
open KEBall

namespace KEBallStage01Smoke

theorem smooth_q_from_original_assumptions {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) :
    ContDiffOn ℝ ∞ (gradientNormSq u) (unitBall n) :=
  hu.gradientNormSq_contDiffOn_ball

theorem transport_from_original_assumptions {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V,
        2 * complexLaplacian u (gradientNormSq u) x =
          (∑ i, ∑ j, (D.hessian u x
            (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) +
          D.ricci x (D.gradient u x) (D.gradient u x)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg, _, _, _, _, hTransport⟩ :=
    hu.exists_local_bochner_transport hp
  exact ⟨g, D, V, hV, hpV, hVB, hg, hTransport⟩

end KEBallStage01Smoke
