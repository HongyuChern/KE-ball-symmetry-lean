import Drafts.KEBall.HessianDefect

/-! Explicit original-assumption consumers. These are source drafts, not an
independent Comparator run or a receipt from the Lean kernel. -/

set_option autoImplicit false
open Set
open scoped ContDiff Manifold BigOperators
open KEBall

namespace KEBallStage02Smoke

theorem exact_paper_hessian_from_original_assumptions {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, ∀ i j : Fin n,
        covariantHessian20 u x i j = complexify20 (D.hessian u x) i j) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg, _, hS⟩ := hu.exists_local_hessian20_bridge hp
  exact ⟨g, D, V, hV, hpV, hVB, hg, hS⟩

theorem defect_bochner_from_original_assumptions {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V,
        2 * complexLaplacian u (gradientNormSq u) x =
          2 * (n : ℝ) + hessianDefectNormSq D u x +
            D.ricci x (D.gradient u x) (D.gradient u x)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg, _, _, _, hB⟩ :=
    hu.exists_local_bochner_hessian20 hp
  exact ⟨g, D, V, hV, hpV, hVB, hg, hB⟩

end KEBallStage02Smoke
