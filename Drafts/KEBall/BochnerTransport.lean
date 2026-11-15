import KEBall.ScalarLaplacian
import KEBall.ComplexMaximum
import Drafts.KEBall.GradientRegularity

/-!
# Transporting the retained real Bochner identity to the actual KE potential

Status: SOURCE_DRAFT_NOT_KERNEL_CHECKED in the 2026-10-13 Stage01 delivery.
The inherited `ScalarLaplacian` module is also awaiting current replay.

One and the same constructed metric and connection carry all identities.
The derivative of the real Laplacian is proved zero locally, not supplied
as an assumption. The final identity retains the genuine real Ricci and
covariant-Hessian terms. Their complex identifications remain outstanding;
this module does NOT claim the full complex KE Bochner formula.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

/-- A neighbourhood-constant actual scalar Laplacian has zero differential.
This is a locality lemma, not an assumption about the KE potential. -/
theorem laplacian_mvfderiv_eq_zero_of_eventually_const {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {u : E n → ℝ} {x : E n} {c : ℝ}
    (hconst : D.laplacian u =ᶠ[𝓝 x] (fun _ => c)) :
    mvfderiv (𝓡 (2 * n)) (D.laplacian u) x = 0 := by
  rw [Poincare.mvfderiv_eq_of_eventuallyEq hconst, mvfderiv_const]

/-- Transport on the original solution, without assumed Ricci, Hessian,
gradient-norm or Laplacian identification fields.

For this SAME locally constructed `g,D`, the last conclusion is
`2 Lq = |Hess_G u|² + Ric_G(grad_G u, grad_G u)`.
It is not yet `Lq = n + q + |S|²`. -/
theorem IsSolution.exists_local_bochner_transport {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {p : E n}
    (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, g.inner x (D.gradient u x) (D.gradient u x) =
        2 * gradientNormSq u x) ∧
      (∀ x ∈ V, ∀ h : E n → ℝ, ContDiffAt ℝ ∞ h x →
        D.laplacian h x = 2 * complexLaplacian u h x) ∧
      (∀ x ∈ V, D.laplacian u x = 2 * (n : ℝ)) ∧
      (∀ x ∈ V, mvfderiv (𝓡 (2 * n)) (D.laplacian u) x = 0) ∧
      (∀ x ∈ V,
        2 * complexLaplacian u (gradientNormSq u) x =
          (∑ i, ∑ j, (D.hessian u x
            (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) +
          D.ricci x (D.gradient u x) (D.gradient u x)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg, hOp, hLap⟩ :=
    hu.exists_local_complex_laplacian hp
  have huV := hu.contDiffOn_ball.mono hVB
  have hNorm (x : E n) (hx : x ∈ V) :
      g.inner x (D.gradient u x) (D.gradient u x) =
        2 * gradientNormSq u x := by
    have huAt := huV.contDiffAt (hV.mem_nhds hx)
    exact gradient_normSq_eq_twice_complex D
      (huAt.differentiableAt (by simp))
      (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hx)))
      (hg x hx)
  have hZero (x : E n) (hx : x ∈ V) :
      mvfderiv (𝓡 (2 * n)) (D.laplacian u) x = 0 := by
    apply laplacian_mvfderiv_eq_zero_of_eventually_const D
      (c := 2 * (n : ℝ))
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hLap y hy
  refine ⟨g, D, V, hV, hpV, hVB, hg, hNorm, hOp, hLap, hZero, ?_⟩
  intro x hx
  have hq := hu.gradientNormSq_contDiffAt (hVB hx)
  have hNormNear :
      (fun y => g.inner y (D.gradient u y) (D.gradient u y)) =ᶠ[𝓝 x]
        (fun y => 2 * gradientNormSq u y) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hNorm y hy
  have hNormLap :
      D.laplacian (fun y => g.inner y (D.gradient u y) (D.gradient u y)) x =
        4 * complexLaplacian u (gradientNormSq u) x := by
    rw [D.laplacian_eq_of_eventuallyEq hNormNear,
      hOp x hx (fun y => 2 * gradientNormSq u y) (contDiffAt_const.mul hq),
      complexLaplacian_const_mul_at u hq 2]
    ring
  have hB := bochner_on_open D hV huV hx
  rw [hNormLap, hZero x hx] at hB
  simp only [zero_apply, mul_zero, add_zero] at hB
  linarith

end KEBall
