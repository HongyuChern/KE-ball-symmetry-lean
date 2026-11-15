import KEBall.LocalBochner

/-!
# Local smoothness of the actual complex gradient norm

Status: SOURCE_DRAFT_NOT_KERNEL_CHECKED in the 2026-10-13 Stage01 delivery.
This file is isolated from the inherited production imports.

The potential is not assumed globally smooth. An actual scalar cutoff and
an actual local metric realization are used. Metric-gradient regularity is
provided by the retained Poincare library; the coordinate quantity `q` is
then identified with one half of that real squared norm on a neighbourhood.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped ContDiff Manifold Topology BigOperators Bundle

namespace KEBall

/-- Smoothness of a globally smooth scalar's squared metric-gradient norm.
This is an actual use of the upstream gradient and metric regularity API. -/
theorem metric_gradient_normSq_contDiff {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => g.inner y (D.gradient f y) (D.gradient f y)) := by
  have hfM : ContMDiff (𝓡 (2 * n)) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_iff_contDiff.mpr hf
  apply contMDiff_iff_contDiff.mp
  intro y
  have hgrad := D.contMDiffAt_gradient (hfM y)
  have h := ((g.contMDiff y).clm_bundle_apply hgrad).clm_bundle_apply hgrad
  simpa using (contMDiffAt_totalSpace.mp h).2

/-- The real coordinate function `gradientNormSq u` is smooth near every
interior point, with no additional inverse-metric or bridge hypotheses. -/
theorem IsSolution.gradientNormSq_contDiffAt {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    ContDiffAt ℝ ∞ (gradientNormSq u) x := by
  obtain ⟨g, D, V, hV, hxV, hVB, hg⟩ := hu.exists_local_metric hx
  have huV := hu.contDiffOn_ball.mono hVB
  obtain ⟨f, hf, heq⟩ := exists_smooth_scalar_extension hV hxV huV
  have hs := metric_gradient_normSq_contDiff D hf
  have hhalf : ContDiffAt ℝ ∞
      (fun y => g.inner y (D.gradient f y) (D.gradient f y) * (2 : ℝ)⁻¹) x :=
    hs.contDiffAt.mul contDiffAt_const
  apply hhalf.congr_of_eventuallyEq
  filter_upwards [heq.eventually_nhds, hV.mem_nhds hxV] with y hy hyV
  have hgrad := metric_gradient_eq_of_eventuallyEq D hy
  have huY := huV.contDiffAt (hV.mem_nhds hyV)
  have hnorm := gradient_normSq_eq_twice_complex D
    (huY.differentiableAt (by simp))
    (hu.det_isUnit_closedBall (Metric.ball_subset_closedBall (hVB hyV)))
    (hg y hyV)
  rw [hgrad, hnorm]
  ring

theorem IsSolution.gradientNormSq_contDiffOn_ball {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    ContDiffOn ℝ ∞ (gradientNormSq u) (unitBall n) := by
  intro x hx
  exact (hu.gradientNormSq_contDiffAt hx).contDiffWithinAt

end KEBall
