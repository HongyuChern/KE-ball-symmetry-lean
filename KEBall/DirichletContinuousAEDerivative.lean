import KEBall.DirichletMollifiedDerivative
import KEBall.DirichletLocalMollifierConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# A continuous a.e. derivative of a Lipschitz function is its classical derivative

The proof uses the actual normalized smooth kernels, the proved integration
by parts formula, and locally uniform convergence of their derivatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped Convolution ContDiff NNReal Topology

noncomputable section

namespace KEBall

theorem hasFDerivAt_of_dirichlet_continuous_ae_fderiv {n : ℕ}
    {f : E n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {s : Set (E n)} (hs : IsOpen s)
    {H : E n → E n →L[ℝ] ℝ} (hH : ContinuousOn H s)
    (he : H =ᵐ[(volume : Measure (E n)).restrict s] fderiv ℝ f)
    {x : E n} (hx : x ∈ s) : HasFDerivAt f (H x) x := by
  classical
  let F : E n → E n →L[ℝ] ℝ := s.piecewise H (fderiv ℝ f)
  have hFE : EqOn F H s := fun y hy => piecewise_eq_of_mem s H (fderiv ℝ f) hy
  have hFAe : F =ᵐ[volume] fderiv ℝ f := by
    have he' : ∀ᵐ y ∂(volume : Measure (E n)), y ∈ s → H y = fderiv ℝ f y :=
      (ae_restrict_iff' hs.measurableSet).mp he
    filter_upwards [he'] with y hy
    by_cases hys : y ∈ s
    · exact (hFE hys).trans (hy hys)
    · exact piecewise_eq_of_notMem s H (fderiv ℝ f) hys
  have hFC : ContinuousOn F s := hH.congr hFE
  have hFm : AEStronglyMeasurable F volume :=
    (measurable_fderiv ℝ f).aestronglyMeasurable.congr hFAe.symm
  let φ : ℕ → ContDiffBump (0 : E n) := PshLines.shrinkingBump 1 zero_lt_one
  let fₖ : ℕ → E n → ℝ := fun k => PshLines.mollify volume f (φ k)
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    PshLines.tendsto_shrinkingBump_rOut 1 zero_lt_one
  have hJ := tendstoLocallyUniformlyOn_dirichlet_normedConvolution hs hFC hFm hφ
  have hConv (k : ℕ) : (φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F =
      fderiv ℝ (fₖ k) := by
    rw [show fderiv ℝ (fₖ k) =
      (φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ f from
      fderiv_dirichlet_mollify_eq_convolution hf (φ k)]
    exact convolution_congr _ (EventuallyEq.refl _ _) hFAe
  have hJ' : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fₖ k)) H atTop s :=
    (hJ.congr fun k y _ => congrFun (hConv k) y).congr_right hFE
  have hSmooth (k : ℕ) : ContDiff ℝ ∞ (fₖ k) :=
    PshLines.contDiff_mollify volume hf.continuous.locallyIntegrable (φ k)
  have hValue (y : E n) : Tendsto (fun k => fₖ k y) atTop (𝓝 (f y)) := by
    simpa only [fₖ, PshLines.mollify_eq_convolution] using
      (ContDiffBump.convolution_tendsto_right_of_continuous hφ hf.continuous y)
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn hs hJ'
    (fun k y _ => ((hSmooth k).differentiable (by simp) y).hasFDerivAt)
    (fun y _ => hValue y) hx

end KEBall
