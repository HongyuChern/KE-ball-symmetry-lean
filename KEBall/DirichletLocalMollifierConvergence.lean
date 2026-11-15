import KEBall.Domain
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Local uniform convergence of normalized mollification on an open continuity set. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped Convolution Topology

namespace KEBall

theorem tendstoLocallyUniformlyOn_dirichlet_normedConvolution {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : E n → F} {s : Set (E n)} (hs : IsOpen s) (hg : ContinuousOn g s)
    (hm : AEStronglyMeasurable g volume)
    {φ : ℕ → ContDiffBump (0 : E n)}
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun k => (φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) g atTop s := by
  apply tendstoLocallyUniformlyOn_iff_filter.mpr
  intro x hx
  rw [hs.nhdsWithin_eq hx, Metric.tendstoUniformlyOnFilter_iff]
  have hgc : ContinuousAt g x := (hg x hx).continuousAt (hs.mem_nhds hx)
  have hValue : Tendsto (fun p : ℕ × E n => g p.2) (atTop ×ˢ 𝓝 x) (𝓝 (g x)) :=
    hgc.tendsto.comp tendsto_snd
  have hConv : Tendsto (fun p : ℕ × E n =>
      ((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (g x)) :=
    ContDiffBump.convolution_tendsto_right (φ := fun p : ℕ × E n => φ p.1)
      (g := fun _ => g) (hφ.comp tendsto_fst) (Eventually.of_forall fun _ => hm)
      (hgc.tendsto.comp tendsto_snd) tendsto_snd
  have hDist : Tendsto (fun p : ℕ × E n => dist (g p.2)
      (((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p.2))
      (atTop ×ˢ 𝓝 x) (𝓝 0) := by
    simpa only [dist_self] using hValue.dist hConv
  intro ε hε
  exact hDist.eventually (gt_mem_nhds hε)

end KEBall
