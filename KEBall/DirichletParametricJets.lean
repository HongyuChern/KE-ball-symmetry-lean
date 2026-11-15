import KEBall.DirichletRadialPullbackJetContinuity
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Spatial jets of a closed-parameter C2 family

The parameter interval is closed.  No extension in the parameter is
assumed: within derivatives on the product suffice to recover ordinary
spatial derivatives on its open spatial factor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem fderiv_dirichlet_parameter_slice {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (E n)} (hU : IsOpen U) {f : ℝ × E n → F}
    (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1 ×ˢ U))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) {x : E n} (hx : x ∈ U) :
    fderiv ℝ (fun y => f (r, y)) x =
      (fderivWithin ℝ f (Icc (0 : ℝ) 1 ×ˢ U) (r, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (E n)) := by
  have hD := (hf.differentiableOn (by norm_num) (r, x) ⟨hr, hx⟩).hasFDerivWithinAt
  exact (hD.comp_hasFDerivAt x (hasFDerivAt_prodMk_right r x) (by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ⟨hr, hy⟩)).fderiv

theorem realHessian_dirichlet_parameter_slice {n : ℕ}
    {U : Set (E n)} (hU : IsOpen U) {f : ℝ × E n → ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc (0 : ℝ) 1 ×ˢ U))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) {x : E n} (hx : x ∈ U) (v z : E n) :
    realHessian (fun y => f (r, y)) x v z =
      fderivWithin ℝ (fderivWithin ℝ f (Icc (0 : ℝ) 1 ×ˢ U))
        (Icc (0 : ℝ) 1 ×ˢ U) (r, x) (0, v) (0, z) := by
  let S := Icc (0 : ℝ) 1 ×ˢ U
  let G := fderivWithin ℝ f S
  let J := ContinuousLinearMap.inr ℝ ℝ (E n)
  have hUnique : UniqueDiffOn ℝ S := uniqueDiffOn_Icc_zero_one.prod hU.uniqueDiffOn
  have hG : ContDiffOn ℝ 1 G S := hf.fderivWithin hUnique (by norm_num)
  have hD := (hG.differentiableOn (by norm_num) (r, x) ⟨hr, hx⟩).hasFDerivWithinAt
  have hComp := hD.comp_hasFDerivAt x (hasFDerivAt_prodMk_right r x) (by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ⟨hr, hy⟩)
  have hP := hComp.clm_comp (hasFDerivAt_const J x)
  have he : fderiv ℝ (fun y => f (r, y)) =ᶠ[𝓝 x]
      (fun y => (G (r, y)).comp J) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_dirichlet_parameter_slice hU (hf.of_le (by norm_num)) hr hy
  rw [realHessian, he.fderiv_eq,
    show fderiv ℝ (fun y => (G (r, y)).comp J) x = _ from hP.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    _root_.zero_apply, map_zero,
    ContinuousLinearMap.inr_apply, J, zero_add]
  rfl

theorem continuousOn_dirichlet_parameter_spatial_jets {n : ℕ}
    {U : Set (E n)} (hU : IsOpen U) {f : ℝ × E n → ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc (0 : ℝ) 1 ×ˢ U)) :
    ContinuousOn (fun p : ℝ × E n => fderiv ℝ (fun y => f (p.1, y)) p.2)
        (Icc (0 : ℝ) 1 ×ˢ U) ∧
    ContinuousOn (fun p : ℝ × E n => realHessian (fun y => f (p.1, y)) p.2)
        (Icc (0 : ℝ) 1 ×ˢ U) := by
  let S := Icc (0 : ℝ) 1 ×ˢ U
  have hUnique : UniqueDiffOn ℝ S := uniqueDiffOn_Icc_zero_one.prod hU.uniqueDiffOn
  have hG := hf.fderivWithin (m := 1) hUnique (by norm_num)
  have hB := (hG.fderivWithin (m := 0) hUnique (by norm_num)).continuousOn
  constructor
  · apply (hG.continuousOn.clm_comp (continuousOn_const
      (c := ContinuousLinearMap.inr ℝ ℝ (E n)))).congr
    intro p hp
    exact fderiv_dirichlet_parameter_slice hU (hf.of_le (by norm_num)) hp.1 hp.2
  · apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro z
    apply ((hB.clm_apply (continuousOn_const (c := ((0 : ℝ), v)))).clm_apply
      (continuousOn_const (c := ((0 : ℝ), z)))).congr
    intro p hp
    exact realHessian_dirichlet_parameter_slice hU hf hp.1 hp.2 v z

end KEBall
