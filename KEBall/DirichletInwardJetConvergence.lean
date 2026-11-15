import KEBall.DirichletClosedBallPullbackJets
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Uniform convergence of inward dilations and their actual jets

At the limiting parameter the target is the within jet on the closed
ball.  The approximating ordinary derivatives are used only for parameters
strictly below one, so no values outside the closed ball are assumed regular.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem dirichlet_uniform_limit_at_one_of_continuousOn_compact {n : ℕ} {F : Type*}
    [UniformSpace F] {K : Set (E n)} (hK : IsCompact K) {f : ℝ × E n → F}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1 ×ˢ K)) :
    TendstoUniformlyOn (fun r x => f (r, x)) (fun x => f (1, x))
      (𝓝[Icc (0 : ℝ) 1] 1) K := by
  have hUC : UniformContinuousOn (Function.uncurry (fun r x => f (r, x)))
      (Icc (0 : ℝ) 1 ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hf
  exact hUC.tendstoUniformlyOn (by constructor <;> norm_num)

theorem tendstoUniformlyOn_dirichlet_weighted_dilation {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F}
    (hf : ContinuousOn f (closedUnitBall n)) (k : ℕ) :
    TendstoUniformlyOn (fun r x => r ^ k • f (r • x)) f
      (𝓝[Icc (0 : ℝ) 1] 1) (closedUnitBall n) := by
  have hMaps : MapsTo (fun p : ℝ × E n => p.1 • p.2)
      (Icc (0 : ℝ) 1 ×ˢ closedUnitBall n) (closedUnitBall n) := by
    intro p hp
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_of_nonneg hp.1.1]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hp.2) hp.1.1).trans
      (by simpa only [mul_one] using hp.1.2)
  have hC : ContinuousOn (fun p : ℝ × E n => p.1 ^ k • f (p.1 • p.2))
      (Icc (0 : ℝ) 1 ×ˢ closedUnitBall n) :=
    (continuous_fst.pow k).continuousOn.smul
      (hf.comp (continuous_fst.smul continuous_snd).continuousOn hMaps)
  have h := dirichlet_uniform_limit_at_one_of_continuousOn_compact (K := closedUnitBall n)
    (isCompact_closedBall (0 : E n) 1) hC
  simpa only [one_pow, one_smul] using h

private theorem dirichlet_inward_maps {n : ℕ} {r : ℝ} (hr : 0 < r) :
    MapsTo (fun x : E n => r • x) (ball (0 : E n) r⁻¹) (closedUnitBall n) := by
  intro x hx
  apply ball_subset_closedBall
  apply mem_ball_zero_iff.mpr
  rw [norm_smul, Real.norm_of_nonneg hr.le]
  have h := mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hx) hr
  simpa only [mul_inv_cancel₀ hr.ne'] using h

theorem fderiv_dirichlet_inward_dilation {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 1 u (closedUnitBall n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {x : E n} (hx : x ∈ closedUnitBall n) :
    fderiv ℝ (fun y => u (r • y)) x = r • fderivWithin ℝ u (closedUnitBall n) (r • x) := by
  have hxU : x ∈ ball (0 : E n) r⁻¹ :=
    closedBall_subset_ball ((one_lt_inv₀ hr).mpr hr1) hx
  have hL : fderiv ℝ (fun y : E n => r • y) x = r • ContinuousLinearMap.id ℝ (E n) :=
    ((hasFDerivAt_id x).const_smul r).fderiv
  change fderiv ℝ (u ∘ (fun y : E n => r • y)) x = _
  rw [fderiv_dirichlet_comp_closedBall (φ := fun y : E n => r • y) hu isOpen_ball
    (contDiffOn_id.const_smul r) (dirichlet_inward_maps hr) hxU, hL]
  ext v
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, map_smul]

theorem realHessian_dirichlet_inward_dilation {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {x : E n} (hx : x ∈ closedUnitBall n) :
    realHessian (fun y => u (r • y)) x =
      r ^ 2 • fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n))
        (closedUnitBall n) (r • x) := by
  have hxU : x ∈ ball (0 : E n) r⁻¹ :=
    closedBall_subset_ball ((one_lt_inv₀ hr).mpr hr1) hx
  have hL (y : E n) : fderiv ℝ (fun z : E n => r • z) y = r • ContinuousLinearMap.id ℝ (E n) :=
    ((hasFDerivAt_id y).const_smul r).fderiv
  have hSecond : fderiv ℝ (fderiv ℝ (fun y : E n => r • y)) x = 0 := by
    rw [show fderiv ℝ (fun y : E n => r • y) =
      (fun _ => r • ContinuousLinearMap.id ℝ (E n)) from funext hL, fderiv_const_apply]
  ext v z
  change realHessian (u ∘ (fun y : E n => r • y)) x v z = _
  rw [realHessian_dirichlet_comp_closedBall (φ := fun y : E n => r • y) hu isOpen_ball
    (contDiffOn_id.const_smul r) (dirichlet_inward_maps hr) hxU v z]
  simp only [hL, hSecond, _root_.smul_apply, ContinuousLinearMap.id_apply,
    _root_.zero_apply, map_zero, add_zero, map_smul, smul_eq_mul]
  ring

theorem tendstoUniformlyOn_dirichlet_inward_firstJet {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 1 u (closedUnitBall n)) :
    TendstoUniformlyOn (fun r => fderiv ℝ (fun y => u (r • y)))
      (fderivWithin ℝ u (closedUnitBall n))
      (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) := by
  have hUnique : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hC := (hu.fderivWithin (m := 0) hUnique (by norm_num)).continuousOn
  have h := tendstoUniformlyOn_dirichlet_weighted_dilation hC 1
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hεU := (Metric.tendstoUniformlyOn_iff.mp h ε hε).filter_mono
    (nhdsWithin_mono (1 : ℝ) Ioo_subset_Icc_self)
  filter_upwards [hεU, self_mem_nhdsWithin] with r hεr hr x hx
  simpa only [pow_one, fderiv_dirichlet_inward_dilation hu hr.1 hr.2 hx] using hεr x hx

theorem tendstoUniformlyOn_dirichlet_inward_secondJet {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    TendstoUniformlyOn (fun r => realHessian (fun y => u (r • y)))
      (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n))
      (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) := by
  have hUnique : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hC := ((hu.fderivWithin (m := 1) hUnique (by norm_num)).fderivWithin
    (m := 0) hUnique (by norm_num)).continuousOn
  have h := tendstoUniformlyOn_dirichlet_weighted_dilation hC 2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hεU := (Metric.tendstoUniformlyOn_iff.mp h ε hε).filter_mono
    (nhdsWithin_mono (1 : ℝ) Ioo_subset_Icc_self)
  filter_upwards [hεU, self_mem_nhdsWithin] with r hεr hr x hx
  simpa only [realHessian_dirichlet_inward_dilation hu hr.1 hr.2 hx] using hεr x hx

end KEBall
