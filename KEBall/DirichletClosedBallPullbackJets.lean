import KEBall.DirichletNormalRecovery
import KEBall.DirichletClosedTaylorGlue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Pulling actual closed-ball jets back to an open set

The outer function is only C2 on the closed ball.  Its first and second
within derivatives are used in the chain rule; a smooth extension across
the sphere is not assumed.  The sphere identity supplies the cancellation
needed when correcting the boundary values of inward dilations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem fderiv_dirichlet_comp_closedBall {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E n → F} (hu : ContDiffOn ℝ 1 u (closedUnitBall n))
    {U : Set (E n)} (hU : IsOpen U) {φ : E n → E n}
    (hφ : ContDiffOn ℝ 1 φ U) (hMaps : MapsTo φ U (closedUnitBall n))
    {x : E n} (hx : x ∈ U) :
    fderiv ℝ (u ∘ φ) x =
      (fderivWithin ℝ u (closedUnitBall n) (φ x)).comp (fderiv ℝ φ x) := by
  have huD := (hu.differentiableOn (by norm_num) (φ x) (hMaps hx)).hasFDerivWithinAt
  have hφD := ((hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  exact (huD.comp_hasFDerivAt x hφD (by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hMaps hy)).fderiv

theorem realHessian_dirichlet_comp_closedBall {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {U : Set (E n)} (hU : IsOpen U) {φ : E n → E n}
    (hφ : ContDiffOn ℝ 2 φ U) (hMaps : MapsTo φ U (closedUnitBall n))
    {x : E n} (hx : x ∈ U) (v z : E n) :
    realHessian (u ∘ φ) x v z =
      fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n)
        (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x z) +
      fderivWithin ℝ u (closedUnitBall n) (φ x) (fderiv ℝ (fderiv ℝ φ) x v z) := by
  let S := closedUnitBall n
  let G := fderivWithin ℝ u S
  have hUnique : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
    ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hG : ContDiffOn ℝ 1 G S := hu.fderivWithin hUnique (by norm_num)
  have hφ1 : ContDiffOn ℝ 1 φ U := hφ.of_le (by norm_num)
  have hφD := ((hφ1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hGD := (hG.differentiableOn (by norm_num) (φ x) (hMaps hx)).hasFDerivWithinAt
  have hComp := hGD.comp_hasFDerivAt x hφD (by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hMaps hy)
  have hSecond := (((hφ.fderiv_of_isOpen (m := 1) hU (by norm_num)).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hProduct := hComp.clm_comp hSecond
  have he : fderiv ℝ (u ∘ φ) =ᶠ[𝓝 x] (fun y => (G (φ y)).comp (fderiv ℝ φ y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_dirichlet_comp_closedBall (hu.of_le (by norm_num)) hU hφ1 hMaps hy
  rw [realHessian, he.fderiv_eq,
    show fderiv ℝ (fun y => (G (φ y)).comp (fderiv ℝ φ y)) x = _ from hProduct.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, Function.comp_apply]
  exact add_comm _ _

theorem dirichlet_closedBall_secondJet_sphere_pullback_zero {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    {U : Set (E n)} (hU : IsOpen U) {φ : E n → E n}
    (hφ : ContDiffOn ℝ 2 φ U) (hMaps : MapsTo φ U (unitSphere n))
    {x : E n} (hx : x ∈ U) (v z : E n) :
    fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n)
        (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x z) +
      fderivWithin ℝ u (closedUnitBall n) (φ x) (fderiv ℝ (fderiv ℝ φ) x v z) = 0 := by
  have he : (u ∘ φ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hu0 (φ y) (hMaps hy)
  rw [← realHessian_dirichlet_comp_closedBall hu hU hφ
    (fun y hy => sphere_subset_closedBall (hMaps hy)) hx v z]
  rw [realHessian, he.fderiv.fderiv_eq]
  simp only [fderiv_fun_const, fderiv_zero, Pi.zero_apply, _root_.zero_apply]

theorem smoothNear_dirichlet_inward_dilation {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    SmoothNear (closedUnitBall n) (fun x => u (r • x)) := by
  refine ⟨ball (0 : E n) r⁻¹, isOpen_ball, ?_, ?_⟩
  · apply closedBall_subset_ball
    exact (one_lt_inv₀ hr).mpr hr1
  · change ContDiffOn ℝ ∞ (u ∘ (fun x : E n => r • x)) (ball (0 : E n) r⁻¹)
    apply hu.comp (contDiffOn_id.const_smul r)
    intro x hx
    apply mem_ball_zero_iff.mpr
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    have h := mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hx) hr
    simpa only [id_eq, mul_inv_cancel₀ hr.ne'] using h

end KEBall
