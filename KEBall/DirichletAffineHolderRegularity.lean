import KEBall.DirichletSchauderDifferenceLimit

/-!
# Recovering C1 Holder regularity from an affine normalization

Both the spatial scale and the scale of the dependent variable are
inverted explicitly.  This retains the derivative Holder estimate for
the next nonlinear regularity step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped NNReal Topology

namespace KEBall

theorem dirichlet_affine_inverse_maps_ball {n : ℕ} (p : E n) {r R : ℝ} (hr : 0 < r) :
    MapsTo (fun x : E n => r⁻¹ • (x - p)) (ball p (r * R)) (ball 0 R) := by
  intro x hx
  rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr.le,
    inv_mul_eq_div]
  apply (div_lt_iff₀ hr).mpr
  simpa only [mem_ball, dist_eq_norm, mul_comm] using hx

theorem lipschitzWith_dirichlet_affine_inverse {n : ℕ} (p : E n) (r : ℝ) :
    LipschitzWith ‖r⁻¹‖₊ (fun x : E n => r⁻¹ • (x - p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, coe_nnnorm]
  exact le_rfl

theorem dirichlet_C1_holder_of_affine_normalization {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E n → F) (p : E n) {r c R : ℝ} (hr : 0 < r) (hc : c ≠ 0)
    {K α : ℝ≥0}
    (hg : ContDiffOn ℝ 1 (fun x => c • f (p + r • x)) (ball (0 : E n) R))
    (hDg : HolderOnWith K α (fderiv ℝ (fun x => c • f (p + r • x))) (ball (0 : E n) R)) :
    ContDiffOn ℝ 1 f (ball p (r * R)) ∧
      HolderOnWith (‖c⁻¹ * r⁻¹‖₊ * (K * ‖r⁻¹‖₊ ^ (α : ℝ))) α
        (fderiv ℝ f) (ball p (r * R)) := by
  let g (x : E n) := c • f (p + r • x)
  let ψ (x : E n) := r⁻¹ • (x - p)
  have hψMap : MapsTo ψ (ball p (r * R)) (ball 0 R) :=
    dirichlet_affine_inverse_maps_ball p hr
  have hFun : (fun x => c⁻¹ • g (ψ x)) = f := by
    funext x
    simp only [g, ψ, smul_smul, mul_inv_cancel₀ hr.ne', inv_mul_cancel₀ hc,
      one_smul, ← add_sub_assoc, add_sub_cancel_left]
  have hψD (x : E n) : HasFDerivAt ψ (r⁻¹ • ContinuousLinearMap.id ℝ (E n)) x := by
    simpa only [Pi.smul_apply, Pi.sub_apply, id_eq] using!
      ((hasFDerivAt_id x).sub_const p).const_smul r⁻¹
  have hEq (x : E n) (hx : x ∈ ball p (r * R)) :
      fderiv ℝ f x = (c⁻¹ * r⁻¹) • fderiv ℝ g (ψ x) := by
    have hd := (((hg.contDiffAt (isOpen_ball.mem_nhds (hψMap hx))).differentiableAt
      (by norm_num)).hasFDerivAt.comp x (hψD x)).const_smul c⁻¹
    have hJet : c⁻¹ • (fderiv ℝ g (ψ x)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (E n)) =
        (c⁻¹ * r⁻¹) • fderiv ℝ g (ψ x) := by
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        smul_apply, map_smul, smul_smul]
    change HasFDerivAt (fun x => c⁻¹ • g (ψ x)) _ x at hd
    rw [hFun, hJet] at hd
    exact hd.fderiv
  have hPre : HolderOnWith (K * ‖r⁻¹‖₊ ^ (α : ℝ)) α (fun x => fderiv ℝ g (ψ x))
      (ball p (r * R)) := by
    simpa only [mul_one, Function.comp_def] using!
      hDg.comp ((lipschitzWith_dirichlet_affine_inverse p r).holderWith.holderOnWith _) hψMap
  have hPost := (lipschitzWith_smul (c⁻¹ * r⁻¹) (β := E n →L[ℝ] F)).holderWith.comp_holderOnWith hPre
  refine ⟨?_, ?_⟩
  · rw [← hFun]
    apply ContDiffOn.const_smul
    exact hg.comp (by fun_prop) hψMap
  · intro x hx y hy
    rw [hEq x hx, hEq y hy]
    simpa only [Function.comp_def, NNReal.coe_one, NNReal.rpow_one, one_mul] using! hPost x hx y hy

end KEBall
