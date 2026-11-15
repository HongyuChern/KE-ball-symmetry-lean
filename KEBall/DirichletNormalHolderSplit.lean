import KEBall.DirichletTangentHolder

/-! The normal splitting preserves Holder regularity of all known entries. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Set
open scoped ContDiff NNReal

namespace KEBall

theorem exists_dirichlet_holder_realHessian_tangent_split {n : ℕ} {S : Set (E n)}
    {α : ℝ≥0} (hComp : IsCompact S) (hα : 0 < α)
    (hId : HasDirichletHolderOn α (fun x : E n => x) S)
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hBC : ContinuousOn B S) (hAway : ∀ y ∈ S, y ≠ 0)
    (hSym : ∀ y ∈ S, ∀ a b, B y a b = B y b a)
    (hTan : HasDirichletHolderOn α
      (fun y => (B y).comp (ContinuousLinearMap.id ℝ (E n) -
        (‖y‖ ^ 2)⁻¹ • (innerSL ℝ y).smulRight y)) S) :
    ∃ (D : E n → E n →L[ℝ] E n →L[ℝ] ℝ) (t : E n → ℝ),
      HasDirichletHolderOn α D S ∧ ContinuousOn t S ∧
      ∀ y ∈ S, B y = D y + t y • (innerSL ℝ y).smulRight (innerSL ℝ y) := by
  let N (y : E n) : E n →L[ℝ] E n :=
    (‖y‖ ^ 2)⁻¹ • (innerSL ℝ y).smulRight y
  let T (y : E n) := (B y).comp (ContinuousLinearMap.id ℝ (E n) - N y)
  let D (y : E n) := T y + (T y).flip.comp (N y)
  let t (y : E n) := B y y y / (‖y‖ ^ 2) ^ 2
  let P (y : E n) := (innerSL ℝ y).smulRight (innerSL ℝ y)
  have hR : HasDirichletHolderOn α (fun y : E n => (‖y‖ ^ 2)⁻¹) S :=
    (hId.comp_smooth hComp hα (contDiff_norm_sq ℝ)).inv hComp hα
      (fun y hy => pow_ne_zero _ (norm_ne_zero_iff.mpr (hAway y hy)))
  have hN : HasDirichletHolderOn α N S := by
    have hL := hId.clm (innerSL ℝ (E := E n))
    have hP := (hL.prodMk hId).comp_smooth hComp hα
      (contDiff_fst.smulRight contDiff_snd)
    exact hR.smul hP hComp hα
  have hT : HasDirichletHolderOn α T S := hTan
  have hFlip : HasDirichletHolderOn α (fun y => (T y).flip) S :=
    hT.clm (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toContinuousLinearMap
  have hD : HasDirichletHolderOn α D S :=
    hT.add (hFlip.clm_comp hN hComp hα) hComp hα
  have htC : ContinuousOn t S := by
    exact ((hBC.clm_apply continuousOn_id).clm_apply continuousOn_id).div
      ((continuous_norm.continuousOn.pow 2).pow 2)
      (fun y hy => pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hAway y hy))))
  have hSplit (y : E n) (hy : y ∈ S) : B y = D y + t y • P y := by
    have hNorm : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hAway y hy))
    ext a b
    simp only [D, T, N, t, P, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, sub_apply, ContinuousLinearMap.id_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, smul_smul]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [hSym y hy b y]
    field_simp
    ring
  exact ⟨D, t, hD, htC, hSplit⟩

end KEBall
