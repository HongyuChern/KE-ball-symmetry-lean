import KEBall.DirichletCompactHolder
import KEBall.DirichletUnitaryTangents

/-! Quantitative Holder versions of the finite unitary tangent reconstruction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Set
open scoped ContDiff NNReal

namespace KEBall

theorem hasDirichletHolderOn_tangentHessian_of_unitaryRotations {n : ℕ} {S : Set (E n)}
    {α : ℝ≥0} (hComp : IsCompact S) (hα : 0 < α)
    (hId : HasDirichletHolderOn α (fun x : E n => x) S)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (hS : ∀ x ∈ S, x ≠ 0)
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hRot : ∀ i j, HasDirichletHolderOn α
      (fun x => B x (dirichletUnitaryRotation (b i) (b j) x)) S)
    (hJ : HasDirichletHolderOn α (fun x => B x (J x)) S) :
    HasDirichletHolderOn α
      (fun x => (B x).comp (ContinuousLinearMap.id ℝ (E n) -
        (‖x‖ ^ 2)⁻¹ • (innerSL ℝ x).smulRight x)) S := by
  let H (i : Fin (2 * n)) (x : E n) :=
    (∑ j, inner ℝ (b j) x • B x (dirichletUnitaryRotation (b i) (b j) x)) +
      inner ℝ (J (b i)) x • B x (J x)
  let P (x : E n) :=
    ContinuousLinearMap.id ℝ (E n) - (‖x‖ ^ 2)⁻¹ • (innerSL ℝ x).smulRight x
  have hH (i : Fin (2 * n)) : HasDirichletHolderOn α (H i) S := by
    refine (HasDirichletHolderOn.sum (fun j => ?_) hComp hα).add ?_ hComp hα
    · exact (hId.clm (innerSL ℝ (b j))).smul (hRot i j) hComp hα
    · exact (hId.clm (innerSL ℝ (J (b i)))).smul hJ hComp hα
  have hInv : HasDirichletHolderOn α (fun x : E n => (‖x‖ ^ 2)⁻¹) S :=
    (hId.comp_smooth hComp hα (contDiff_norm_sq ℝ)).inv hComp hα
      (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr (hS x hx)))
  have hForm : HasDirichletHolderOn α
      (fun x => ∑ i, (innerSL ℝ (b i)).smulRight ((‖x‖ ^ 2)⁻¹ • H i x)) S := by
    apply HasDirichletHolderOn.sum (fun i => ?_) hComp hα
    exact (hInv.smul (hH i) hComp hα).comp_smooth hComp hα
      (contDiff_const.smulRight contDiff_id)
  refine hForm.congr fun x hx => ?_
  have hNorm : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hS x hx))
  have hP (i : Fin (2 * n)) : P x (b i) =
      (‖x‖ ^ 2)⁻¹ • (‖x‖ ^ 2 • b i - inner ℝ (b i) x • x) := by
    simp only [P, sub_apply, ContinuousLinearMap.id_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_sub, smul_smul,
      inv_mul_cancel₀ hNorm, one_smul, real_inner_comm x (b i)]
  have hEval (i : Fin (2 * n)) : B x (P x (b i)) = (‖x‖ ^ 2)⁻¹ • H i x := by
    rw [hP, ← sum_dirichletUnitaryRotation_eq_tangentProjection b (b i) x]
    simp only [H, map_smul, map_add, map_sum]
  change (B x).comp (P x) = _
  ext a : 1
  calc
    ((B x).comp (P x)) a =
        ((B x).comp (P x)) (∑ i, inner ℝ (b i) a • b i) := by rw [b.sum_repr']
    _ = _ := by
      simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply, hEval,
        sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

end KEBall
