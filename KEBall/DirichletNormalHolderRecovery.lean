import KEBall.DirichletNormalHolderSplit
import KEBall.DirichletHessianCofactorHolder

/-!
# Holder recovery of the normal Hessian coefficient

A constant positive rank-one shift is selected on the compact set.  The
determinant then recovers the omitted coefficient by division by a strictly
positive slope.  All Holder estimates keep the given exponent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem hasDirichletHolderOn_realHessian_of_tangent_det {n : ℕ} {S : Set (E n)}
    {α : ℝ≥0} (hComp : IsCompact S) (hα : 0 < α)
    (hId : HasDirichletHolderOn α (fun x : E n => x) S)
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {f : E n → ℝ}
    (hBC : ContinuousOn B S) (hAway : ∀ y ∈ S, y ≠ 0)
    (hSym : ∀ y ∈ S, ∀ a b, B y a b = B y b a)
    (hTan : HasDirichletHolderOn α
      (fun y => (B y).comp (ContinuousLinearMap.id ℝ (E n) -
        (‖y‖ ^ 2)⁻¹ • (innerSL ℝ y).smulRight y)) S)
    (hf : HasDirichletHolderOn α f S)
    (hPos : ∀ x ∈ S, (complexHessianOfRealBilinear (B x)).PosDef)
    (hDet : ∀ x ∈ S, (complexHessianOfRealBilinear (B x)).det.re = f x) :
    HasDirichletHolderOn α B S := by
  obtain ⟨D, t, hD, htC, hSplit⟩ := exists_dirichlet_holder_realHessian_tangent_split
    hComp hα hId hBC hAway hSym hTan
  obtain ⟨c, hc⟩ := hComp.exists_bound_of_continuousOn htC
  let P (x : E n) := (innerSL ℝ x).smulRight (innerSL ℝ x)
  let A (x : E n) := complexHessianOfRealBilinear (D x + c • P x)
  let z (x : E n) := star (complexCoord x)
  have hP : HasDirichletHolderOn α P S := by
    have hL := hId.clm (innerSL ℝ (E := E n))
    exact (hL.prodMk hL).comp_smooth hComp hα (contDiff_fst.smulRight contDiff_snd)
  have hA : HasDirichletHolderOn α A S :=
    (hD.add ((HasDirichletHolderOn.const c).smul hP hComp hα) hComp hα).comp_smooth
      hComp hα contDiff_dirichlet_complexHessianOfRealBilinear
  have hz : HasDirichletHolderOn α z S := by
    apply hId.comp_smooth hComp hα (g := fun x : E n => star (complexCoord x))
    apply contDiff_pi.mpr
    intro i
    exact Complex.conjCLE.contDiff.comp (complexCoordCLM i).contDiff
  have hz0 (x : E n) (hx : x ∈ S) : z x ≠ 0 := by
    intro he
    apply hAway x hx
    apply complexCoord_eq_zero_iff.mp
    simpa only [z, star_star, star_zero] using congrArg star he
  have hAP (x : E n) (hx : x ∈ S) : (A x).PosDef := by
    have hct : 0 ≤ c - t x := by
      have h := hc x hx
      rw [Real.norm_eq_abs] at h
      linarith [le_abs_self (t x)]
    have hshift : D x + c • P x = B x + (c - t x) • P x := by
      rw [hSplit x hx]
      dsimp only [P]
      module
    dsimp only [A]
    rw [hshift, complexHessianOfRealBilinear_add_rankOne]
    apply (hPos x hx).add_posSemidef
    simpa only [star_star] using
      ((posSemidef_vecMulVec_self_star (star (complexCoord x))).smul
        (show (0 : ℂ) ≤ ((c - t x) / 4 : ℝ) from
          Complex.zero_le_real.mpr (div_nonneg hct (by norm_num))))
  have hSlope : HasDirichletHolderOn α
      (fun x => hermitianRankOneDetSlope (A x) (z x)) S := by
    apply (hA.prodMk hz).comp_smooth hComp hα
      (g := fun q : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) =>
        hermitianRankOneDetSlope q.1 q.2)
    apply contDiffOn_univ.mp
    apply contDiffOn_hermitianRankOneDetSlope
    · intro i j
      fun_prop
    · intro i
      fun_prop
  have hADet : HasDirichletHolderOn α (fun x => (A x).det.re) S := by
    apply hA.comp_smooth hComp hα (g := fun A : Matrix (Fin n) (Fin n) ℂ => A.det.re)
    apply contDiffOn_univ.mp
    apply Complex.reCLM.contDiff.comp_contDiffOn
    apply contDiffOn_det_of_contDiffOn_entries
    intro i j
    fun_prop
  have hInv := hSlope.inv hComp hα (fun x hx =>
    (hermitianRankOneDetSlope_pos (hAP x hx) (hz0 x hx)).ne')
  have htFormula (x : E n) (hx : x ∈ S) :
      t x = 4 * ((f x - (A x).det.re) /
        hermitianRankOneDetSlope (A x) (z x)) + c := by
    have hB : complexHessianOfRealBilinear (B x) =
        A x + (((t x - c) / 4 : ℝ) : ℂ) • Matrix.vecMulVec (z x) (star (z x)) := by
      have he : B x = D x + c • P x + (t x - c) • P x := by
        rw [hSplit x hx]
        dsimp only [P]
        module
      rw [he]
      simpa only [A, P, z, star_star] using
        complexHessianOfRealBilinear_add_rankOne (D x + c • P x) x (t x - c)
    have he := real_rankOne_coefficient_eq_of_det (hAP x hx) (hz0 x hx) hB
    rw [← hermitianRankOneDetSlope_eq (hAP x hx), hDet x hx] at he
    linarith
  have ht : HasDirichletHolderOn α t S := by
    have hQuot := (hf.sub hADet hComp hα).smul hInv hComp hα
    have hAffine := hQuot.comp_smooth hComp hα
      ((contDiff_const.mul contDiff_id).add contDiff_const :
        ContDiff ℝ ∞ (fun a : ℝ => 4 * a + c))
    apply hAffine.congr
    intro x hx
    simpa only [Function.comp_apply, id_eq, smul_eq_mul, div_eq_mul_inv] using htFormula x hx
  exact (hD.add (ht.smul hP hComp hα) hComp hα).congr
    (fun x hx => hSplit x hx)

end KEBall
