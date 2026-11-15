import KEBall.DirichletRotationHessianHolder
import KEBall.DirichletNormalHolderRecovery
import KEBall.DirichletCoreAnnulusHolder

/-! A two-point Holder bound for the same actual Hessian on the closed ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff NNReal

namespace KEBall

theorem exists_dirichlet_closedBall_holder_realHessian {n : ℕ} (hn : 0 < n)
    {w f : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hw2 : ContDiffOn ℝ 2 w (closedUnitBall n))
    (hw3 : ContDiffOn ℝ 3 w (unitBall n))
    (hf : ContDiffOn ℝ 1 f (closedUnitBall n))
    (hDclosed : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    (hw0 : ∀ x ∈ unitSphere n, w x = 0)
    (hDecay : HasDirichletHessianOscillationDecay G)
    (hPower : HasDirichletRotationBoundaryPower G)
    (hPos : ∀ x ∈ closedUnitBall n, (complexHessianOfRealBilinear
      (fderivWithin ℝ (fderivWithin ℝ w (closedUnitBall n)) (closedUnitBall n) x)).PosDef)
    (hDet : ∀ x ∈ closedUnitBall n, (complexHessianOfRealBilinear
      (fderivWithin ℝ (fderivWithin ℝ w (closedUnitBall n)) (closedUnitBall n) x)).det.re = f x) :
    ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧ HasDirichletHolderOn α
      (fderivWithin ℝ (fderivWithin ℝ w (closedUnitBall n)) (closedUnitBall n))
      (closedUnitBall n) := by
  let S := closedUnitBall n
  let B := fderivWithin ℝ (fderivWithin ℝ w S) S
  let A := S ∩ {x : E n | 1 / 2 ≤ ‖x‖}
  let C := closedBall (0 : E n) (3 / 4 : ℝ)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hU : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
    ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hBC : ContinuousOn B S :=
    ((hw2.fderivWithin (m := 1) hU (by norm_num)).fderivWithin
      (m := 0) hU (by norm_num)).continuousOn
  obtain ⟨α, hα, hα1, hRot⟩ := exists_dirichlet_closedBall_holder_unitary_hessian
    hn hw2 hDclosed hD hLip hw0 hDecay hPower
  have hId : HasDirichletHolderOn α (fun x : E n => x) S :=
    hasDirichletHolderOn_of_contDiffOn hS (convex_closedBall _ _) contDiffOn_id hα1.le
  have hfH : HasDirichletHolderOn α f S :=
    hasDirichletHolderOn_of_contDiffOn hS (convex_closedBall _ _) hf hα1.le
  have hA : IsCompact A := hS.inter_right (isClosed_le continuous_const continuous_norm)
  have hAway (x : E n) (hx : x ∈ A) : x ≠ 0 := by
    intro he
    have h := hx.2
    change 1 / 2 ≤ ‖x‖ at h
    rw [he, norm_zero] at h
    norm_num at h
  have hSym (x : E n) (hx : x ∈ A) (a b : E n) : B x a b = B x b a := by
    have hClosure : x ∈ closure (interior S) := by
      rw [show interior S = unitBall n from interior_closedBall _ (by norm_num),
        unitBall, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
      exact hx.1
    exact ((hw2 x hx.1).isSymmSndFDerivWithinAt (by norm_num) hU hClosure hx.1).eq a b
  have hTan : HasDirichletHolderOn α
      (fun x => (B x).comp (ContinuousLinearMap.id ℝ (E n) -
        (‖x‖ ^ 2)⁻¹ • (innerSL ℝ x).smulRight x)) A := by
    apply hasDirichletHolderOn_tangentHessian_of_unitaryRotations hA hα
      (hId.mono inter_subset_left) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) hAway
    · intro i j
      exact (hRot _ (dirichletUnitaryRotation_star _ _) (dirichletUnitaryRotation_J _ _)).mono
        inter_subset_left
    · simpa only [JCLM_apply] using
        (hRot (JCLM n) (JCLM_star n) (fun x => by simp only [JCLM_apply])).mono
          (show A ⊆ S from inter_subset_left)
  have hAnn : HasDirichletHolderOn α B A :=
    hasDirichletHolderOn_realHessian_of_tangent_det hA hα (hId.mono inter_subset_left)
      (hBC.mono inter_subset_left) hAway hSym hTan (hfH.mono inter_subset_left)
      (fun x hx => hPos x hx.1) (fun x hx => hDet x hx.1)
  have hCSub : C ⊆ unitBall n := closedBall_subset_ball (by norm_num)
  have hHessC : ContDiffOn ℝ 1 (realHessian w) (unitBall n) :=
    (hw3.fderiv_of_isOpen (m := 2) isOpen_ball (by norm_num)).fderiv_of_isOpen
      (m := 1) isOpen_ball (by norm_num)
  have hCore : HasDirichletHolderOn α B C := by
    apply (hasDirichletHolderOn_of_contDiffOn (isCompact_closedBall _ _) (convex_closedBall _ _)
      (hHessC.mono hCSub) hα1.le).congr
    intro x hx
    exact fderivWithin_fderivWithin_eq_of_mem_nhds
      (mem_of_superset (isOpen_ball.mem_nhds (hCSub hx)) ball_subset_closedBall)
  exact ⟨α, hα, hα1, hasDirichletHolderOn_closedBall_of_core_annulus hBC hCore hAnn⟩

end KEBall
