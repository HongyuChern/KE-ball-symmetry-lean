import KEBall.DirichletRotationClosedBallHolder
import KEBall.DirichletUnitaryFieldMatrix
import KEBall.DirichletCompactHolder

/-! Identifying the Holder rotation jets with the actual within Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

theorem exists_dirichlet_closedBall_holder_unitary_hessian {n : ℕ} (hn : 0 < n)
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hw2 : ContDiffOn ℝ 2 w (closedUnitBall n))
    (hDclosed : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    (hw0 : ∀ x ∈ unitSphere n, w x = 0)
    (hDecay : HasDirichletHessianOscillationDecay G)
    (hPower : HasDirichletRotationBoundaryPower G) :
    ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧
      ∀ (R : E n →L[ℝ] E n), star R = -R → (∀ x, R (J x) = J (R x)) →
        HasDirichletHolderOn α
          (fun x => fderivWithin ℝ (fderivWithin ℝ w (closedUnitBall n))
            (closedUnitBall n) x (R x)) (closedUnitBall n) := by
  let S := closedUnitBall n
  let B := fderivWithin ℝ (fderivWithin ℝ w S) S
  have hComp : IsCompact S := isCompact_closedBall _ _
  have hUnique : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
    ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hInterior := hw2.mono (ball_subset_closedBall : unitBall n ⊆ S)
  have hFirst : ContDiffOn ℝ 1 (fderivWithin ℝ w S) S :=
    hw2.fderivWithin hUnique (by norm_num)
  have hBC : ContinuousOn B S :=
    (hFirst.fderivWithin (m := 0) hUnique (by norm_num)).continuousOn
  have hBInterior (x : E n) (hx : x ∈ unitBall n) : B x = realHessian w x :=
    fderivWithin_fderivWithin_eq_of_mem_nhds
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  have hGFirst : EqOn G (fderivWithin ℝ w S) S :=
    fun x hx => ((hDclosed x hx).fderivWithin (hUnique x hx)).symm
  obtain ⟨α, hα, hα1, hRot⟩ := exists_dirichlet_rotation_closedBall_holder_firstJet hn
    hInterior hDclosed hD hLip hw0
    (exists_dirichlet_realHessian_scaled_holder_of_oscillation hD hLip hDecay) hPower
  have hGH : HasDirichletHolderOn α G S :=
    (hasDirichletHolderOn_of_contDiffOn hComp (convex_closedBall _ _) hFirst hα1.le).congr hGFirst
  have hIdentify (T : E n →L[ℝ] E n) {Q : E n → E n →L[ℝ] ℝ}
      (hQ : HasDirichletHolderOn α Q S)
      (hQi : ∀ x ∈ unitBall n, Q x = fderiv ℝ (fun y => G y (T y)) x) :
      HasDirichletHolderOn α (fun x => B x (T x)) S := by
    have hKnown := hQ.sub (hGH.clm_comp (HasDirichletHolderOn.const T) hComp hα) hComp hα
    apply hKnown.congr
    apply EqOn.of_subset_closure (s := unitBall n)
    · intro x hx
      change B x (T x) = Q x - (G x).comp T
      rw [hBInterior x hx, hQi x hx]
      ext v
      simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply]
      rw [fderiv_dirichlet_firstJet_linearField
        (differentiableAt_dirichlet_firstJet_of_interiorC2 hInterior hD hx),
        fderiv_dirichlet_firstJet_eq_realHessian hD hx, add_sub_cancel_right]
      exact ((hInterior.contDiffAt (isOpen_ball.mem_nhds hx)).isSymmSndFDerivAt
        (by norm_num)).eq (T x) v
    · exact hBC.clm_apply T.continuous.continuousOn
    · exact hKnown.continuousOn hα
    · exact ball_subset_closedBall
    · rw [unitBall, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
      exact Subset.rfl
  refine ⟨α, hα, hα1, ?_⟩
  intro R hR hRJ
  let c : ℝ := (1 + ‖R‖)⁻¹
  let T := c • R
  have hc : 0 < c := inv_pos.mpr (by positivity)
  have hTStar : star T = -T := by
    simp only [T, star_smul, star_trivial, hR, smul_neg]
  have hTJ (x : E n) : T (J x) = J (T x) := by
    change c • R (J x) = J (c • R x)
    rw [hRJ]
    simp only [← JCLM_apply, map_smul]
  obtain ⟨M, hTM, hM⟩ := exists_dirichlet_skewHermitian_matrix_of_field T hTStar hTJ
  have hNorm : ‖T‖ ≤ 3 := by
    have hp : c * ‖R‖ ≤ 1 := by
      dsimp [c]
      rw [inv_mul_eq_div, div_le_iff₀ (by positivity : 0 < 1 + ‖R‖)]
      linarith
    rw [show T = c • R from rfl, norm_smul, Real.norm_of_nonneg hc.le]
    linarith
  obtain ⟨Q, K, hQ, hQi, _, _⟩ := hRot T hTJ M hTM hM
    (fun x _ => inner_dirichlet_skew_field_self T hTStar x) hNorm
  have hTH := hIdentify T ⟨K, hQ⟩ hQi
  have hScaled := (HasDirichletHolderOn.const c⁻¹).smul hTH hComp hα
  apply hScaled.congr
  intro x hx
  change B x (R x) = c⁻¹ • B x (c • R x)
  rw [map_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

end KEBall
