import KEBall.DirichletRotationQuotientBound
import KEBall.DirichletHessianScaledHolder

/-!
# Derivative modulus of rotations of an actual first jet

Both terms in differentiating G(x)(T x) are retained.  This is used with
the classical interior Hessian of the same path limit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped NNReal

namespace KEBall

theorem fderiv_dirichlet_firstJet_linearField {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {x : E n} (hG : DifferentiableAt ℝ G x)
    (T : E n →L[ℝ] E n) (v : E n) :
    fderiv ℝ (fun y => G y (T y)) x v =
      fderiv ℝ G x v (T x) + G x (T v) := by
  have h := hG.hasFDerivAt.clm_apply (T.hasFDerivAt (x := x))
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_comm]

theorem norm_fderiv_dirichlet_firstJet_linearField_sub_le {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    (T : E n →L[ℝ] E n) {x y : E n} (hx : x ∈ unitBall n) (hy : y ∈ unitBall n)
    (hDx : DifferentiableAt ℝ G x) (hDy : DifferentiableAt ℝ G y) :
    ‖fderiv ℝ (fun z => G z (T z)) x - fderiv ℝ (fun z => G z (T z)) y‖ ≤
      ‖T‖ * (‖fderiv ℝ G x - fderiv ℝ G y‖ + 2 * (L : ℝ) * ‖x - y‖) := by
  have he : fderiv ℝ (fun z => G z (T z)) x - fderiv ℝ (fun z => G z (T z)) y =
      (fderiv ℝ G x - fderiv ℝ G y).flip (T x) +
        (fderiv ℝ G y).flip (T (x - y)) + (G x - G y).comp T := by
    ext v
    simp only [_root_.sub_apply, fderiv_dirichlet_firstJet_linearField hDx,
      fderiv_dirichlet_firstJet_linearField hDy, _root_.add_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, map_sub]
    ring
  have hPartial (D : E n →L[ℝ] E n →L[ℝ] ℝ) (v : E n) : ‖D.flip v‖ ≤ ‖D‖ * ‖v‖ := by
    simpa only [ContinuousLinearMap.opNorm_flip] using D.flip.le_opNorm v
  have hTx : ‖T x‖ ≤ ‖T‖ := (T.le_opNorm x).trans
    (mul_le_of_le_one_right (norm_nonneg T) (mem_ball_zero_iff.mp hx).le)
  have hDNorm : ‖fderiv ℝ G y‖ ≤ L := norm_fderiv_le_of_lipschitzOn ℝ
    (mem_of_superset (isOpen_ball.mem_nhds hy) ball_subset_closedBall) hLip
  have hGdiff : ‖G x - G y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using
      hLip.dist_le_mul x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
  calc
    _ ≤ ‖(fderiv ℝ G x - fderiv ℝ G y).flip (T x)‖ +
        ‖(fderiv ℝ G y).flip (T (x - y))‖ + ‖(G x - G y).comp T‖ := by
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖fderiv ℝ G x - fderiv ℝ G y‖ * ‖T x‖ +
        ‖fderiv ℝ G y‖ * ‖T (x - y)‖ + ‖G x - G y‖ * ‖T‖ :=
      add_le_add (add_le_add (hPartial _ _) (hPartial _ _))
        ((G x - G y).opNorm_comp_le T)
    _ ≤ ‖fderiv ℝ G x - fderiv ℝ G y‖ * ‖T‖ +
        (L : ℝ) * (‖T‖ * ‖x - y‖) + ((L : ℝ) * ‖x - y‖) * ‖T‖ := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left hTx (norm_nonneg _)
        · exact mul_le_mul hDNorm (T.le_opNorm _) (norm_nonneg _) L.coe_nonneg
      · exact mul_le_mul_of_nonneg_right hGdiff (norm_nonneg T)
    _ = _ := by ring

theorem dirichlet_firstJet_linearField_derivative_holder {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    {s : Set (E n)} (hSub : s ⊆ unitBall n)
    (hG : ∀ x ∈ s, DifferentiableAt ℝ G x)
    {K β : ℝ} (hβ1 : β ≤ 1)
    (hHolder : ∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ K * ‖x - y‖ ^ β)
    (hDiam : ∀ x ∈ s, ∀ y ∈ s, ‖x - y‖ ≤ 1)
    (T : E n →L[ℝ] E n) :
    ∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ (fun z => G z (T z)) x - fderiv ℝ (fun z => G z (T z)) y‖ ≤
        (‖T‖ * (K + 2 * (L : ℝ))) * ‖x - y‖ ^ β := by
  intro x hx y hy
  apply (norm_fderiv_dirichlet_firstJet_linearField_sub_le hLip T
    (hSub hx) (hSub hy) (hG x hx) (hG y hy)).trans
  have hPow := Real.self_le_rpow_of_le_one (norm_nonneg (x - y)) (hDiam x hx y hy) hβ1
  calc
    ‖T‖ * (‖fderiv ℝ G x - fderiv ℝ G y‖ + 2 * (L : ℝ) * ‖x - y‖) ≤
        ‖T‖ * (K * ‖x - y‖ ^ β + 2 * (L : ℝ) * ‖x - y‖ ^ β) :=
      mul_le_mul_of_nonneg_left (add_le_add (hHolder x hx y hy)
        (mul_le_mul_of_nonneg_left hPow (by positivity))) (norm_nonneg T)
    _ = _ := by ring

end KEBall
