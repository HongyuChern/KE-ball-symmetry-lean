import KEBall.MoserTrudingerGibbsProjectedSource

/-! The actual full directional Hessian defect, with its preceding
Gibbs potential's real Hessian source. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall.MoserTrudinger

theorem gibbs_realHessian_defect_cofactor_source_bound
    {n : ℕ} (hn : 0 < n) {γ F D : ℝ} (hγ : 0 ≤ γ) (hF : 0 ≤ F) (hD : 0 ≤ D)
    {u q : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = gibbsDensity γ q y)
    (hDensity : ∀ y ∈ unitBall n, gibbsDensity γ q y ≤ F)
    (hHess : ∀ y ∈ unitBall n, ‖realHessian q y‖ ≤ D)
    (M : ℝ) (v : E n) {x : E n} (hx : x ∈ unitBall n) :
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletCofactorOperator u x)
      (realHessian (fun y => M - realHessian u y v v) x) ≤
        (γ * F * D) * ‖v‖ ^ 2 := by
  let p : E n → ℝ := fun y => realHessian u y v v
  have hp : ContDiff ℝ ∞ p :=
    (((hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).clm_apply contDiff_const
  have huN : SmoothNear (closedUnitBall n) u := ⟨univ, isOpen_univ, subset_univ _, hu.contDiffOn⟩
  have hfN : SmoothNear (closedUnitBall n) (gibbsDensity γ q) :=
    ⟨univ, isOpen_univ, subset_univ _, (((contDiff_const.mul hq).exp).div_const _).contDiffOn⟩
  have hSource := complexLaplacian_realHessian_self_ge_logDensity huN hfN huP hEq hx v
  rw [realHessian_log_gibbsDensity hn γ hq] at hSource
  simp only [_root_.smul_apply, smul_eq_mul] at hSource
  have hd : 0 < (complexHessian u x).det.re := posDef_det_re_pos (huP x hx)
  have hNorm := ((realHessian q x v).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (((realHessian q x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hHess x hx) (norm_nonneg v))) (norm_nonneg v))
  have hPrev : realHessian q x v v ≤ D * ‖v‖ ^ 2 := by
    rw [Real.norm_eq_abs] at hNorm
    exact (le_abs_self _).trans (hNorm.trans_eq (by ring))
  have hMul := mul_le_mul_of_nonneg_left hSource hd.le
  have hUp := mul_le_mul_of_nonneg_left hPrev (mul_nonneg hγ hd.le)
  have hDen := mul_le_mul_of_nonneg_right (hDensity x hx)
    (show 0 ≤ (γ * D) * ‖v‖ ^ 2 by positivity)
  rw [← hEq x hx] at hDen
  rw [← dirichletCofactorOfMatrix_complexHessian,
    dirichletBilinearContraction_cofactor_eq u _
      ((contDiff_const.sub hp).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    cofactorContraction_eq_det_mul_complexLaplacian (huP x hx),
    complexLaplacian_sub_at u contDiffAt_const hp.contDiffAt,
    complexLaplacian_const]
  change (complexHessian u x).det.re * (0 - complexLaplacian u p x) ≤ _
  dsimp only [p]
  nlinarith only [hMul, hUp, hDen]

end KEBall.MoserTrudinger
