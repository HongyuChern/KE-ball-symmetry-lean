import KEBall.DirichletProjectedHessian
import KEBall.DirichletInteriorHessian
import KEBall.DirichletSmoothSupersolution
import KEBall.MoserTrudingerGibbsLogTrace

/-! The paired second-derivative source for the actual Gibbs equation.
The right-hand side uses the projected Hessian of the preceding potential. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall.MoserTrudinger

theorem realHessian_log_gibbsDensity {n : ℕ} (hn : 0 < n) (γ : ℝ)
    {q : E n → ℝ} (hq : ContDiff ℝ ∞ q) (x : E n) :
    realHessian (fun y => Real.log (gibbsDensity γ q y)) x = (-γ) • realHessian q x := by
  have he : (fun y => Real.log (gibbsDensity γ q y)) =
      (-γ) • q - (fun _ => Real.log (normalizingIntegral γ q)) :=
    funext fun y => log_gibbsDensity_eq hn γ hq.continuous.continuousOn y
  have hq2 : ContDiffAt ℝ 2 q x :=
    hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hScaled : ContDiffAt ℝ 2 ((-γ) • q) x := by
    simpa only [Pi.smul_apply] using! hq2.const_smul (-γ)
  rw [he, dirichlet_realHessian_sub_C2 hScaled contDiffAt_const,
    dirichlet_realHessian_smul_C2 hq2]
  simp [realHessian, fderiv_fun_const]

theorem complexLaplacian_projected_self_ge_logGibbs {n : ℕ} (hn : 0 < n)
    (γ : ℝ) {u q : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = gibbsDensity γ q y)
    {x : E n} (hx : x ∈ unitBall n) (v : E n) :
    (-γ) * complexProjectedHessian q x v v ≤
      complexLaplacian u (fun y => complexProjectedHessian u y v v) x := by
  have huN : SmoothNear (closedUnitBall n) u :=
    ⟨univ, isOpen_univ, subset_univ _, hu.contDiffOn⟩
  have hfN : SmoothNear (closedUnitBall n) (gibbsDensity γ q) :=
    ⟨univ, isOpen_univ, subset_univ _, (((contDiff_const.mul hq).exp).div_const _).contDiffOn⟩
  have hv := complexLaplacian_realHessian_self_ge_logDensity huN hfN huP hEq hx v
  have hJv := complexLaplacian_realHessian_self_ge_logDensity huN hfN huP hEq hx (J v)
  rw [realHessian_log_gibbsDensity hn γ hq] at hv hJv
  simp only [_root_.smul_apply, smul_eq_mul] at hv hJv
  have hH (a : E n) : ContDiffAt ℝ ∞ (fun y => realHessian u y a a) x :=
    ((realHessian_contDiffAt hu.contDiffAt).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have he : (fun y => complexProjectedHessian u y v v) =
      (fun y => (1 / 2 : ℝ) *
        (realHessian u y v v - (-1 : ℝ) * realHessian u y (J v) (J v))) := by
    funext y
    rw [complexProjectedHessian_eq_average hu.contDiffAt]
    ring
  rw [he, complexLaplacian_const_mul_at u
      ((hH v).sub (contDiffAt_const.mul (hH (J v)))),
    complexLaplacian_sub_at u (hH v) (contDiffAt_const.mul (hH (J v))),
    complexLaplacian_const_mul_at u (hH (J v)),
    complexProjectedHessian_eq_average hq.contDiffAt]
  linarith only [hv, hJv]

theorem gibbs_projected_defect_cofactor_source_bound {n : ℕ} (hn : 0 < n)
    {γ F D : ℝ} (hγ : 0 ≤ γ) (hF : 0 ≤ F) (hD : 0 ≤ D)
    {u q : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hqP : ∀ y ∈ unitBall n, (complexHessian q y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = gibbsDensity γ q y)
    (hDensity : ∀ y ∈ unitBall n, gibbsDensity γ q y ≤ F)
    (hTrace : ∀ y ∈ unitBall n, (complexHessian q y).trace.re ≤ D)
    (M : ℝ) (v : E n) {x : E n} (hx : x ∈ unitBall n) :
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletCofactorOperator u x)
      (realHessian (fun y => M - complexProjectedHessian u y v v) x) ≤
        (2 * γ * F * D) * ‖v‖ ^ 2 := by
  let p : E n → ℝ := fun y => complexProjectedHessian u y v v
  have hp : ContDiff ℝ ∞ p :=
    ((complexProjectedHessian_contDiff hu).clm_apply contDiff_const).clm_apply contDiff_const
  have hd : 0 < (complexHessian u x).det.re := posDef_det_re_pos (huP x hx)
  have hp2 : ContDiffAt ℝ 2 (fun y => M - p y) x :=
    (contDiff_const.sub hp).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [← dirichletCofactorOfMatrix_complexHessian,
    dirichletBilinearContraction_cofactor_eq u _ hp2,
    cofactorContraction_eq_det_mul_complexLaplacian (huP x hx),
    complexLaplacian_sub_at u contDiffAt_const hp.contDiffAt,
    complexLaplacian_const]
  have hSource := complexLaplacian_projected_self_ge_logGibbs hn γ hu hq huP hEq hx v
  have hP := complexProjectedHessian_self_bounds_of_trace (hqP x hx) (hTrace x hx) v
  have hProd := mul_le_mul_of_nonneg_left hSource hd.le
  have hUp := mul_le_mul_of_nonneg_left hP.2 (mul_nonneg hγ hd.le)
  have hDen := mul_le_mul_of_nonneg_right (hDensity x hx)
    (show 0 ≤ (2 * γ * D) * ‖v‖ ^ 2 by positivity)
  rw [← hEq x hx] at hDen
  change (complexHessian u x).det.re * (0 - complexLaplacian u p x) ≤ _
  dsimp only [p] at *
  nlinarith only [hProd, hUp, hDen]

end KEBall.MoserTrudinger
