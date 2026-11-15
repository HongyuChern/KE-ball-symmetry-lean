import KEBall.DirichletHessianSquare
import KEBall.DirichletQuadraticAbsorption
import KEBall.MoserTrudingerGibbsProjectedSource
import KEBall.DirichletCompactness

/-! A quadratic maximum estimate for the full actual real Hessian of a
Gibbs output.  The previous Hessian occurs linearly and is absorbed by
the positive square of the output Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

open Filter InnerProductSpace Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall.MoserTrudinger

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem gibbs_directional_hessian_square_source
    {n : ℕ} (hn : 0 < n) {γ F G c C : ℝ}
    (hγ : 0 ≤ γ) (hF : 0 ≤ F) (hG : 0 ≤ G) (hc : 0 ≤ c) (hC : 0 ≤ C)
    {u q : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = gibbsDensity γ q x)
    (hDensity : ∀ x ∈ unitBall n, gibbsDensity γ q x ≤ F)
    (hEll : ∀ x ∈ unitBall n, ∀ z : E n,
      c * ‖z‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x z) z)
    (huG : ∀ x ∈ unitBall n, ‖fderiv ℝ u x‖ ≤ G)
    (hqG : ∀ x ∈ unitBall n, ‖fderiv ℝ q x‖ ≤ G)
    (hPrev : ∀ x ∈ unitBall n, ∀ v : E n, ‖v‖ = 1 → realHessian q x v v ≤ C)
    {v : E n} (hv : ‖v‖ = 1) {x : E n} (hx : x ∈ unitBall n) :
    2 * c * (realHessian u x v v) ^ 2 - (γ * F) * (C + 2 * G ^ 2) ≤
      dirichletBilinearContraction e[n] (dirichletCofactorOperator u x)
        (realHessian (fun y => realHessian u y v v + (fderiv ℝ u y v) ^ 2) x) := by
  let H : E n → ℝ := fun y => realHessian u y v v
  let p : E n → ℝ := fun y => fderiv ℝ u y v
  let A := dirichletCofactorOperator u x
  let L := dirichletHessianContractionLinearMap e[n] A
  have hp : ContDiff ℝ ∞ p := (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hH : ContDiff ℝ ∞ H :=
    (((hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).clm_apply contDiff_const
  have huN : SmoothNear (closedUnitBall n) u := ⟨univ, isOpen_univ, subset_univ _, hu.contDiffOn⟩
  have hfN : SmoothNear (closedUnitBall n) (gibbsDensity γ q) :=
    ⟨univ, isOpen_univ, subset_univ _, (((contDiff_const.mul hq).exp).div_const _).contDiffOn⟩
  have hρ : 0 < gibbsDensity γ q x := (hEq x hx) ▸ posDef_det_re_pos (huP x hx)
  have hLH : -(γ * F * C) ≤ L (realHessian H x) := by
    have hSource := complexLaplacian_realHessian_self_ge_logDensity huN hfN huP hEq hx v
    rw [realHessian_log_gibbsDensity hn γ hq] at hSource
    simp only [_root_.smul_apply, smul_eq_mul] at hSource
    have hMul := mul_le_mul_of_nonneg_left hSource hρ.le
    have hPrev' := mul_le_mul_of_nonneg_left (hPrev x hx v hv) (mul_nonneg hγ hρ.le)
    have hDen := mul_le_mul_of_nonneg_right (hDensity x hx) (mul_nonneg hγ hC)
    change _ ≤ dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian H x)
    rw [← dirichletCofactorOfMatrix_complexHessian,
      dirichletBilinearContraction_cofactor_eq u H
        (hH.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      cofactorContraction_eq_det_mul_complexLaplacian (huP x hx), hEq x hx]
    dsimp only [H]
    nlinarith only [hMul, hPrev', hDen]
  have hLp : L (realHessian p x) = gibbsDensity γ q x * ((-γ) * fderiv ℝ q x v) := by
    change dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian p x) = _
    rw [← dirichletCofactorOfMatrix_complexHessian,
      dirichletBilinearContraction_cofactor_eq u p
        (hp.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      cofactorContraction_eq_det_mul_complexLaplacian (huP x hx), hEq x hx,
      complexLaplacian_directionalDerivative_eq_logDensity huN hfN huP hEq hx v,
      fderiv_log_gibbsDensity hn γ hq]
    rfl
  have hAbsU : |p x| ≤ G := by
    have h := (fderiv ℝ u x).le_opNorm v
    rw [hv, mul_one, Real.norm_eq_abs] at h
    exact h.trans (huG x hx)
  have hAbsQ : |fderiv ℝ q x v| ≤ G := by
    have h := (fderiv ℝ q x).le_opNorm v
    rw [hv, mul_one, Real.norm_eq_abs] at h
    exact h.trans (hqG x hx)
  have hCross : p x * fderiv ℝ q x v ≤ G ^ 2 := by
    calc
      _ ≤ |p x * fderiv ℝ q x v| := le_abs_self _
      _ = |p x| * |fderiv ℝ q x v| := abs_mul _ _
      _ ≤ G * G := mul_le_mul hAbsU hAbsQ (abs_nonneg _) hG
      _ = G ^ 2 := (pow_two G).symm
  have hCrossρ := mul_le_mul_of_nonneg_left hCross (mul_nonneg hγ hρ.le)
  have hDen := mul_le_mul_of_nonneg_right (hDensity x hx) (mul_nonneg hγ (sq_nonneg G))
  have hLP : -(2 * γ * F * G ^ 2) ≤ 2 * p x * L (realHessian p x) := by
    rw [hLp]
    nlinarith only [hCrossρ, hDen]
  have hSquare := dirichletBilinearContraction_dualSquare_ge e[n] hc (hEll x hx)
    (fderiv ℝ p x) hv
  have hDP : fderiv ℝ p x v = realHessian u x v v := fderiv_firstDerivative_apply hu.contDiffAt v v
  rw [hDP] at hSquare
  have hW : realHessian (fun y => H y + (p y) ^ 2) x =
      realHessian H x + realHessian (fun y => p y * p y) x := by
    simp only [pow_two]
    exact dirichlet_realHessian_add_C2
      (hH.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      ((hp.mul hp).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change _ ≤ L (realHessian (fun y => H y + (p y) ^ 2) x)
  rw [hW, map_add]
  have hLS := dirichletBilinearContraction_square e[n] A hp x
  change L (realHessian (fun y => p y * p y) x) =
    2 * p x * L (realHessian p x) +
      2 * dirichletBilinearContraction e[n] A ((fderiv ℝ p x).smulRight (fderiv ℝ p x)) at hLS
  rw [hLS]
  nlinarith only [hLH, hLP, hSquare]

theorem gibbs_realHessian_upper_of_absorption
    {n : ℕ} (hn : 0 < n) {γ F G c C BC : ℝ}
    (hγ : 0 ≤ γ) (hF : 0 ≤ F) (hG : 0 ≤ G) (hc : 0 < c) (hC : 0 < C)
    (hCS : 2 * G ^ 2 ≤ C) (hTC : 4 * (γ * F) < c * C) (hBC : BC + G ^ 2 ≤ C)
    {u q : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = gibbsDensity γ q x)
    (hDensity : ∀ x ∈ unitBall n, gibbsDensity γ q x ≤ F)
    (hEll : ∀ x ∈ unitBall n, ∀ z : E n,
      c * ‖z‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x z) z)
    (huG : ∀ x ∈ closedUnitBall n, ‖fderiv ℝ u x‖ ≤ G)
    (hqG : ∀ x ∈ unitBall n, ‖fderiv ℝ q x‖ ≤ G)
    (hPrev : ∀ x ∈ unitBall n, ∀ v : E n, ‖v‖ = 1 → realHessian q x v v ≤ C)
    (hBoundary : ∀ x ∈ unitSphere n, ∀ v : E n, ‖v‖ = 1 → realHessian u x v v ≤ BC) :
    ∀ x ∈ closedUnitBall n, ∀ v : E n, ‖v‖ = 1 → realHessian u x v v ≤ C := by
  have hA (x : E n) (hx : x ∈ unitBall n) : (dirichletCofactorOperator u x).IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff _).mpr
    refine ⟨?_, fun z => (mul_nonneg hc.le (sq_nonneg _)).trans (hEll x hx z)⟩
    intro v w
    rw [← dirichletCofactorOfMatrix_complexHessian]
    exact (dirichletCofactorOfMatrix_symmetric (huP x hx).isHermitian v w).trans (real_inner_comm _ _)
  intro x hx v hv
  let H : E n → ℝ := fun y => realHessian u y v v
  let p : E n → ℝ := fun y => fderiv ℝ u y v
  have hp : ContDiff ℝ ∞ p := (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hH : ContDiff ℝ ∞ H :=
    (((hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).clm_apply contDiff_const
  have hW : SmoothNear (closedUnitBall n) (fun y => H y + (p y) ^ 2) :=
    ⟨univ, isOpen_univ, subset_univ _, (hH.add (hp.pow 2)).contDiffOn⟩
  apply dirichlet_quadratic_absorption e[n] hA hW hc (mul_nonneg hγ hF)
    (sq_nonneg G) hC hCS hTC hBC _ _ _ x hx
  · intro y hy
    have h := (fderiv ℝ u y).le_opNorm v
    rw [hv, mul_one, Real.norm_eq_abs] at h
    have hAbs := h.trans (huG y hy)
    have hPN : 0 ≤ |p y| := abs_nonneg _
    nlinarith [sq_abs (p y)]
  · intro y hy
    exact hBoundary y hy v hv
  · intro y hy
    exact gibbs_directional_hessian_square_source hn hγ hF hG hc.le hC.le hu hq huP hEq
      hDensity hEll (fun z hz => huG z (ball_subset_closedBall hz)) hqG hPrev hv hy

end KEBall.MoserTrudinger
