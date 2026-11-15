import KEBall.MoserTrudingerGibbsHessianAbsorption
import KEBall.MoserTrudingerGibbsBoundaryHessian
import KEBall.MoserTrudingerGibbsCofactorUniform

/-! Uniform closed-ball bounds on the full real Hessian of the actual
Gibbs inverse iteration.  No Hessian bound is assumed on the family. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000

open Metric Set
open scoped ComplexOrder ContDiff NNReal

namespace KEBall.MoserTrudinger

theorem exists_uniform_realHessian_bound_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 0 < n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ j x, x ∈ closedUnitBall n →
      ‖realHessian (u j) x‖ ≤ C := by
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration hn hγ hu hu0 huP hEq hM huB
  obtain ⟨a, b, ha, hb, hDensity⟩ := exists_power_density_bounds_of_bounded_family hn hγ
    (fun j => (hu j).continuous.continuousOn) huB
  obtain ⟨c, K, hc, _, hCoeff⟩ :=
    exists_uniform_cofactor_bounds_of_smoothGibbs_trace hn hγ hD hu huP hEq huB hTrace
  obtain ⟨Cb, hCb, hBoundary⟩ :=
    exists_uniform_boundary_hessian_bound_of_gibbs_density hn hγ ha hb
  have hH0 : Continuous (realHessian (u 0)) :=
    (((hu 0).fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hH0.continuousOn
  let BC : ℝ := Cb * (1 + G ^ 2)
  let T : ℝ := γ * b ^ n
  let C : ℝ := |C0| + BC + 2 * G ^ 2 + 4 * T / c + 1
  have hBC0 : 0 < BC := by dsimp [BC]; positivity
  have hT : 0 ≤ T := mul_nonneg hγ (pow_pos hb n).le
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0C : C0 ≤ C := by
    have h := le_abs_self C0
    have hp : 0 ≤ 4 * T / c := by positivity
    dsimp [C]
    nlinarith only [h, hBC0.le, sq_nonneg G, hp]
  have hCS : 2 * G ^ 2 ≤ C := by
    have hp : 0 ≤ 4 * T / c := by positivity
    dsimp [C]
    linarith [abs_nonneg C0, hBC0.le]
  have hTC : 4 * T < c * C := by
    have hDiv : 4 * T / c < C := by
      dsimp [C]
      nlinarith only [abs_nonneg C0, hBC0.le, sq_nonneg G]
    exact (div_lt_iff₀ hc).mp hDiv |>.trans_eq (mul_comm C c)
  have hBC : BC + G ^ 2 ≤ C := by
    have hp : 0 ≤ 4 * T / c := by positivity
    dsimp [C]
    nlinarith only [abs_nonneg C0, sq_nonneg G, hp]
  have hSphere (j : ℕ) (x : E n) (hx : x ∈ unitSphere n) (v : E n) (hv : ‖v‖ = 1) :
      |realHessian (u (j + 1)) x v v| ≤ BC :=
    hBoundary (u (j + 1)) (u j) ⟨univ, isOpen_univ, subset_univ _, (hu (j + 1)).contDiffOn⟩
      (hu j) (hu0 (j + 1)) (huP (j + 1)) (hEq j)
      (fun y hy => hDensity j y (ball_subset_closedBall hy)) G hG.le
      (fun y hy => hGrad j y (ball_subset_closedBall hy)) x hx v hv
  have hUp (j : ℕ) : ∀ x ∈ closedUnitBall n, ∀ v : E n, ‖v‖ = 1 →
      realHessian (u j) x v v ≤ C := by
    induction j with
    | zero =>
      intro x hx v hv
      have h := ((realHessian (u 0) x v).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((realHessian (u 0) x).le_opNorm v) (norm_nonneg v))
      rw [hv, mul_one, mul_one, Real.norm_eq_abs] at h
      exact (le_abs_self _).trans (h.trans ((hC0 x hx).trans hC0C))
    | succ j ih =>
      exact gibbs_realHessian_upper_of_absorption hn hγ (pow_pos hb n).le hG.le hc hC
        hCS hTC hBC (hu (j + 1)) (hu j) (huP (j + 1)) (hEq j)
        (fun x hx => (hDensity j x (ball_subset_closedBall hx)).2)
        (fun x hx => (hCoeff j x (ball_subset_closedBall hx)).2) (hGrad (j + 1))
        (fun x hx => hGrad j x (ball_subset_closedBall hx))
        (fun x hx => ih x (ball_subset_closedBall hx))
        (fun x hx v hv => (le_abs_self _).trans (hSphere j x hx v hv))
  have hAbs (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) (v : E n) (hv : ‖v‖ = 1) :
      |realHessian (u j) x v v| ≤ C := by
    cases j with
    | zero =>
      have h := ((realHessian (u 0) x v).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((realHessian (u 0) x).le_opNorm v) (norm_nonneg v))
      rw [hv, mul_one, mul_one, Real.norm_eq_abs] at h
      exact h.trans ((hC0 x hx).trans hC0C)
    | succ j =>
      rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with hlt | heq
      · have hxB : x ∈ unitBall n := mem_ball_zero_iff.mpr hlt
        have hv0 : v ≠ 0 := by intro he; simp [he] at hv
        have hPos : 0 < realMetricForm (u (j + 1)) x v v := by
          rw [realMetricForm_eq]
          exact hermitianRealification_pos (huP (j + 1) x hxB) v hv0
        rw [realMetricForm_eq_average_hessian (hu (j + 1)).contDiffAt] at hPos
        have hJ := hUp (j + 1) x hx (J v) (by rw [norm_J, hv])
        exact abs_le.mpr ⟨by linarith only [hPos, hJ], hUp (j + 1) x hx v hv⟩
      · exact (hSphere j x (mem_sphere_zero_iff_norm.mpr heq) v hv).trans
          (le_trans (le_add_of_nonneg_right (sq_nonneg G)) hBC)
  exact ⟨C, hC, fun j x hx => norm_realHessian_le_of_unit_test (hu j).contDiffAt hC.le (hAbs j x hx)⟩

theorem exists_uniform_lipschitz_firstJet_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 0 < n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ L : ℝ≥0, ∀ j, LipschitzOnWith L (fderiv ℝ (u j)) (closedUnitBall n) := by
  obtain ⟨C, hC, hH⟩ :=
    exists_uniform_realHessian_bound_of_bounded_smoothGibbsIteration hn hγ hu hu0 huP hEq hM huB
  refine ⟨⟨C, hC.le⟩, fun j => ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall (0 : E n) 1)
  · intro x _
    exact ((hu j).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  · intro x hx
    exact_mod_cast hH j x hx

end KEBall.MoserTrudinger
