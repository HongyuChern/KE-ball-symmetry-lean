import KEBall.DirichletTraceCofactorBounds
import KEBall.MoserTrudingerGibbsGradientUniform

/-! Uniform ellipticity of the actual Gibbs cofactor family. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall.MoserTrudinger

theorem exists_power_density_bounds_of_bounded_family {n : ℕ} (hn : 0 < n)
    {γ B : ℝ} (hγ : 0 ≤ γ) {u : ℕ → E n → ℝ}
    (hu : ∀ j, ContinuousOn (u j) (closedUnitBall n))
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ j x, x ∈ closedUnitBall n →
      a ^ n ≤ gibbsDensity γ (u j) x ∧ gibbsDensity γ (u j) x ≤ b ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a : ℝ := Real.exp (-(γ * B) / n)
  let b : ℝ := Real.exp ((γ * B) / n)
  have haPow : a ^ n = Real.exp (-(γ * B)) := by
    dsimp [a]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [hnR.ne']
  have hbPow : b ^ n = Real.exp (γ * B) := by
    dsimp [b]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [hnR.ne']
  refine ⟨a, b, Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro j x hx
  rw [haPow, hbPow]
  exact gibbsDensity_bounds_of_nonpositive_bounded hn hγ (hu j) (huB j) x hx

/-- Uniform complex trace and amplitude bounds give a common ellipticity
interval and operator-norm bound for every actual Gibbs output cofactor. -/
theorem exists_uniform_cofactor_bounds_of_smoothGibbs_trace
    {n : ℕ} (hn : 0 < n) {γ B D : ℝ} (hγ : 0 ≤ γ) (hD : 0 < D)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0)
    (hTrace : ∀ j x, x ∈ closedUnitBall n → (complexHessian (u (j + 1)) x).trace.re ≤ D) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ j x, x ∈ closedUnitBall n →
      ‖dirichletCofactorOperator (u (j + 1)) x‖ ≤ K ∧
      ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator (u (j + 1)) x v) v := by
  obtain ⟨a, b, ha, hb, hDensity⟩ := exists_power_density_bounds_of_bounded_family hn hγ
    (fun j => (hu j).continuous.continuousOn) huB
  refine ⟨a ^ n * (D⁻¹ / 4), b ^ n * ((a ^ n / D ^ (n - 1))⁻¹ / 4),
    by positivity, by positivity, ?_⟩
  intro j x hx
  have hNear : SmoothNear (closedUnitBall n) (u (j + 1)) :=
    ⟨univ, isOpen_univ, subset_univ _, (hu (j + 1)).contDiffOn⟩
  have hDensityNear : SmoothNear (closedUnitBall n) (gibbsDensity γ (u j)) :=
    ⟨univ, isOpen_univ, subset_univ _, (((contDiff_const.mul (hu j)).exp).div_const _).contDiffOn⟩
  exact dirichletCofactorOperator_bounds_of_det_trace hNear hDensityNear
    (huP (j + 1)) (hEq j) ha hb hD (hDensity j) (hTrace j) hx

theorem exists_uniform_cofactor_bounds_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 0 < n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ j x, x ∈ closedUnitBall n →
      ‖dirichletCofactorOperator (u (j + 1)) x‖ ≤ K ∧
      ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator (u (j + 1)) x v) v := by
  obtain ⟨_, _, D, hD, _, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration hn hγ hu hu0 huP hEq hM huB
  exact exists_uniform_cofactor_bounds_of_smoothGibbs_trace hn hγ hD hu huP hEq huB hTrace

end KEBall.MoserTrudinger
