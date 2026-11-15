import KEBall.DirichletPoissonIteration
import KEBall.MoserTrudingerGibbsModulus
import KEBall.MoserTrudingerGibbsTraceBound
import KEBall.DirichletLaplacianTrace

/-! Uniform gradient and complex-Hessian trace bounds for the actual Gibbs
inverse iteration, with no bound on previous gradients assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Laplacian Topology

namespace KEBall.MoserTrudinger

open Cegrell

/-- Energy and amplitude bounds along a genuine Gibbs inverse iteration imply
one gradient bound for all iterates and one trace bound for all outputs. -/
theorem exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration
    {n : ℕ} (hn : 0 < n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ G : ℝ, 0 < G ∧ ∃ D : ℝ, 0 < D ∧
      (∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ G) ∧
      ∀ j x, x ∈ closedUnitBall n → (complexHessian (u (j + 1)) x).trace.re ≤ D := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a : ℝ := Real.exp (-(γ * B) / n)
  let b : ℝ := Real.exp ((γ * B) / n)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
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
  have hDensity (j : ℕ) (x : E n) (hx : x ∈ unitBall n) :
      a ^ n ≤ gibbsDensity γ (u j) x ∧ gibbsDensity γ (u j) x ≤ b ^ n := by
    rw [haPow, hbPow]
    exact gibbsDensity_bounds_of_nonpositive_bounded hn hγ
      (hu j).continuous.continuousOn (huB j) x (ball_subset_closedBall hx)
  let uNear (j : ℕ) : SmoothNear (closedUnitBall n) (u j) :=
    ⟨univ, isOpen_univ, subset_univ _, (hu j).contDiffOn⟩
  have hBarrier (j : ℕ) := quadratic_and_boundarySlope_bounds hn (uNear (j + 1))
    (fun x hx => (huP (j + 1) x hx).posSemidef) (hu0 (j + 1)) ha hb
    (fun x hx => hEq j x hx ▸ hDensity j x hx)
  have hbar (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) :
      ‖u (j + 1) x‖ ≤ (2 * b) * (1 - ‖x‖) := by
    rw [Real.norm_eq_abs, abs_of_nonpos (huB (j + 1) x hx).2]
    have hlo := (hBarrier j).1 x hx |>.1
    have hs := mul_nonneg hb.le (sq_nonneg (‖x‖ - 1))
    nlinarith only [hlo, hs]
  have hboundary (j : ℕ) (x : E n) (hx : x ∈ unitSphere n) :
      ‖fderiv ℝ (u (j + 1)) x‖ ≤ 2 * b := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro v hv
    have hInner := abs_real_inner_le_norm x v
    rw [mem_sphere_zero_iff_norm.mp hx, hv, one_mul] at hInner
    obtain ⟨h₁, h₂⟩ := (hBarrier j).2 x hx
    have hPos : 0 ≤ 2 * boundarySlope (u (j + 1)) x :=
      mul_nonneg (by norm_num) (ha.le.trans h₁)
    rw [Real.norm_eq_abs, sphere_fderiv_normal (uNear (j + 1)) (hu0 (j + 1)) hx v,
      abs_mul, abs_of_nonneg hPos]
    exact (mul_le_mul_of_nonneg_left hInner hPos).trans (by linarith)
  have hAE (j : ℕ) : ∀ᵐ x ∂(volume0 n).restrict (unitBall n), u j x ∈ Icc (-B) 0 := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact huB j x (ball_subset_closedBall hx)
  have hmod := exists_uniform_modulus_of_smoothGibbsPairs hn hγ hu
    (fun j => hu (j + 1)) hu0 (fun j => hu0 (j + 1)) huP
    (fun j => huP (j + 1)) hEq hM hAE
  obtain ⟨T, hT, hTrace⟩ := exists_uniform_trace_bound_of_gibbs_density
    (B := B) hn hγ ha hb
  have hrec (j : ℕ) (G : ℝ) (hG : 0 ≤ G)
      (hGrad : ∀ x ∈ closedUnitBall n, ‖fderiv ℝ (u j) x‖ ≤ G) :
      ∀ x ∈ unitBall n, ‖Δ (u (j + 1)) x‖ ≤ (4 * T) * (1 + G ^ 2) := by
    intro x hx
    have htr := hTrace (u (j + 1)) (u j) (hu (j + 1)) (hu j)
      (hu0 (j + 1)) (hu0 j) (huP (j + 1))
      (fun y hy => (huP j y hy).posSemidef) (hEq j) (hDensity j)
      (fun y hy => (huB j y hy).1) G hG
      (fun y hy => hGrad y (ball_subset_closedBall hy)) x (ball_subset_closedBall hx)
    have htr0 := (dirichlet_posDef_trace_re_pos (huP (j + 1) x hx)).le
    rw [euclideanLaplacian_eq_four_complexHessian_trace_re (hu (j + 1)).contDiffAt,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) htr0)]
    nlinarith only [htr]
  obtain ⟨G, hG, hGrad⟩ := exists_uniform_gradient_bound_of_poisson_iteration hu
    (by positivity : 0 ≤ 2 * b) (by positivity : 0 < 4 * T) hbar hboundary hmod hrec
  refine ⟨G, hG, T * (1 + G ^ 2), by positivity, hGrad, ?_⟩
  intro j x hx
  exact hTrace (u (j + 1)) (u j) (hu (j + 1)) (hu j)
    (hu0 (j + 1)) (hu0 j) (huP (j + 1))
    (fun y hy => (huP j y hy).posSemidef) (hEq j) (hDensity j)
    (fun y hy => (huB j y hy).1) G hG.le
    (fun y hy => hGrad j y (ball_subset_closedBall hy)) x hx

/-- The subcritical iteration supplied by the unconditional smooth Gibbs solve
has uniform first-derivative and complex trace bounds. -/
theorem exists_uniformly_bounded_smoothGibbsIteration {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    ∃ (u : ℕ → E n → ℝ) (M B G D : ℝ),
      u 0 = v ∧ (∀ j, ContDiff ℝ ∞ (u j)) ∧
      (∀ j x, x ∈ unitSphere n → u j x = 0) ∧
      (∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef) ∧
      (∀ j x, x ∈ unitBall n →
        (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x) ∧
      Monotone (fun j => smoothFunctional γ (u j)) ∧
      (∀ j, smoothEnergy (u j) ≤ M) ∧ 0 < B ∧
      (∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) ∧
      0 < G ∧ (∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ G) ∧
      0 < D ∧ ∀ j x, x ∈ closedUnitBall n →
        (complexHessian (u (j + 1)) x).trace.re ≤ D := by
  obtain ⟨u, M, B, hinit, hu, hu0, huP, hEq, hmono, hM, hB, huB⟩ :=
    exists_bounded_smoothGibbsIteration_unconditional hn hγ hγn hv hv0 hvP
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration
      (by omega) hγ.le hu hu0 huP hEq hM huB
  exact ⟨u, M, B, G, D, hinit, hu, hu0, huP, hEq, hmono, hM, hB, huB, hG, hGrad, hD, hTrace⟩

end KEBall.MoserTrudinger
