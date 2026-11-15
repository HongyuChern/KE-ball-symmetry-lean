import KEBall.DirichletPoissonScaledGradientHolder
import KEBall.MoserTrudingerGibbsGradientUniform

/-! Uniform local continuity of the actual first derivatives of Gibbs outputs.
The only second-order input is the proved complex trace bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

open Metric Set
open scoped ComplexOrder ContDiff Laplacian

namespace KEBall.MoserTrudinger

theorem exists_uniform_gradient_holder_of_smoothGibbs_bounds
    {n : ℕ} (hn : 0 < n) {D G : ℝ} (hD : 0 < D) (hG : 0 ≤ G)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hTrace : ∀ j x, x ∈ closedUnitBall n →
      (complexHessian (u (j + 1)) x).trace.re ≤ D)
    (hGrad : ∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ G) :
    ∃ H : ℝ, 0 < H ∧ ∀ (j : ℕ) (p : E n) (R : ℝ),
      0 < R → R ≤ 1 → closedBall p R ⊆ unitBall n →
        ∀ x ∈ ball p (R / 2), ∀ y ∈ ball p (R / 2),
          ‖fderiv ℝ (u (j + 1)) x - fderiv ℝ (u (j + 1)) y‖ ≤
            (H / Real.sqrt R) * Real.sqrt ‖x - y‖ := by
  letI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C, hC, hLocal⟩ := exists_local_poisson_scaled_gradient_holder_constant (V := E n)
  refine ⟨C * (G + 4 * D), by positivity, ?_⟩
  intro j p R hR hR1 hSub x hx y hy
  apply hLocal (u (j + 1)) (hu (j + 1)) p R G (4 * D) hR hR1 hG
    (by positivity) (fun z hz => hGrad (j + 1) z (ball_subset_closedBall (hSub hz)))
    _ x hx y hy
  intro z hz
  have htr := hTrace j z (ball_subset_closedBall (hSub hz))
  have htr0 := (dirichlet_posDef_trace_re_pos (huP (j + 1) z (hSub hz))).le
  rw [euclideanLaplacian_eq_four_complexHessian_trace_re (hu (j + 1)).contDiffAt,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) htr0)]
  exact mul_le_mul_of_nonneg_left htr (by norm_num)

theorem exists_uniform_gradient_holder_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 0 < n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ H : ℝ, 0 < H ∧ ∀ (j : ℕ) (p : E n) (R : ℝ),
      0 < R → R ≤ 1 → closedBall p R ⊆ unitBall n →
        ∀ x ∈ ball p (R / 2), ∀ y ∈ ball p (R / 2),
          ‖fderiv ℝ (u (j + 1)) x - fderiv ℝ (u (j + 1)) y‖ ≤
            (H / Real.sqrt R) * Real.sqrt ‖x - y‖ := by
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration hn hγ hu hu0 huP hEq hM huB
  exact exists_uniform_gradient_holder_of_smoothGibbs_bounds hn hD hG.le hu huP hTrace hGrad

end KEBall.MoserTrudinger
