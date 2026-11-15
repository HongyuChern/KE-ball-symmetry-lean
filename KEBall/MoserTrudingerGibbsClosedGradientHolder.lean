import KEBall.DirichletPoissonClosedGradientHolder
import KEBall.MoserTrudingerGibbsGradientUniform

/-! One closed-ball Holder constant for the actual gradients of all Gibbs
outputs, obtained from the Poisson equation and the actual zero boundary data. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped ComplexOrder ContDiff Laplacian NNReal

namespace KEBall.MoserTrudinger

theorem exists_uniform_closed_gradient_holder_of_smoothGibbs_bounds
    {n : ℕ} (hn : 2 ≤ n) {D G : ℝ} (hD : 0 < D) (hG : 0 ≤ G)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hTrace : ∀ j x, x ∈ closedUnitBall n →
      (complexHessian (u (j + 1)) x).trace.re ≤ D)
    (hGrad : ∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ G) :
    ∃ θ K : ℝ≥0, 0 < θ ∧ θ < 1 ∧
      ∀ j, HolderOnWith K θ (fderiv ℝ (u (j + 1))) (closedUnitBall n) := by
  letI : NeZero n := ⟨by omega⟩
  apply exists_uniform_closedBall_poisson_gradient_holder hn (fun j => u (j + 1))
    hG (by positivity : 0 ≤ 4 * D) (fun j => hu (j + 1))
    (fun j => hu0 (j + 1)) (fun j => hGrad (j + 1))
  intro j x hx
  have htr := hTrace j x (ball_subset_closedBall hx)
  have htr0 := (dirichlet_posDef_trace_re_pos (huP (j + 1) x hx)).le
  rw [euclideanLaplacian_eq_four_complexHessian_trace_re (hu (j + 1)).contDiffAt,
    abs_of_nonneg (mul_nonneg (by norm_num) htr0)]
  exact mul_le_mul_of_nonneg_left htr (by norm_num)

theorem exists_uniform_closed_gradient_holder_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ θ K : ℝ≥0, 0 < θ ∧ θ < 1 ∧
      ∀ j, HolderOnWith K θ (fderiv ℝ (u (j + 1))) (closedUnitBall n) := by
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration
      (by omega) hγ hu hu0 huP hEq hM huB
  exact exists_uniform_closed_gradient_holder_of_smoothGibbs_bounds hn hD hG.le
    hu hu0 huP hTrace hGrad

end KEBall.MoserTrudinger
