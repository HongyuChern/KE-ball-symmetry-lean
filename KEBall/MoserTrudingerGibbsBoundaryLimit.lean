import KEBall.MoserTrudingerGibbsBoundaryPower
import KEBall.MoserTrudingerGibbsHessianUniform
import KEBall.DirichletLogDensityCombinedLimit

/-! The actual Gibbs rotation quotient power passes to the specified
uniform first-jet limit, with no smoothness assumption on its density. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff Matrix NNReal Topology

namespace KEBall.MoserTrudinger

theorem hasDirichletRotationBoundaryPower_of_bounded_smoothGibbs_firstJet_limit
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0)
    {ι : ℕ → ℕ} (hι : StrictMono ι) {Dw : E n → E n →L[ℝ] ℝ}
    (hDU : TendstoUniformlyOn (fun j => fderiv ℝ (u (ι j))) Dw atTop (closedUnitBall n)) :
    HasDirichletRotationBoundaryPower Dw := by
  have hn0 : 0 < n := by omega
  obtain ⟨G, hG, _, _, hGrad, _⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration hn0 hγ hu hu0 huP hEq hM huB
  obtain ⟨L, hLip⟩ :=
    exists_uniform_lipschitz_firstJet_of_bounded_smoothGibbsIteration hn0 hγ hu hu0 huP hEq hM huB
  obtain ⟨α, C, hα, hα1, hC, hPower⟩ :=
    exists_uniform_rotation_boundary_power_of_bounded_smoothGibbsIteration
      hn hγ (by norm_num : (0 : ℝ) ≤ 3) hu hu0 huP hEq hM huB
  refine ⟨α, C * (256 : ℝ) ^ α, hα, hα1, by positivity, ?_⟩
  intro T hTJ A hTA hA hTan hT p hp r hr hr1
  let κ (j : ℕ) := ι (j + 1)
  have hκ (j : ℕ) : 1 ≤ κ j := (by omega : 1 ≤ j + 1).trans (hι.id_le (j + 1))
  have hBound (j : ℕ) (x : E n) (hx : x ∈ unitBall n) :
      |fderiv ℝ (u (κ j)) x (T x) / dirichletBoundaryDistanceProxy x| ≤
        2 * (2 * (L : ℝ) + G) * 3 := by
    have hDu (y : E n) (_hy : y ∈ closedUnitBall n) :
        HasFDerivWithinAt (u (κ j)) (fderiv ℝ (u (κ j)) y) (closedUnitBall n) y :=
      ((hu (κ j)).differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt
    have h := abs_dirichlet_rotation_firstJet_quotient_le hn0 (hLip (κ j)) hDu
      (hu0 (κ j)) T hTan hx
    have hFirst : 2 * (2 * (L : ℝ) + ‖fderiv ℝ (u (κ j)) 0‖) ≤
        2 * (2 * (L : ℝ) + G) := by
      linarith only [hGrad (κ j) 0 (by simp [closedUnitBall])]
    exact h.trans (mul_le_mul hFirst hT (norm_nonneg T) (by positivity))
  have hLim (x : E n) (hx : x ∈ unitBall n) :
      Tendsto (fun j => fderiv ℝ (u (κ j)) x (T x) / dirichletBoundaryDistanceProxy x)
        atTop (𝓝 (Dw x (T x) / dirichletBoundaryDistanceProxy x)) := by
    have h := (hDU.tendsto_at (ball_subset_closedBall hx)).comp (tendsto_add_atTop_nat 1)
    exact (((ContinuousLinearMap.apply ℝ ℝ (T x)).continuous.tendsto (Dw x)).comp h).div_const _
  apply dirichletBoundaryOscillation_le_of_pointwise_limit hBound hLim hp hr
  intro j
  have h := hPower (κ j - 1) T hTJ A hTA hA hTan hT p hp 1 zero_lt_one le_rfl r hr hr1
  simpa only [Nat.sub_add_cancel (hκ j), div_one] using h

end KEBall.MoserTrudinger
