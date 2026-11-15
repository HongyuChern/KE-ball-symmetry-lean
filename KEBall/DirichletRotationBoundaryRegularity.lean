import KEBall.DirichletBoundaryDerivativeLimit
import KEBall.DirichletBoundaryDerivativeExtension
import KEBall.DirichletRotationInteriorScale
import KEBall.DirichletLogDensityCombinedLimit

/-!
# Closed-ball C1 regularity of the actual rotation derivatives

The potential is only assumed C2 in the open ball.  The boundary derivative
of its rotation trace is obtained from the proved quotient decay and local
interpolation, rather than assumed as a boundary second derivative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ContDiff Matrix NNReal Topology

namespace KEBall

theorem exists_dirichlet_rotation_boundary_firstJet {n : ℕ} (hn : 0 < n)
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hw2 : ContDiffOn ℝ 2 w (unitBall n))
    (hDclosed : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x)
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hLip : LipschitzOnWith L G (closedUnitBall n))
    (hw0 : ∀ x ∈ unitSphere n, w x = 0)
    (hHolder : ∃ β H : ℝ, 0 < β ∧ β ≤ 1 ∧ 0 ≤ H ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖realHessian w x - realHessian w y‖ ≤ (H * (4 / R : ℝ) ^ β) * ‖x - y‖ ^ β)
    (hPower : HasDirichletRotationBoundaryPower G)
    (T : E n →L[ℝ] E n) (hTJ : ∀ y, T (J y) = J (T y))
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hTM : ∀ y, complexCoord (T y) = M *ᵥ complexCoord y)
    (hM : Mᴴᵀ = -Mᵀ) (hTan : ∀ x ∈ unitSphere n, inner ℝ x (T x) = 0)
    (hNorm : ‖T‖ ≤ 3) :
    ∃ (a : E n → ℝ) (Q : E n → E n →L[ℝ] ℝ),
      ContinuousOn a (unitSphere n) ∧ ContinuousOn Q (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, Q x = fderiv ℝ (fun y => G y (T y)) x) ∧
      (∀ p ∈ unitSphere n, Q p = a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p) ∧
      (∀ x ∈ closedUnitBall n,
        HasFDerivWithinAt (fun y => G y (T y)) (Q x) (closedUnitBall n) x) ∧
      ContDiffOn ℝ 1 (fun y => G y (T y)) (closedUnitBall n) ∧
      (∀ p ∈ unitSphere n, Tendsto (fderiv ℝ (fun y => G y (T y)))
        (𝓝[unitBall n] p) (𝓝 (a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p))) := by
  obtain ⟨β, H, hβ, hβ1, hH, hGH⟩ := hHolder
  obtain ⟨α, C, hα, hα1, hC, hP⟩ := hPower
  have hOsc := hP T hTJ M hTM hM hTan hNorm
  let B : ℝ := 2 * (2 * (L : ℝ) + ‖G 0‖) * ‖T‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBound (x : E n) (hx : x ∈ unitBall n) :
      |G x (T x) / dirichletBoundaryDistanceProxy x| ≤ B :=
    abs_dirichlet_rotation_firstJet_quotient_le hn hLip hDclosed hw0 T hTan hx
  obtain ⟨a, hATrace, hATracePower, _⟩ :=
    exists_dirichlet_boundary_trace_with_power_control hα hC hBound hOsc
  have hABound (p : E n) (hp : p ∈ unitSphere n) : |a p| ≤ B :=
    abs_dirichlet_boundary_trace_le hBound hp (hATrace p hp)
  have hAC : ContinuousOn a (unitSphere n) :=
    continuousOn_dirichlet_boundary_trace hB hC hα hBound hATrace hOsc
  obtain ⟨hqD, K, hK, hqHolder⟩ :=
    exists_dirichlet_rotation_derivative_boundary_scale_holder hw2 hD hLip hβ hβ1 hH hGH T
  have hLimit (p : E n) (hp : p ∈ unitSphere n) :=
    tendsto_dirichlet_boundary_fderiv_of_quotient_and_scaled_holder hn
      hB hC hK hα hβ hβ1 hqD hABound hAC hATracePower hqHolder hp
  have hρC : Continuous (fun x : E n => fderiv ℝ (@dirichletBoundaryDistanceProxy n) x) := by
    simpa only [fderiv_dirichletBoundaryDistanceProxy] using! (innerSL ℝ (E := E n)).continuous.neg
  have hQBoundary : ContinuousOn
      (fun p => a p • fderiv ℝ (@dirichletBoundaryDistanceProxy n) p) (unitSphere n) :=
    hAC.smul hρC.continuousOn
  have hG1 : ContDiffOn ℝ 1 G (unitBall n) := by
    have hW1 : ContDiffOn ℝ 1 (fderiv ℝ w) (unitBall n) := fun x hx =>
      ((hw2.contDiffAt (isOpen_ball.mem_nhds hx)).fderiv_right
        (m := 1) (by norm_num)).contDiffWithinAt
    exact hW1.congr fun x hx => (hD x hx).fderiv.symm
  have hq1 : ContDiffOn ℝ 1 (fun y => G y (T y)) (unitBall n) :=
    hG1.clm_apply T.contDiff.contDiffOn
  have hqC : ContinuousOn (fun y => G y (T y)) (closedUnitBall n) :=
    hLip.continuousOn.clm_apply T.continuous.continuousOn
  obtain ⟨Q, hQC, hQi, hQb, hQD, hqClosed⟩ :=
    exists_dirichlet_closedBall_derivative_extension hqC hq1 hQBoundary hLimit
  exact ⟨a, Q, hAC, hQC, hQi, hQb, hQD, hqClosed, hLimit⟩

end KEBall
