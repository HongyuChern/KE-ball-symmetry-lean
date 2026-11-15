import KEBall.DirichletHessianInteriorC2
import KEBall.DirichletInteriorHessianEquation

/-!
# Classical interior solutions at limits of the smooth log-density path

This is an interior theorem with continuous zero boundary data.  Closed-ball
smoothness, needed by the full continuity-method solver, is not part of its
conclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem exists_dirichlet_interior_classical_limit_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      ContinuousOn w (closedUnitBall n) ∧
      ContDiffOn ℝ 2 w (unitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      ∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x) := by
  obtain ⟨w, G, L, hwC, hw2, hD, hLip, hw0, hAe⟩ :=
    exists_dirichlet_limit_interior_C2_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  have hHess (x : E n) (hx : x ∈ unitBall n) :
      complexHessianOfRealBilinear (fderiv ℝ G x) = complexHessian w x := by
    rw [fderiv_dirichlet_firstJet_eq_realHessian hD hx]
    exact complexHessianOfRealBilinear_eq (hw2.contDiffAt (isOpen_ball.mem_nhds hx))
  have hAe' : ∀ᵐ x ∂ν[n], (complexHessian w x).PosDef ∧
      (complexHessian w x).det.re = Real.exp (t₀ * g x) := by
    filter_upwards [hAe, ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx hxB
    rwa [hHess x hxB] at hx
  have hgC : ContinuousOn g (unitBall n) := by
    obtain ⟨U, _, hSub, hgU⟩ := hg
    exact hgU.continuousOn.mono (ball_subset_closedBall.trans hSub)
  have hPoint : EqOn (fun x => (complexHessian w x).det.re)
      (fun x => Real.exp (t₀ * g x)) (unitBall n) :=
    Measure.eqOn_open_of_ae_eq (hAe'.mono fun _ hx => hx.2) isOpen_ball
      (continuousOn_det_complexHessian_C2 hw2)
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hgC))
  have hPos := dirichlet_complexHessian_posDef_of_interior_C2_ae hw2
    (hAe'.mono fun _ hx => hx.1)
    (fun x hx => by
      have he := hPoint hx
      dsimp only at he
      exact (Real.exp_pos _).trans_eq he.symm)
  exact ⟨w, G, L, hwC, hw2, hD, hLip, hw0, hPos, fun x hx => hPoint hx⟩

end KEBall
