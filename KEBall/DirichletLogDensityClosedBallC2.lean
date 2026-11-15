import KEBall.DirichletClosedBallHessianRegularity

/-!
# Closed-ball C2 compactness on the prescribed log-density path

All estimates refer to the same limiting potential and first jet.  This
theorem proves C2 regularity up to the sphere; it does not assert smoothness
or solve the separate weak Gibbs regularity problem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall

theorem exists_dirichlet_closedBall_C2_limit_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      StrictMono φ ∧ TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      ContDiffOn ℝ 2 w (closedUnitBall n) ∧
      (∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧ (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) := by
  obtain ⟨φ, w, G, L, hφ, hUw, hGrad, hw1, hw2, hDclosed, hD, hLip, hw0,
      hPos, hDet, _, hHolder, hPower⟩ :=
    exists_dirichlet_C1_interior_boundary_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  have hgC : ContinuousOn g (closedUnitBall n) :=
    fun x hx => (hg.contDiffAt hx).continuousAt.continuousWithinAt
  have hfC : ContinuousOn (fun x => Real.exp (t₀ * g x)) (closedUnitBall n) :=
    fun x hx => Real.continuous_exp.continuousAt.comp_continuousWithinAt
      ((continuousOn_const.mul hgC) x hx)
  have hwClosed := contDiffOn_two_dirichlet_of_rotation_boundary_power (by omega : 0 < n)
    hw1.continuousOn hw2 hDclosed hD hLip hw0 hHolder hPower hfC
    (fun x _ => Real.exp_pos (t₀ * g x)) hPos hDet
  exact ⟨φ, w, G, L, hφ, hUw, hGrad, hwClosed, hDclosed, hLip, hw0, hPos, hDet⟩

end KEBall
