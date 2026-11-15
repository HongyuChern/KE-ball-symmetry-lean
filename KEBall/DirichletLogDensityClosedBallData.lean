import KEBall.DirichletClosedBallEllipticity

/-!
# Retained elliptic and oscillation data at the same closed-ball limit

This strengthens the compiled C2 compactness output by retaining its
actual first jet, the interior Hessian decay and the boundary rotation
decay.  Positivity and the prescribed determinant hold for the within
Hessian on the entire closed ball, including the sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall

theorem exists_dirichlet_closedBall_C2_elliptic_limit_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
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
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧ (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian w x).PosDef ∧
        (dirichletWithinComplexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      HasDirichletHessianOscillationDecay G ∧ HasDirichletRotationBoundaryPower G ∧
      (let A (x : E n) := dirichletCofactorOfMatrix (dirichletWithinComplexHessian w x)
       ContinuousOn A (closedUnitBall n) ∧
        (∀ x ∈ closedUnitBall n, ∀ v z : E n, inner ℝ (A x v) z = inner ℝ (A x z) v) ∧
        ∃ l M : ℝ, 0 < l ∧ 0 < M ∧
          (∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M) ∧
          ∀ x ∈ closedUnitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) := by
  obtain ⟨φ, w, G, L, hφ, hUw, hGrad, hw1, hw2, hDclosed, hD, hLip, hw0,
      hPos, hDet, hDecay, hHolder, hPower⟩ :=
    exists_dirichlet_C1_interior_boundary_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  have hgC : ContinuousOn g (closedUnitBall n) :=
    fun x hx => (hg.contDiffAt hx).continuousAt.continuousWithinAt
  have hfC : ContinuousOn (fun x => Real.exp (t₀ * g x)) (closedUnitBall n) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hgC)
  have hwClosed := contDiffOn_two_dirichlet_of_rotation_boundary_power (by omega : 0 < n)
    hw1.continuousOn hw2 hDclosed hD hLip hw0 hHolder hPower hfC
    (fun x _ => Real.exp_pos (t₀ * g x)) hPos hDet
  have hClosed := closedBall_withinHessian_posDef_and_det_of_C2 hwClosed hfC
    (fun x _ => Real.exp_pos (t₀ * g x)) hPos (fun x hx => hDet x hx)
  refine ⟨φ, w, G, L, hφ, hUw, hGrad, hwClosed, hDclosed, hD, hLip, hw0,
    hPos, hDet, hClosed, hDecay, hPower, ?_⟩
  exact exists_dirichlet_closedBall_cofactor_ellipticity_of_C2 (by omega) hwClosed hfC
    (fun x _ => Real.exp_pos (t₀ * g x)) hPos (fun x hx => hDet x hx)

end KEBall
