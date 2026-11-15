import KEBall.DirichletLogDensityClosedBallData
import KEBall.DirichletOscillationInteriorC3

/-!
# The actual log-density path limit has interior C3 regularity

This is the same uniformly attained C2 closed-ball limit, with the same
first jet, boundary values and prescribed determinant.  The conclusion
does not assert higher regularity on the sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall

theorem exists_dirichlet_closedBall_C2_interior_C3_limit_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
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
      ContDiffOn ℝ 2 w (closedUnitBall n) ∧ ContDiffOn ℝ 3 w (unitBall n) ∧
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
  obtain ⟨φ, w, G, L, hφ, hUw, hGrad, hwC2, hDclosed, hD, hLip, hw0,
      hPos, hDet, hClosed, hDecay, hPower, hElliptic⟩ :=
    exists_dirichlet_closedBall_C2_elliptic_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  have hf : ContDiffOn ℝ 2 (fun x => Real.exp (t₀ * g x)) (unitBall n) := by
    intro x hx
    exact (((contDiffAt_const (c := t₀)).mul
      (hg.contDiffAt (ball_subset_closedBall hx))).exp.of_le
        (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
  have hwC3 := contDiffOn_three_of_dirichlet_hessian_oscillation_and_determinant
    (by omega : 0 < n) hD hLip hDecay hf hPos hDet
  exact ⟨φ, w, G, L, hφ, hUw, hGrad, hwC2, hwC3, hDclosed, hD, hLip, hw0,
    hPos, hDet, hClosed, hDecay, hPower, hElliptic⟩

end KEBall
