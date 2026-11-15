import KEBall.DirichletLogDensityInteriorSmooth
import KEBall.DirichletClosedBallHessianHolder

/-!
# Actual closed-ball Holder jets of the log-density path limit

The Hessian and the real cofactor below belong to the same limit witness.
The exponent is positive and common to both estimates.  This records C2
regularity with a Holder Hessian on the closed ball and smoothness in its
interior; smoothness on a neighborhood of the closed ball is not asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

theorem exists_dirichlet_closedBall_C2_holder_interior_smooth_limit_of_logDensityPath
    {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L α : ℝ≥0),
      StrictMono φ ∧ TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      ContDiffOn ℝ 2 w (closedUnitBall n) ∧ ContDiffOn ℝ ∞ w (unitBall n) ∧
      (∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧ (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian w x).PosDef ∧
        (dirichletWithinComplexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      HasDirichletHessianOscillationDecay G ∧ HasDirichletRotationBoundaryPower G ∧
      0 < α ∧ α < 1 ∧
      HasDirichletHolderOn α
        (fderivWithin ℝ (fderivWithin ℝ w (closedUnitBall n)) (closedUnitBall n))
        (closedUnitBall n) ∧
      (let A (x : E n) := dirichletCofactorOfMatrix (dirichletWithinComplexHessian w x)
       HasDirichletHolderOn α A (closedUnitBall n) ∧
        ContinuousOn A (closedUnitBall n) ∧
        (∀ x ∈ closedUnitBall n, ∀ v z : E n, inner ℝ (A x v) z = inner ℝ (A x z) v) ∧
        ∃ l M : ℝ, 0 < l ∧ 0 < M ∧
          (∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M) ∧
          ∀ x ∈ closedUnitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) := by
  obtain ⟨φ, w, G, L, hφ, hUw, hGrad, hwC2, hwSmooth, hDclosed, hD, hLip, hw0,
      hPos, hDet, hClosed, hDecay, hPower, hElliptic⟩ :=
    exists_dirichlet_closedBall_C2_interior_smooth_limit_of_logDensityPath
      hn hg ht hT hu hu0 huP hEq
  have hf : ContDiffOn ℝ 1 (fun x => Real.exp (t₀ * g x)) (closedUnitBall n) := by
    intro x hx
    exact ((((contDiffAt_const (c := t₀)).mul (hg.contDiffAt hx)).exp).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).contDiffWithinAt
  obtain ⟨α, hα, hα1, hH⟩ := exists_dirichlet_closedBall_holder_realHessian
    (by omega : 0 < n) hwC2
    (hwSmooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) hf hDclosed hD hLip hw0
    hDecay hPower (fun x hx => (hClosed x hx).1) (fun x hx => (hClosed x hx).2)
  have hA : HasDirichletHolderOn α
      (fun x => dirichletCofactorOfMatrix (dirichletWithinComplexHessian w x))
      (closedUnitBall n) := by
    exact hH.comp_smooth (isCompact_closedBall _ _) hα
      (g := fun B => dirichletCofactorOfMatrix (complexHessianOfRealBilinear B))
      (contDiff_dirichletCofactorOfMatrix.comp contDiff_dirichlet_complexHessianOfRealBilinear)
  exact ⟨φ, w, G, L, α, hφ, hUw, hGrad, hwC2, hwSmooth, hDclosed, hD, hLip, hw0,
    hPos, hDet, hClosed, hDecay, hPower, hα, hα1, hH, hA, hElliptic⟩

end KEBall
