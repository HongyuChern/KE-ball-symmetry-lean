import KEBall.DirichletCofactorHessian
import KEBall.DirichletSobolevGraph

/-! Bounded finite-order solution operators for the cofactor linearization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff NNReal

namespace KEBall

/-- The actual cofactor equation has a bounded linear weak solution
operator gaining two orders in the closed-ball Sobolev graph norms. -/
theorem exists_dirichletCofactorSobolevInverse {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    (k : ℕ) :
    ∃ (S : DirichletBallL2 n ℝ →L[ℝ] DirichletSobolev n)
      (R : dirichletSobolevJetGraph (k := k) b →L[ℝ]
        dirichletSobolevJetGraph (k := k + 2) b),
      (∀ g, IsDirichletWeakSolution (dirichletCofactorOperator u) g (S g)) ∧
      ∀ z, (R z).val.1 = (S z.val.1 : DirichletBallL2Pair n).fst := by
  obtain ⟨S, hS⟩ := exists_weakCofactorDirichletSolutionCLM hn hu huP ha hl hDensity hElliptic
  let T : DirichletBallL2 n ℝ →L[ℝ] DirichletBallL2 n ℝ :=
    ((WithLp.fstL 2 ℝ _ _).comp (dirichletSobolevSubmodule n).subtypeL).comp S
  have hGain (g : DirichletBallL2 n ℝ) (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) k) :
      HasDirichletWeakDerivativesL2 (T g : E n → ℝ) (k + 2) := by
    obtain ⟨w, hw, hReg⟩ := exists_weakCofactorDirichletSolution_with_weakDerivatives hn
      hu huP ha hl hDensity hElliptic k g hg
    rw [(hS g).2 w hw] at hReg
    exact hReg
  obtain ⟨R, hR⟩ := exists_dirichletSobolevJetGraph_lift hn b T hGain
  exact ⟨S, R, fun g => (hS g).1, hR⟩

end KEBall
