import KEBall.DirichletDivergenceWeakGradient

/-! Third weak derivatives of the angular Dirichlet solution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

/-- When the forcing and its angular derivative have L² weak gradients,
the angular derivative of the solution has third weak derivatives in L². -/
theorem exists_dirichletAngularDerivative_with_L2ThirdDerivative {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g gS : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hg : HasDirichletWeakGradientL2 (g : E n → ℝ))
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    (hgS : HasDirichletWeakGradientL2 (gS : E n → ℝ))
    (heS : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * gS x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n])) :
    ∃ (v : DirichletSobolev n) (g' : DirichletBallL2 n ℝ),
      (∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n])) ∧
      IsDirichletWeakSolution A g' v ∧ HasDirichletThirdDerivativeEntriesL2 b[n] v := by
  have hAE := (ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)).mono hE
  obtain ⟨v, hv⟩ :=
    exists_dirichletSobolev_angularDerivative_L2 hn hA hl hAE hLipA hM₀ hM hu S hS
  have hH := exists_dirichletHessianEntryL2 hn b[n] hA hAc hSym hl hE hLipA hM₀ hM hu
  have hT := hu.exists_dirichletThirdDerivativeEntryL2_of_weakGradient
    hn hA hAc hSym hl hE hLipA hM₀ hM hg
  obtain ⟨D, hD, heD⟩ := exists_dirichletGradientDivergence_with_weakGradient hn b[n] u hH hT
    (contDiff_dirichletAngularCoefficient hAc S)
  have hEq := hu.angularDerivative_of_forcing hn b[n] hA hAc S hS heS v hv heD
  have hF : HasDirichletWeakGradientL2 ((gS + D : DirichletBallL2 n ℝ) : E n → ℝ) :=
    (hgS.add hn (Lp.memLp gS) (Lp.memLp D) hD).congr (Lp.coeFn_add gS D).symm
  exact ⟨v, gS + D, hv, hEq,
    hEq.exists_dirichletThirdDerivativeEntryL2_of_weakGradient hn hA hAc hSym hl hE hLipA hM₀ hM hF⟩

end KEBall
