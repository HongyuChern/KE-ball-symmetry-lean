import KEBall.DirichletGlobalWeakFourthDerivative
import KEBall.DirichletWeakSobolev

/-! Fourth-order weak Sobolev regularity in every real direction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- A weak solution on the unit ball with smooth forcing has every real
weak derivative through order four in L². -/
theorem IsDirichletWeakSolution.hasDirichletWeakDerivativesL2_four
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G) :
    HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) 4 := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let f := (u : DirichletBallL2Pair n).fst
  let U := (u : DirichletBallL2Pair n).snd
  apply HasDirichletWeakDerivativesL2.of_coordinate_tests hn b (Lp.memLp f)
  intro ds hds
  match ds with
  | [] => exact ⟨f, Lp.memLp f, fun _ => rfl⟩
  | [i] => exact ⟨fun x => inner ℝ (b i) (U x), (Lp.memLp U).const_inner (b i),
      dirichletDistributionalDerivative_singleton u (b i)⟩
  | [j, i] =>
      obtain ⟨F, hF, he⟩ := exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE
        hLipA hM₀ hM hu i j
      exact ⟨F, hF, fun ψ => (dirichletDistributionalDerivative_pair u (b j) (b i) ψ).trans (he ψ)⟩
  | [k, j, i] =>
      obtain ⟨F, hF, he⟩ := hu.exists_dirichletThirdDerivativeEntryL2 hn hA hAc hSym hl hE
        hLipA hM₀ hM hG hRep i j k
      exact ⟨F, hF, fun ψ =>
        (dirichletDistributionalDerivative_triple u (b k) (b j) (b i) ψ).trans (he ψ)⟩
  | [m, k, j, i] =>
      obtain ⟨F, hF, he⟩ := hu.exists_dirichletFourthDerivativeEntryL2 hn hA hAc hSym hl hE
        hLipA hM₀ hM hG hRep i j k m
      exact ⟨F, hF, fun ψ =>
        (dirichletDistributionalDerivative_quadruple u (b m) (b k) (b j) (b i) ψ).trans (he ψ)⟩
  | m :: k :: j :: i :: a :: ds =>
      simp only [List.length_cons] at hds
      omega

end KEBall
