import KEBall.DirichletFourthTangentMatrix

/-! Fourth weak derivatives in the exterior annuli of the Dirichlet ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- All fourth weak coordinate derivatives have L² representatives on
every annulus separated from the center of the Dirichlet ball. -/
theorem IsDirichletWeakSolution.exists_dirichletFourthDerivativeEntryL2_on_annulus
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    {r : ℝ} (hr : 0 < r) (i j k m : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      tsupport (ψ : E n → ℝ) ⊆ {x | r < ‖x‖} →
      dirichletFourthDerivativeEntry u ψ (b[n] m) (b[n] k) (b[n] j) (b[n] i) =
        ∫ x, ψ x * F x ∂ν[n] := by
  let b := b[n]
  let entry (ψ : 𝓓B[n]) (v w : E n) :=
    dirichletFourthDerivativeEntry u ψ (b m) (b k) v w
  have hH : HasDirichletHessianEntriesL2 b u :=
    exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE hLipA hM₀ hM hu
  have hT : HasDirichletThirdDerivativeEntriesL2 b u :=
    hu.exists_dirichletThirdDerivativeEntryL2 hn hA hAc hSym hl hE hLipA hM₀ hM hG hRep
  obtain ⟨R, hR, heR⟩ := hu.exists_dirichletFourthDerivativeSliceL2 hn b hAc hH hT hG hRep m k
  have hTrace : HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖} hAc :=
    ⟨R, hR, fun ψ _ => heR ψ⟩
  have hTan {D : E n → E n →L[ℝ] E n} (hD : ContDiff ℝ ∞ D) :
      HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖}
        (contDiff_dirichletTangentTensor.clm_comp hD) := by
    obtain ⟨T, hT, heT⟩ := hu.exists_dirichletFourthDerivativeSlice_tangentCompL2
      hn hA hAc hSym hl hE hLipA hM₀ hM hG hRep m k hD
    exact ⟨T, hT, fun ψ _ => heT ψ⟩
  let B (_ : E n) := rankOne ℝ (b j) (b i)
  let hB : ContDiff ℝ ∞ B := contDiff_const
  have hBAdj : ContDiff ℝ ∞ (fun x => (B x).adjoint) := by
    change ContDiff ℝ ∞ (fun _ : E n => (rankOne ℝ (b j) (b i)).adjoint)
    exact contDiff_const
  obtain ⟨F, hF, heF⟩ := hasDirichletMatrixContractionL2On_annulus hn b entry
    (fun ψ φ v w => dirichletFourthDerivativeEntry_add hn u ψ φ (b m) (b k) v w)
    (fun ψ v w => dirichletFourthDerivativeEntry_comm₃₄ u ψ (b m) (b k) v w)
    hAc hB hSym hBAdj hl hr hE hTrace hTan
  refine ⟨F, hF, fun ψ hψ => ?_⟩
  exact (dirichletMatrixContraction_rankOne_basis b entry ψ i j
    (fun v w => dirichletFourthDerivativeEntry_zero u (b m) (b k) v w)).symm.trans (heF ψ hψ)

end KEBall
