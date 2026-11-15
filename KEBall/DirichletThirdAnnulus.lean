import KEBall.DirichletThirdSlice
import KEBall.DirichletMatrixAnnulus

/-! Third weak derivatives on annuli of the Dirichlet ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

/-- A square-integrable representative of a third derivative contraction on
tests supported in a subset of the ball. -/
abbrev HasDirichletThirdDerivativeSliceL2On {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (d : E n) (s : Set (E n)) {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) : Prop :=
  HasDirichletMatrixContractionL2On b (fun ψ v w => dirichletThirdDerivativeEntry u ψ d v w) s hB

/-- The differentiated elliptic equation and tangential estimates recover the
complete third derivative contraction on every annulus away from the center. -/
theorem IsDirichletWeakSolution.hasDirichletThirdDerivativeSliceL2_on_annulus_of_weakGradient
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hg : HasDirichletWeakGradientL2 (g : E n → ℝ))
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    (hBAdj : ContDiff ℝ ∞ (fun x => (B x).adjoint)) {r : ℝ} (hr : 0 < r)
    (k : Fin (2 * n)) :
    HasDirichletThirdDerivativeSliceL2On b[n] u (b[n] k) {x | r < ‖x‖} hB := by
  let b := b[n]
  let d := b k
  let s : Set (E n) := {x | r < ‖x‖}
  have hH : HasDirichletHessianEntriesL2 b u :=
    exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE hLipA hM₀ hM hu
  obtain ⟨F, hF, heF⟩ := hu.exists_dirichletThirdDerivativeTraceL2_of_weakGradient hn hAc hH hg
    (contDiff_const (c := d))
  have hTrace : HasDirichletThirdDerivativeSliceL2On b u d s hAc := by
    refine ⟨F, hF, fun ψ _ => ?_⟩
    change dirichletThirdDerivativeSlice b u ψ d hAc = _
    rw [← dirichletThirdDerivativeTrace_const_basis b u ψ k]
    exact heF ψ
  have hTan := exists_dirichletHessianEntry_tangentDerivative_of_angular_forcing hn b hA hAc
    hSym hl hE hLipA hM₀ hM hu (hg.exists_angularDerivative hn g)
  have hTangent {D : E n → E n →L[ℝ] E n} (hD : ContDiff ℝ ∞ D) :
      HasDirichletThirdDerivativeSliceL2On b u d s (contDiff_dirichletTangentTensor.clm_comp hD) := by
    obtain ⟨T, hT, heT⟩ := exists_dirichletThirdDerivativeSlice_tangentComp hn b u d hTan hD
    exact ⟨T, hT, fun ψ _ => heT ψ⟩
  exact hasDirichletMatrixContractionL2On_annulus hn b
    (fun ψ v w => dirichletThirdDerivativeEntry u ψ d v w)
    (fun ψ φ v w => dirichletThirdDerivativeEntry_add hn u ψ φ d v w)
    (fun ψ v w => dirichletThirdDerivativeEntry_comm₂₃ u ψ d v w)
    hAc hB hSym hBAdj hl hr hE hTrace hTangent

/-- Each third weak coordinate derivative is represented by an L² function
on tests supported in any annulus away from the center of the ball. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeEntryL2_on_annulus_of_weakGradient
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hg : HasDirichletWeakGradientL2 (g : E n → ℝ)) {r : ℝ} (hr : 0 < r)
    (i j k : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ {x | r < ‖x‖} →
      dirichletThirdDerivativeEntry u ψ (b[n] k) (b[n] j) (b[n] i) = ∫ x, ψ x * F x ∂ν[n] := by
  let B (_ : E n) := rankOne ℝ (b[n] j) (b[n] i)
  let hB : ContDiff ℝ ∞ B := contDiff_const
  have hBAdj : ContDiff ℝ ∞ (fun x => (B x).adjoint) := by
    change ContDiff ℝ ∞ (fun _ : E n => (rankOne ℝ (b[n] j) (b[n] i)).adjoint)
    exact contDiff_const
  obtain ⟨F, hF, he⟩ := hu.hasDirichletThirdDerivativeSliceL2_on_annulus_of_weakGradient hn hA hAc hSym
    hl hE hLipA hM₀ hM hg hB hBAdj hr k
  refine ⟨F, hF, fun ψ hψ => ?_⟩
  rw [← dirichletThirdDerivativeSlice_rankOne_basis b[n] u ψ (b[n] k) i j]
  exact he ψ hψ

/-- The differentiated elliptic equation and tangential estimates recover the
complete third derivative contraction on every annulus away from the center. -/
theorem IsDirichletWeakSolution.hasDirichletThirdDerivativeSliceL2_on_annulus
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    (hBAdj : ContDiff ℝ ∞ (fun x => (B x).adjoint)) {r : ℝ} (hr : 0 < r)
    (k : Fin (2 * n)) :
    HasDirichletThirdDerivativeSliceL2On b[n] u (b[n] k) {x | r < ‖x‖} hB :=
  hu.hasDirichletThirdDerivativeSliceL2_on_annulus_of_weakGradient hn hA hAc hSym
    hl hE hLipA hM₀ hM (HasDirichletWeakGradientL2.of_smooth_ae hn hG hRep) hB hBAdj hr k

/-- Each third weak coordinate derivative is represented by an L² function
on tests supported in any annulus away from the center of the ball. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeEntryL2_on_annulus
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G) {r : ℝ} (hr : 0 < r)
    (i j k : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ {x | r < ‖x‖} →
      dirichletThirdDerivativeEntry u ψ (b[n] k) (b[n] j) (b[n] i) = ∫ x, ψ x * F x ∂ν[n] :=
  hu.exists_dirichletThirdDerivativeEntryL2_on_annulus_of_weakGradient hn hA hAc hSym
    hl hE hLipA hM₀ hM (HasDirichletWeakGradientL2.of_smooth_ae hn hG hRep) hr i j k

end KEBall
