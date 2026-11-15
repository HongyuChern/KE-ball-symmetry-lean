import KEBall.DirichletBoundaryWeakSobolev
import KEBall.DirichletAngularForcingWeakSobolev

/-! Combining the interior estimate and the differentiated angular equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Given the gain of two orders for forcing of order k, an interior
estimate at the next order suffices to propagate the global estimate. -/
theorem IsDirichletWeakSolution.hasDirichletWeakDerivativesL2_succ_of_interior
    {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    (k : ℕ)
    (hStep : ∀ (g : DirichletBallL2 n ℝ) (u : DirichletSobolev n),
      IsDirichletWeakSolution A g u → HasDirichletWeakDerivativesL2 (g : E n → ℝ) k →
      HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2))
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) (k + 1))
    (hInterior : ∀ is : List (Fin (2 * n)), is.length = k + 3 →
      ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
        tsupport (ψ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2) →
        dirichletDistributionalDerivative u (is.map b) ψ = ∫ x, ψ x * F x ∂ν[n]) :
    HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 3) := by
  have hg₀ : HasDirichletWeakDerivativesL2 (g : E n → ℝ) k :=
    ⟨hg.1, fun ds hs => hg.2 ds (hs.trans (Nat.le_succ _))⟩
  have hU := hStep g u hu hg₀
  have hAngle (S : E n →L[ℝ] E n) (hS : star S = -S) :
      ∃ v : DirichletSobolev n,
        HasDirichletWeakDerivativesL2 ((v : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2) ∧
        ∀ ψ : 𝓓B[n], (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]) := by
    obtain ⟨v, g', hg', hv, he⟩ :=
      hu.exists_angularDerivative_with_weakForcing hn b hA hAc hl hE hLipA hM₀ hM k hU hg S hS
    exact ⟨v, hStep g' v hv hg', he⟩
  apply HasDirichletWeakDerivativesL2.of_coordinate_tests hn b hU.1
  intro is hLen
  by_cases h : is.length ≤ k + 2
  · exact hU.2 (is.map b) (by simpa using h)
  have hlen : is.length = k + 3 := by omega
  obtain ⟨F₀, hF₀, he₀⟩ := hInterior is hlen
  have hShape : ∃ m j i : Fin (2 * n), ∃ ms : List (Fin (2 * n)),
      ms.length = k ∧ is = (m :: ms) ++ [j, i] := by
    cases is with
    | nil => simp at hlen
    | cons m rest =>
      cases hrev : rest.reverse with
      | nil =>
        have hz := congrArg List.length hrev
        simp at hz
        simp [hz] at hlen
      | cons i tail =>
        cases tail with
        | nil =>
          have hz := congrArg List.length hrev
          simp at hz
          simp [hz] at hlen
        | cons j ms =>
          have he : rest = ms.reverse ++ [j, i] := by
            have he' := congrArg List.reverse hrev
            simpa [List.reverse_cons, List.append_assoc] using he'
          refine ⟨m, j, i, ms.reverse, ?_, by rw [he]; rfl⟩
          simp [he] at hlen
          simpa using (show ms.length = k by omega)
  obtain ⟨m, j, i, ms, hms, hEq⟩ := hShape
  subst is
  obtain ⟨F₁, hF₁, he₁⟩ := hu.exists_dirichletDistributionalDerivativeL2_on_annulus
    hn b hAc hSym hl hE k hU hg hAngle (r := 1 / 8) (by norm_num) (b m) (ms.map b)
    (by simpa using hms) i j
  have he₁' (ψ : 𝓓B[n]) (hψ : tsupport (ψ : E n → ℝ) ⊆ {x | (1 / 8 : ℝ) < ‖x‖}) :
      dirichletDistributionalDerivative u (((m :: ms) ++ [j, i]).map b) ψ =
        ∫ x, ψ x * F₁ x ∂ν[n] := by
    simpa only [List.map_append, List.map_cons, List.map_nil] using he₁ ψ hψ
  exact exists_dirichletTestL2_of_interior_annulus hn _ (fun ψ φ =>
    dirichletDistributionalDerivative_add hn u _ ψ φ) hF₀ hF₁ he₀ he₁'

end KEBall
