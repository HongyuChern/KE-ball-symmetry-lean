import KEBall.DirichletFourthAnnulus
import KEBall.DirichletWholeSecondForcing
import KEBall.DirichletWholeFourthDerivative

/-! Interior and global fourth weak derivatives on the Dirichlet ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private theorem tsupport_dirichletTestConstDerivative_subset {n : ℕ} (ψ : 𝓓B[n]) (d : E n) :
    tsupport ((dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const : 𝓓B[n]) : E n → ℝ) ⊆
      tsupport (ψ : E n → ℝ) :=
  tsupport_fderiv_apply_subset ℝ d

/-- Fourth weak coordinate derivatives have L² representatives on tests
supported near the center of the ball. -/
theorem IsDirichletWeakSolution.exists_dirichletFourthDerivativeEntryL2_interior
    {n : ℕ} (hn : 0 < n) (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x)
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hH : HasDirichletHessianEntriesL2 b u) (hT : HasDirichletThirdDerivativeEntriesL2 b u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G) (d e v w : E n) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      tsupport (ψ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2) →
      dirichletFourthDerivativeEntry u ψ d e v w = ∫ x, ψ x * F x ∂ν[n] := by
  obtain ⟨χ, η, B, K, hB, f', hχ, hη, hBc, hBE, hLip, hD₁, hD₂, hSupp, hf', hEq⟩ :=
    hu.exists_interior_cutoff_with_derivativeSupport hn b hA hSym hE
  have hD₃ (a c m : E n) : MemLp (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ B z a) y c) x m) ⊤ (volume0 n) := by
    have h₁ : ContDiff ℝ ∞ (fun x => fderiv ℝ B x a) :=
      (hBc.fderiv_right (by simp)).clm_apply contDiff_const
    have h₂ : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ B y a) x c) :=
      (h₁.fderiv_right (by simp)).clm_apply contDiff_const
    have h₃ : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y =>
        fderiv ℝ (fun z => fderiv ℝ B z a) y c) x m) :=
      (h₂.fderiv_right (by simp)).clm_apply contDiff_const
    exact h₃.continuous.memLp_top_of_hasCompactSupport
      (((hSupp a).fderiv_apply ℝ c).fderiv_apply ℝ m) _
  obtain ⟨H, J, L, hH', hJ, hL⟩ := hEq.exists_thirdGradientWeakDerivative b v e d
    hBc hD₁ hD₂ hD₃ hl (Eventually.of_forall hBE) hLip
    (fun a => exists_dirichletCutoffForcing_weakDerivative_with_weakGradient hn b a hA hH hT
      hG hRep χ η hη f' hf')
  refine ⟨fun x => inner ℝ w (L x), ((Lp.memLp L).const_inner w).restrict _, fun ψ hψ => ?_⟩
  let τ := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
  let σ := dirichletTestFieldDerivative τ (fun _ => e) contDiff_const
  let φ : 𝓓E[n] := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_univ _⟩
  let ξ : 𝓓E[n] := ⟨τ, τ.contDiff, τ.hasCompactSupport, subset_univ _⟩
  let ζ : 𝓓E[n] := ⟨σ, σ.contDiff, σ.hasCompactSupport, subset_univ _⟩
  have hI : (∫ x, ψ x * inner ℝ w (L x) ∂ν[n]) =
      ∫ x, φ x * inner ℝ w (L x) ∂volume0 n := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (ψ.tsupport_subset hs)), zero_mul]
  have hTransfer := integral_dirichletCutoff_gradient_on_interior u χ σ hχ
    ((tsupport_dirichletTestConstDerivative_subset τ e).trans
      ((tsupport_dirichletTestConstDerivative_subset ψ d).trans hψ)) v w
  have hξ (x : E n) : fderiv ℝ (φ : E n → ℝ) x d = ξ x := rfl
  have hζ (x : E n) : fderiv ℝ (ξ : E n → ℝ) x e = ζ x := rfl
  have heL := hL φ w
  have heJ := hJ ξ w
  have heH := hH' ζ w
  rw [hI, heL]
  simp only [hξ]
  rw [heJ]
  simp only [hζ]
  rw [heH]
  exact congrArg (fun x : ℝ => - - -x) hTransfer.symm

/-- The fourth weak coordinate derivatives of the Dirichlet solution
are in L² throughout the ball for a smooth forcing. -/
theorem IsDirichletWeakSolution.exists_dirichletFourthDerivativeEntryL2
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G) (i j k m : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      dirichletFourthDerivativeEntry u ψ (b[n] m) (b[n] k) (b[n] j) (b[n] i) =
        ∫ x, ψ x * F x ∂ν[n] := by
  let b := b[n]
  have hH : HasDirichletHessianEntriesL2 b u :=
    exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE hLipA hM₀ hM hu
  have hT : HasDirichletThirdDerivativeEntriesL2 b u :=
    hu.exists_dirichletThirdDerivativeEntryL2 hn hA hAc hSym hl hE hLipA hM₀ hM hG hRep
  obtain ⟨F₀, hF₀, he₀⟩ := hu.exists_dirichletFourthDerivativeEntryL2_interior hn b hAc
    (fun x _ => hSym x) hl hE hH hT hG hRep (b m) (b k) (b j) (b i)
  obtain ⟨F₁, hF₁, he₁⟩ := hu.exists_dirichletFourthDerivativeEntryL2_on_annulus hn hA hAc
    hSym hl hE hLipA hM₀ hM hG hRep (r := 1 / 8) (by norm_num) i j k m
  exact exists_dirichletTestL2_of_interior_annulus hn _ (fun ψ φ =>
    dirichletFourthDerivativeEntry_add hn u ψ φ (b m) (b k) (b j) (b i)) hF₀ hF₁ he₀ he₁

end KEBall
