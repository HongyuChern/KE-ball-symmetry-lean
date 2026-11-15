import KEBall.DirichletAngularThirdDerivative

/-! Angular derivatives of third weak derivative entries. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

private theorem exists_dirichletThirdDerivativeEntryL2_of_last_two_basis {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hH : HasDirichletHessianEntriesL2 b u) (hT : HasDirichletThirdDerivativeEntriesL2 b u)
    (d : E n) (i j : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeEntry u ψ d (b j) (b i) = ∫ x, ψ x * F x ∂ν[n] := by
  obtain ⟨G, hG, heG⟩ := hH i j
  obtain ⟨F, hF, heF⟩ := hasDirichletWeakGradientL2_of_hessianEntry hn b u hT i j hG heG d
  exact ⟨F, hF, fun ψ =>
    (dirichletThirdDerivativeEntry_eq_integral u (b j) (b i) heG ψ d).trans (heF ψ).symm⟩

private theorem dirichletThirdDerivativeEntry_comm₁₃ {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d e w : E n) :
    dirichletThirdDerivativeEntry u ψ d e w = dirichletThirdDerivativeEntry u ψ w e d := by
  rw [dirichletThirdDerivativeEntry_comm₁₂ u ψ d e w,
    dirichletThirdDerivativeEntry_comm₂₃ u ψ e d w,
    dirichletThirdDerivativeEntry_comm₁₂ u ψ e w d]

/-- Commuting an angular derivative past three fixed derivatives gives the
three changes of direction from differentiating the linear vector field. -/
theorem dirichletThirdDerivativeEntry_angular_commutator {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (u v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d e w : E n) :
    let η := dirichletTestFieldDerivative ψ S S.contDiff
    (-dirichletThirdDerivativeEntry u η d e w) =
      dirichletThirdDerivativeEntry v ψ d e w - dirichletThirdDerivativeEntry u ψ (S d) e w -
        dirichletThirdDerivativeEntry u ψ d (S e) w - dirichletThirdDerivativeEntry u ψ d e (S w) := by
  let η := dirichletTestFieldDerivative ψ S S.contDiff
  let ξ := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
  let τ := dirichletTestFieldDerivative ξ S S.contDiff
  let σ := dirichletTestFieldDerivative ψ (fun _ => S d) contDiff_const
  have hTest : dirichletTestFieldDerivative η (fun _ => d) contDiff_const = τ + σ := by
    apply TestFunction.ext
    intro x
    have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hs := (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast)
    change fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y (S y)) x d =
      fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y d) x (S x) + fderiv ℝ (ψ : E n → ℝ) x (S d)
    rw [fderiv_clm_apply hd S.differentiableAt, fderiv_clm_apply hd (differentiableAt_const d)]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.fderiv, fderiv_fun_const, Pi.zero_apply, zero_apply, map_zero, zero_add]
    rw [hs.eq d (S x), add_comm]
  have he := dirichletHessianEntry_angular_commutator hn S u v hv ξ e w
  change -dirichletHessianEntry u τ e w = _ at he
  change -(-dirichletHessianEntry u (dirichletTestFieldDerivative η (fun _ => d) contDiff_const) e w) =
    (-dirichletHessianEntry v ξ e w) - (-dirichletHessianEntry u σ e w) -
      (-dirichletHessianEntry u ξ (S e) w) - (-dirichletHessianEntry u ξ e (S w))
  rw [hTest, dirichletHessianEntry_add hn]
  linarith only [he]

/-- An angular derivative of a third weak coordinate derivative is in L²
if both the original and angular solutions have third derivatives in L². -/
theorem exists_dirichletThirdDerivativeEntry_angularDerivative_L2 {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (S : E n →L[ℝ] E n) (u v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (hH : HasDirichletHessianEntriesL2 b u) (hU : HasDirichletThirdDerivativeEntriesL2 b u)
    (hV : HasDirichletThirdDerivativeEntriesL2 b v) (i j k : Fin (2 * n))
    {F : E n → ℝ}
    (heF : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeEntry u ψ (b k) (b j) (b i) = ∫ x, ψ x * F x ∂ν[n]) :
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * T x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * F x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hOther := exists_dirichletThirdDerivativeEntryL2_of_last_two_basis hn b u hH hU
  obtain ⟨G, hG, heG⟩ := hV i j k
  obtain ⟨H, hH₂, heH⟩ := hOther (S (b k)) i j
  obtain ⟨J, hJ, heJ⟩ := hOther (S (b j)) i k
  obtain ⟨L, hL, heL⟩ := hOther (S (b i)) k j
  refine ⟨G - H - J - L, ((hG.sub hH₂).sub hJ).sub hL, fun ψ => ?_⟩
  let η := dirichletTestFieldDerivative ψ S S.contDiff
  have he := dirichletThirdDerivativeEntry_angular_commutator hn S u v hv ψ (b k) (b j) (b i)
  change -dirichletThirdDerivativeEntry u η (b k) (b j) (b i) = _ at he
  rw [heF η, heG ψ, heH ψ, dirichletThirdDerivativeEntry_comm₁₂ u ψ (b k) (S (b j)) (b i),
    heJ ψ, dirichletThirdDerivativeEntry_comm₁₃ u ψ (b k) (b j) (S (b i)), heL ψ] at he
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  have hGH : Integrable (fun x => ψ x * G x - ψ x * H x) ν[n] :=
    (hI hG).sub (hI hH₂)
  have hGHJ : Integrable (fun x => ψ x * G x - ψ x * H x - ψ x * J x) ν[n] :=
    hGH.sub (hI hJ)
  simp_rw [Pi.sub_apply, mul_sub]
  rw [integral_sub hGHJ (hI hL), integral_sub hGH (hI hJ), integral_sub (hI hG) (hI hH₂)]
  exact he.symm

/-- With smooth forcing, every third weak coordinate entry has an L²
derivative along the scaled tangential projection on the entire ball. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeEntry_tangentDerivative
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    (i j k : Fin (2 * n)) (z : E n) :
    ∃ F T : E n → ℝ, MemLp F 2 ν[n] ∧ MemLp T 2 ν[n] ∧
      ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        dirichletThirdDerivativeEntry u ψ (b[n] k) (b[n] j) (b[n] i) =
          (∫ x, ψ x * F x ∂ν[n]) ∧
        (∫ x, ψ x * T x ∂ν[n]) =
          -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • z - inner ℝ z x • x) +
            ((1 - (2 : ℝ) * n) * inner ℝ z x) * ψ x) * F x ∂ν[n]) := by
  let b := b[n]
  have hg := HasDirichletWeakGradientL2.of_smooth_ae hn hG hRep
  have hH := exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE hLipA hM₀ hM hu
  have hU := hu.exists_dirichletThirdDerivativeEntryL2_of_weakGradient
    hn hA hAc hSym hl hE hLipA hM₀ hM hg
  obtain ⟨F, hF, heF⟩ := hU i j k
  have hAngular (S : E n →L[ℝ] E n) (hS : star S = -S) :
      ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, ψ x * T x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * F x ∂ν[n]) := by
    obtain ⟨gS, hRepS, heS⟩ := exists_dirichletForcing_angularDerivative_of_smooth hn g hG hRep S hS
    have hGS : ContDiff ℝ ∞ (fun x => fderiv ℝ G x (S x)) :=
      (hG.fderiv_right (by simp)).clm_apply S.contDiff
    have hgS := HasDirichletWeakGradientL2.of_smooth_ae hn hGS hRepS
    obtain ⟨v, _, hv, _, hV⟩ := exists_dirichletAngularDerivative_with_L2ThirdDerivative
      hn hA hAc hSym hl hE hLipA hM₀ hM hu hg S hS hgS heS
    exact exists_dirichletThirdDerivativeEntry_angularDerivative_L2 hn b S u v hv
      hH hU hV i j k heF
  obtain ⟨T, hT, heT⟩ := exists_memLp_dirichletTangentDerivative hn hF z hAngular
  exact ⟨F, T, hF, hT, fun ψ => ⟨heF ψ, heT ψ⟩⟩

end KEBall
