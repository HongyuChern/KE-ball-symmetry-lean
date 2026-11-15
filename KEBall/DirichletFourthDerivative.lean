import KEBall.DirichletAngularThirdEntries

/-! Product rules for fixed-direction weak derivatives of matrix contractions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Differentiate the test multiplied by a matrix coefficient. -/
theorem dirichletTestFieldDerivative_coefficient_mul {n : ℕ}
    (ψ : 𝓓B[n]) (d e w : E n) {A : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (hD : ContDiff ℝ ∞ (fun x => fderiv ℝ A x d)) :
    dirichletTestFieldDerivative (dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hA e w))
      (fun _ => d) contDiff_const =
      dirichletTestMul (dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const)
        (contDiff_dirichletCoefficientEntry hA e w) +
      dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hD e w) := by
  apply TestFunction.ext
  intro x
  let c (y : E n) := inner ℝ w (A y e)
  have hc : ContDiff ℝ ∞ c := contDiff_dirichletCoefficientEntry hA e w
  have he : fderiv ℝ c x d = inner ℝ w (fderiv ℝ A x d e) := by
    let L : (E n →L[ℝ] E n) →L[ℝ] ℝ :=
      (innerSL ℝ w).comp (ContinuousLinearMap.apply ℝ (E n) e)
    change fderiv ℝ (L ∘ A) x d = _
    rw [(L.hasFDerivAt.comp x (hA.differentiable (by simp) x).hasFDerivAt).fderiv]
    rfl
  change fderiv ℝ (fun y => ψ y * c y) x d =
    fderiv ℝ (ψ : E n → ℝ) x d * c x + ψ x * inner ℝ w (fderiv ℝ A x d e)
  rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (hc.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul, he]
  ring

/-- A fixed derivative of the Hessian trace is the third derivative trace
plus the Hessian trace with differentiated coefficients. -/
theorem dirichletThirdDerivativeSlice_eq_neg_hessianTrace {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d : E n) {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) (hD : ContDiff ℝ ∞ (fun x => fderiv ℝ A x d)) :
    dirichletThirdDerivativeSlice b u ψ d hA =
      -dirichletHessianTrace b u (dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const) hA -
        dirichletHessianTrace b u ψ hD := by
  unfold dirichletThirdDerivativeSlice dirichletThirdDerivativeEntry dirichletHessianTrace
  simp_rw [dirichletTestFieldDerivative_coefficient_mul ψ d _ _ hA hD, dirichletHessianEntry_add hn,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  ring

/-- The fourth weak derivative tested in four fixed directions. -/
noncomputable def dirichletFourthDerivativeEntry {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d e v w : E n) : ℝ :=
  -dirichletThirdDerivativeEntry u (dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const) e v w

/-- The last two indices of a fourth weak derivative are contracted with
a smooth matrix while the first two directions stay fixed. -/
noncomputable def dirichletFourthDerivativeSlice {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d e : E n) {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) : ℝ :=
  ∑ i, ∑ j, dirichletFourthDerivativeEntry u
    (dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hA (b i) (b j))) d e (b j) (b i)

theorem dirichletFourthDerivativeEntry_comm₁₂ {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d e v w : E n) :
    dirichletFourthDerivativeEntry u ψ d e v w =
      dirichletFourthDerivativeEntry u ψ e d v w := by
  let ψd := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
  let ψe := dirichletTestFieldDerivative ψ (fun _ => e) contDiff_const
  have he : dirichletTestFieldDerivative ψd (fun _ => e) contDiff_const =
      dirichletTestFieldDerivative ψe (fun _ => d) contDiff_const := by
    apply TestFunction.ext
    intro x
    have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hs := (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast)
    change fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y d) x e =
      fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y e) x d
    rw [fderiv_clm_apply hd (differentiableAt_const d),
      fderiv_clm_apply hd (differentiableAt_const e)]
    simpa using hs.eq e d
  simp only [dirichletFourthDerivativeEntry, dirichletThirdDerivativeEntry]
  change -(-dirichletHessianEntry u (dirichletTestFieldDerivative ψd (fun _ => e) contDiff_const) v w) =
    -(-dirichletHessianEntry u (dirichletTestFieldDerivative ψe (fun _ => d) contDiff_const) v w)
  rw [he]

theorem dirichletFourthDerivativeEntry_comm₂₃ {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d e v w : E n) :
    dirichletFourthDerivativeEntry u ψ d e v w =
      dirichletFourthDerivativeEntry u ψ d v e w := by
  unfold dirichletFourthDerivativeEntry
  rw [dirichletThirdDerivativeEntry_comm₁₂ u _ e v w]

theorem dirichletFourthDerivativeEntry_comm₃₄ {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d e v w : E n) :
    dirichletFourthDerivativeEntry u ψ d e v w =
      dirichletFourthDerivativeEntry u ψ d e w v := by
  unfold dirichletFourthDerivativeEntry
  rw [dirichletThirdDerivativeEntry_comm₂₃ u _ e v w]

/-- The product rule for differentiating the matrix-contracted third derivative. -/
theorem dirichletFourthDerivativeSlice_eq_neg_thirdDerivativeSlice {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d e : E n) {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) (hD : ContDiff ℝ ∞ (fun x => fderiv ℝ A x d)) :
    dirichletFourthDerivativeSlice b u ψ d e hA =
      -dirichletThirdDerivativeSlice b u (dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const) e hA -
        dirichletThirdDerivativeSlice b u ψ e hD := by
  unfold dirichletFourthDerivativeSlice dirichletFourthDerivativeEntry dirichletThirdDerivativeSlice
  simp_rw [dirichletTestFieldDerivative_coefficient_mul ψ d _ _ hA hD, dirichletThirdDerivativeEntry_add hn,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  ring

/-- Expanding the two fixed derivatives gives the twice differentiated
Hessian trace and the three lower-order coefficient corrections. -/
theorem dirichletFourthDerivativeSlice_eq_hessianTrace {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d e : E n) {A : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A)
    (hD : ContDiff ℝ ∞ (fun x => fderiv ℝ A x d))
    (hE : ContDiff ℝ ∞ (fun x => fderiv ℝ A x e))
    (hDE : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ A y d) x e)) :
    let ψd := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
    let ψe := dirichletTestFieldDerivative ψ (fun _ => e) contDiff_const
    let ψde := dirichletTestFieldDerivative ψd (fun _ => e) contDiff_const
    dirichletFourthDerivativeSlice b u ψ d e hA =
      dirichletHessianTrace b u ψde hA + dirichletHessianTrace b u ψd hE +
        dirichletHessianTrace b u ψe hD + dirichletHessianTrace b u ψ hDE := by
  dsimp only
  rw [dirichletFourthDerivativeSlice_eq_neg_thirdDerivativeSlice hn b u ψ d e hA hD,
    dirichletThirdDerivativeSlice_eq_neg_hessianTrace hn b u _ e hA hE,
    dirichletThirdDerivativeSlice_eq_neg_hessianTrace hn b u ψ e hD hDE]
  ring

/-- Expand the first index of a fourth weak derivative against a smooth
field, with the other three indices held fixed. -/
theorem sum_dirichletFourthDerivativeEntry_eq_field {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (d e w : E n)
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (heF : ∀ τ : 𝓓B[n], dirichletThirdDerivativeEntry u τ d e w = ∫ x, τ x * F x ∂ν[n]) :
    (∑ i, dirichletFourthDerivativeEntry u
      (dirichletTestMul ψ ((innerSL ℝ (b i)).contDiff.comp hX)) (b i) d e w) =
      -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) *
        F x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let D (i : Fin (2 * n)) := dirichletTestFieldDerivative
    (dirichletTestMul ψ ((innerSL ℝ (b i)).contDiff.comp hX)) (fun _ => b i) contDiff_const
  have hI (i : Fin (2 * n)) : Integrable (fun x => D i x * F x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn (D i).continuous.continuousOn hF).integrable (by norm_num)
  simp only [dirichletFourthDerivativeEntry, heF]
  change (∑ i, -(∫ x, D i x * F x ∂ν[n])) = _
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hI i)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ i, D i x * F x) = _
    rw [← Finset.sum_mul]
    exact congrArg (fun a : ℝ => a * F x) (sum_dirichletTestFieldDerivative_mul_eq b ψ hX x)

/-- Each coordinate third derivative has a square-integrable fourth
contraction in every scaled tangential direction on the ball. -/
theorem IsDirichletWeakSolution.exists_dirichletFourthDerivative_tangentL2
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    (i j k : Fin (2 * n)) (z : E n) :
    let X (x : E n) := dirichletTangentTensor x z
    let hX : ContDiff ℝ ∞ X := contDiff_dirichletTangentTensor.clm_apply contDiff_const
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (∑ a, dirichletFourthDerivativeEntry u
        (dirichletTestMul ψ ((innerSL ℝ (b[n] a)).contDiff.comp hX))
          (b[n] a) (b[n] k) (b[n] j) (b[n] i)) = ∫ x, ψ x * T x ∂ν[n] := by
  let b := b[n]
  let X (x : E n) := dirichletTangentTensor x z
  let hX : ContDiff ℝ ∞ X := contDiff_dirichletTangentTensor.clm_apply contDiff_const
  obtain ⟨F, T, hF, hT, he⟩ := hu.exists_dirichletThirdDerivativeEntry_tangentDerivative
    hn hA hAc hSym hl hE hLipA hM₀ hM hG hRep i j k z
  refine ⟨T, hT, fun ψ => ?_⟩
  change (∑ a, dirichletFourthDerivativeEntry u
    (dirichletTestMul ψ ((innerSL ℝ (b a)).contDiff.comp hX)) (b a) (b k) (b j) (b i)) = _
  rw [sum_dirichletFourthDerivativeEntry_eq_field hn b u ψ (b k) (b j) (b i) hX hF
    (fun τ => (he τ).1), (he ψ).2]
  have hD (x : E n) : dirichletVectorDivergence b X x =
      (1 - (2 : ℝ) * n) * inner ℝ z x :=
    dirichletVectorDivergence_tangentTensor b z x
  simp_rw [hD, mul_comm (ψ _)]
  simp only [X, dirichletTangentTensor_apply]

end KEBall
