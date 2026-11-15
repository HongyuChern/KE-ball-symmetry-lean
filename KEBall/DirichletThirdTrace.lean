import KEBall.DirichletWeakGradientL2

/-! Differentiating the elliptic contraction of the weak Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

/-- The divergence of a smooth vector field times a compactly supported test. -/
noncomputable def dirichletTestDivergence {n : ℕ} (ψ : 𝓓(dirichletBallOpens n, ℝ))
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {X : E n → E n}
    (hX : ContDiff ℝ ∞ X) : 𝓓(dirichletBallOpens n, ℝ) :=
  dirichletTestFieldDerivative ψ X hX +
    dirichletTestMul ψ (contDiff_dirichletVectorDivergence b hX)

theorem dirichletTestDivergence_apply {n : ℕ} (ψ : 𝓓(dirichletBallOpens n, ℝ))
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {X : E n → E n}
    (hX : ContDiff ℝ ∞ X) (x : E n) :
    dirichletTestDivergence ψ b hX x =
      fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x :=
  rfl

/-- The weak third derivative with the first index contracted against a vector
field and the other two contracted against a matrix field. -/
noncomputable def dirichletThirdDerivativeTrace {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) {X : E n → E n} (hX : ContDiff ℝ ∞ X) : ℝ :=
  ∑ i, ∑ j, ∑ k, dirichletThirdDerivativeEntry u
    (dirichletTestMul (dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hA (b i) (b j)))
      ((innerSL ℝ (b k)).contDiff.comp hX)) (b k) (b j) (b i)

private theorem dirichletTestDivergence_mul_apply {n : ℕ}
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {c : E n → ℝ} (hc : ContDiff ℝ ∞ c) {X : E n → E n} (hX : ContDiff ℝ ∞ X) (x : E n) :
    dirichletTestDivergence (dirichletTestMul ψ hc) b hX x =
      dirichletTestDivergence ψ b hX x * c x + ψ x * fderiv ℝ c x (X x) := by
  simp only [dirichletTestDivergence_apply, dirichletTestMul_apply]
  change fderiv ℝ (fun y => ψ y * c y) x (X x) + _ = _
  rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (hc.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The derivative of the Hessian trace differs from the contraction of the
third derivative by an L² term differentiating the matrix coefficients. -/
theorem exists_dirichletThirdDerivativeTrace_correction {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hH : HasDirichletHessianEntriesL2 b u)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) :
    ∃ R : E n → ℝ, MemLp R 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeTrace b u ψ hA hX =
        -dirichletHessianTrace b u (dirichletTestDivergence ψ b hX) hA -
          ∫ x, ψ x * R x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  unfold HasDirichletHessianEntriesL2 at hH
  choose F hF heF using hH
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (A x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hA (b i) (b j)
  let dc (i j : Fin (2 * n)) (x : E n) := fderiv ℝ (c i j) x (X x)
  have hdc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (dc i j) :=
    ((hc i j).fderiv_right (by simp)).clm_apply hX
  let R (i j : Fin (2 * n)) (x : E n) := dc i j x * F i j x
  have hR (i j : Fin (2 * n)) : MemLp (R i j) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hdc i j).continuous.continuousOn (hF i j)
  refine ⟨fun x => ∑ i, ∑ j, R i j x,
    memLp_finsetSum Finset.univ (fun i _ => memLp_finsetSum Finset.univ (fun j _ => hR i j)), ?_⟩
  intro ψ
  let τ := dirichletTestDivergence ψ b hX
  have hI (φ : 𝓓(dirichletBallOpens n, ℝ)) {f : E n → ℝ} (hf : MemLp f 2 ν[n]) :
      Integrable (fun x => φ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hf).integrable (by norm_num)
  have hTerm (i j : Fin (2 * n)) :
      (∑ k, dirichletThirdDerivativeEntry u
        (dirichletTestMul (dirichletTestMul ψ (hc i j))
          ((innerSL ℝ (b k)).contDiff.comp hX)) (b k) (b j) (b i)) =
        -dirichletHessianEntry u (dirichletTestMul τ (hc i j)) (b j) (b i) -
          ∫ x, ψ x * R i j x ∂ν[n] := by
    rw [sum_dirichletThirdDerivativeEntry_eq_field hn b u _ _ _ hX (hF i j) (heF i j),
      heF i j]
    have hInt := integral_add (hI (dirichletTestMul τ (hc i j)) (hF i j)) (hI ψ (hR i j))
    rw [sub_eq_add_neg, ← neg_add, ← hInt]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change dirichletTestDivergence (dirichletTestMul ψ (hc i j)) b hX x * F i j x =
        (τ x * c i j x) * F i j x + ψ x * R i j x
      rw [dirichletTestDivergence_mul_apply]
      dsimp only [R, dc, τ]
      ring
  change (∑ i, ∑ j, ∑ k, dirichletThirdDerivativeEntry u
    (dirichletTestMul (dirichletTestMul ψ (hc i j)) ((innerSL ℝ (b k)).contDiff.comp hX))
      (b k) (b j) (b i)) =
    -(∑ i, ∑ j, dirichletHessianEntry u (dirichletTestMul τ (hc i j)) (b j) (b i)) -
      ∫ x, ψ x * (∑ i, ∑ j, R i j x) ∂ν[n]
  simp_rw [hTerm, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI ψ (hR i j)))]
  exact Finset.sum_congr rfl (fun i _ =>
    (integral_finsetSum _ (fun j _ => hI ψ (hR i j))).symm)

private theorem exists_dirichletGradientPairing_fieldDerivative {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hH : HasDirichletHessianEntriesL2 b u)
    {Y X : E n → E n} (hY : ContDiff ℝ ∞ Y) (hX : ContDiff ℝ ∞ X) :
    ∃ R : E n → ℝ, MemLp R 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, dirichletTestDivergence ψ b hX x *
        inner ℝ (Y x) ((u : DirichletBallL2Pair n).snd x) ∂ν[n]) =
      ∫ x, ψ x * R x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let U := (u : DirichletBallL2Pair n).snd
  let a (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (Y x)
  let W (x : E n) := inner ℝ (Y x) (U x)
  have hW : MemLp W 2 ν[n] := by
    have he (x : E n) : (∑ i, a i x * inner ℝ (b i) (U x)) = W x := by
      change _ = inner ℝ (Y x) (U x)
      rw [← b.sum_repr' (Y x), sum_inner]
      simp only [real_inner_smul_left, a]
    refine MemLp.ae_eq (Eventually.of_forall he)
      (memLp_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => ?_)
    exact memLp_dirichlet_mul_of_continuousOn ((innerSL ℝ (b i)).continuous.comp
      hY.continuous).continuousOn ((Lp.memLp U).const_inner (b i))
  let divX := dirichletVectorDivergence b X
  let V (x : E n) := divX x * W x
  have hV : MemLp V 2 ν[n] := memLp_dirichlet_mul_of_continuousOn
    (contDiff_dirichletVectorDivergence b hX).continuous.continuousOn hW
  obtain ⟨d, hd⟩ := exists_dirichletGradientDivergence_L2 hn b u hH (contDiff_rankOne_real hX hY)
  refine ⟨V - d, hV.sub (Lp.memLp d), fun ψ => ?_⟩
  let τ := dirichletTestFieldDerivative ψ X hX
  have hI (φ : 𝓓(dirichletBallOpens n, ℝ)) {f : E n → ℝ} (hf : MemLp f 2 ν[n]) :
      Integrable (fun x => φ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hf).integrable (by norm_num)
  have hD := hd ψ
  change (∫ x, fderiv ℝ (ψ : E n → ℝ) x (rankOne ℝ (X x) (Y x) (U x)) ∂ν[n]) = _ at hD
  simp_rw [rankOne_apply, map_smul, smul_eq_mul, mul_comm (inner ℝ (Y _) (U _))] at hD
  have he (x : E n) : dirichletTestDivergence ψ b hX x * W x =
      τ x * W x + ψ x * V x := by
    rw [dirichletTestDivergence_apply, add_mul, mul_assoc]
    rfl
  change (∫ x, dirichletTestDivergence ψ b hX x * W x ∂ν[n]) = _
  simp_rw [he, Pi.sub_apply, mul_sub]
  rw [integral_add (hI τ hW) (hI ψ hV), integral_sub (hI ψ hV) (hI ψ (Lp.memLp d))]
  change (∫ x, fderiv ℝ (ψ : E n → ℝ) x (X x) * W x ∂ν[n]) + _ = _
  rw [show (∫ x, fderiv ℝ (ψ : E n → ℝ) x (X x) * W x ∂ν[n]) =
    -(∫ x, ψ x * d x ∂ν[n]) from hD]
  ring

/-- For forcing with an L² weak gradient, the weak derivative of the
elliptic Hessian trace along every smooth vector field is in L² after
subtracting the derivative of its coefficients. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeTraceL2_of_weakGradient {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A g u) (hH : HasDirichletHessianEntriesL2 b[n] u)
    (hg : HasDirichletWeakGradientL2 (g : E n → ℝ))
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) :
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeTrace b[n] u ψ hA hX = ∫ x, ψ x * T x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let b := b[n]
  let D (i : Fin (2 * n)) (x : E n) := dirichletColumnDivergence b A (b i) x
  let Y (x : E n) := ∑ i, D i x • b i
  have hY : ContDiff ℝ ∞ Y := ContDiff.sum fun i _ =>
    (contDiff_dirichletVectorDivergence b (hA.clm_apply contDiff_const)).smul contDiff_const
  let U := (u : DirichletBallL2Pair n).snd
  have hY_eq (x : E n) : inner ℝ (Y x) (U x) = ∑ i, D i x * inner ℝ (b i) (U x) := by
    simp only [Y, sum_inner, real_inner_smul_left]
  obtain ⟨R, hR, heR⟩ := exists_dirichletThirdDerivativeTrace_correction hn b u hH hA hX
  obtain ⟨S, hS, heS⟩ := exists_dirichletGradientPairing_fieldDerivative hn b u hH hY hX
  obtain ⟨DG, hDG, hWeak⟩ := hg.exists_fieldDerivative hn b (Lp.memLp g) hX
  refine ⟨-DG + S - R, (hDG.neg.add hS).sub hR, fun ψ => ?_⟩
  let τ := dirichletTestDivergence ψ b hX
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  have hForce : (∫ x, τ x * g x ∂ν[n]) = -(∫ x, ψ x * DG x ∂ν[n]) := by
    have h := hWeak ψ
    change (∫ x, ψ x * DG x ∂ν[n]) = -(∫ x, τ x * g x ∂ν[n]) at h
    linarith only [h]
  rw [heR ψ, hu.dirichletHessianTrace_eq_integral hn b hA, hForce]
  have hGrad := heS ψ
  change (∫ x, τ x * inner ℝ (Y x) (U x) ∂ν[n]) = _ at hGrad
  simp_rw [hY_eq] at hGrad
  rw [hGrad]
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, mul_sub, mul_add, mul_neg]
  have hNeg : Integrable (fun x => -(ψ x * DG x)) ν[n] := (hI hDG).neg
  have hAdd : Integrable (fun x => -(ψ x * DG x) + ψ x * S x) ν[n] :=
    hNeg.add (hI hS)
  rw [integral_sub hAdd (hI hR), integral_add hNeg (hI hS),
    integral_neg (f := fun x => ψ x * DG x)]
  ring

/-- For a smooth representative of the forcing, the weak derivative of the
elliptic Hessian trace along every smooth vector field is in L² after
subtracting the derivative of its coefficients. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeTraceL2 {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A g u) (hH : HasDirichletHessianEntriesL2 b[n] u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) :
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeTrace b[n] u ψ hA hX = ∫ x, ψ x * T x ∂ν[n] :=
  hu.exists_dirichletThirdDerivativeTraceL2_of_weakGradient hn hA hH
    (HasDirichletWeakGradientL2.of_smooth_ae hn hG hRep) hX

end KEBall
