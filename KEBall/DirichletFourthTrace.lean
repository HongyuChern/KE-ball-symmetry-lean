import KEBall.DirichletFourthDerivative

/-! Twice differentiating the elliptic equation to control its fourth derivative contraction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- If the potential has third derivatives in L², each weak derivative of
the first-order divergence correction itself has an L² weak gradient. -/
theorem exists_dirichletDivergenceGradientCorrection_weakDerivative_with_weakGradient
    {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hH : HasDirichletHessianEntriesL2 b u) (hT : HasDirichletThirdDerivativeEntriesL2 b u)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) (j : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ HasDirichletWeakGradientL2 F ∧ ∀ ψ : 𝓓B[n],
      (∫ x, ψ x * F x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (b j) *
          dirichletDivergenceGradientCorrection b u A x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hHj (i : Fin (2 * n)) := hH i j
  choose H hH₂ heH using hHj
  let U := (u : DirichletBallL2Pair n).snd
  let G (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (U x)
  have hG (i : Fin (2 * n)) : MemLp (G i) 2 ν[n] := (Lp.memLp U).const_inner (b i)
  let C (i : Fin (2 * n)) (x : E n) := dirichletColumnDivergence b A (b i) x
  have hC (i : Fin (2 * n)) : ContDiff ℝ ∞ (C i) :=
    contDiff_dirichletVectorDivergence b (hA.clm_apply contDiff_const)
  let D (i : Fin (2 * n)) (x : E n) := fderiv ℝ (C i) x (b j)
  have hD (i : Fin (2 * n)) : ContDiff ℝ ∞ (D i) :=
    ((hC i).fderiv_right (by simp)).clm_apply contDiff_const
  let F (i : Fin (2 * n)) (x : E n) := C i x * H i x + D i x * G i x
  have hP (i : Fin (2 * n)) := dirichletWeakDerivative_mul hn (hG i) (hH₂ i) (hC i) (b j)
    (fun ψ => (heH i ψ).symm)
  have hF (i : Fin (2 * n)) : MemLp (F i) 2 ν[n] := (hP i).1
  have hFW (i : Fin (2 * n)) : HasDirichletWeakGradientL2 (F i) := by
    have hHW := hasDirichletWeakGradientL2_of_hessianEntry hn b u hT i j (hH₂ i) (heH i)
    have hGW := hasDirichletWeakGradientL2_of_gradientEntry hn b u hH i
    have hC₂ := memLp_dirichlet_mul_of_continuousOn (hC i).continuous.continuousOn (hH₂ i)
    have hD₂ := memLp_dirichlet_mul_of_continuousOn (hD i).continuous.continuousOn (hG i)
    exact (hHW.mul_smooth hn (hH₂ i) (hC i)).add hn hC₂ hD₂
      (hGW.mul_smooth hn (hG i) (hD i))
  refine ⟨fun x => ∑ i, F i x, memLp_finsetSum Finset.univ (fun i _ => hF i),
    HasDirichletWeakGradientL2.finsetSum hn Finset.univ (fun i _ => hF i) (fun i _ => hFW i),
    fun ψ => ?_⟩
  let τ := dirichletTestFieldDerivative ψ (fun _ => b j) contDiff_const
  have hI (φ : 𝓓B[n]) {f : E n → ℝ} (hf : MemLp f 2 ν[n]) :
      Integrable (fun x => φ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hf).integrable (by norm_num)
  change (∫ x, ψ x * (∑ i, F i x) ∂ν[n]) =
    -(∫ x, τ x * (∑ i, C i x * G i x) ∂ν[n])
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hI ψ (hF i)),
    integral_finsetSum _ (fun i _ => hI τ
      (memLp_dirichlet_mul_of_continuousOn (hC i).continuous.continuousOn (hG i))),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (hP i).2 ψ

/-- The third weak derivative contracted with a smooth matrix is represented by
the sum of its entries weighted by the matrix coefficients. -/
theorem dirichletThirdDerivativeSlice_eq_integral_of_entries {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    (k : Fin (2 * n)) (F : Fin (2 * n) → Fin (2 * n) → E n → ℝ)
    (hF : ∀ i j, MemLp (F i j) 2 ν[n])
    (he : ∀ i j (ψ : 𝓓(dirichletBallOpens n, ℝ)),
      dirichletThirdDerivativeEntry u ψ (b k) (b j) (b i) = ∫ x, ψ x * F i j x ∂ν[n])
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    dirichletThirdDerivativeSlice b u ψ (b k) hB =
      ∫ x, ψ x * (∑ i, ∑ j, inner ℝ (b j) (B x (b i)) * F i j x) ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hB (b i) (b j)
  have hTerm (i j : Fin (2 * n)) : MemLp (fun x => c i j x * F i j x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hc i j).continuous.continuousOn (hF i j)
  have hSum (i : Fin (2 * n)) : MemLp (fun x => ∑ j, c i j x * F i j x) 2 ν[n] :=
    memLp_finsetSum Finset.univ fun j _ => hTerm i j
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  change (∑ i, ∑ j, dirichletThirdDerivativeEntry u (dirichletTestMul ψ (hc i j)) (b k) (b j) (b i)) =
    ∫ x, ψ x * (∑ i, ∑ j, c i j x * F i j x) ∂ν[n]
  simp_rw [he, dirichletTestMul_apply, mul_assoc]
  rw [show (∫ x, ψ x * (∑ i, ∑ j, c i j x * F i j x) ∂ν[n]) =
      ∑ i, ∫ x, ψ x * (∑ j, c i j x * F i j x) ∂ν[n] from by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => by
      simpa only [Finset.mul_sum] using hI (hSum i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.mul_sum]
  exact (integral_finsetSum _ fun j _ => hI (hTerm i j)).symm

/-- A contraction with smooth coefficients is represented by the weighted
sum of the L² representatives of the third derivative entries. -/
theorem exists_dirichletThirdDerivativeSliceL2_of_entries {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hEntries : HasDirichletThirdDerivativeEntriesL2 b u) (k : Fin (2 * n))
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      dirichletThirdDerivativeSlice b u ψ (b k) hB = ∫ x, ψ x * F x ∂ν[n] := by
  have hk (i j : Fin (2 * n)) := hEntries i j k
  choose F hF he using hk
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hB (b i) (b j)
  have hTerm (i j : Fin (2 * n)) : MemLp (fun x => c i j x * F i j x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hc i j).continuous.continuousOn (hF i j)
  have hSum (i : Fin (2 * n)) : MemLp (fun x => ∑ j, c i j x * F i j x) 2 ν[n] :=
    memLp_finsetSum Finset.univ fun j _ => hTerm i j
  exact ⟨fun x => ∑ i, ∑ j, c i j x * F i j x,
    memLp_finsetSum Finset.univ (fun i _ => hSum i),
    dirichletThirdDerivativeSlice_eq_integral_of_entries hn b u hB k F hF he⟩

private theorem integral_dirichletTest_constDerivative_mul_smooth {n : ℕ} (hn : 0 < n)
    (ψ : 𝓓B[n]) (d : E n) {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) :
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x d * G x ∂ν[n]) =
      -(∫ x, ψ x * fderiv ℝ G x d ∂ν[n]) := by
  have h := integral_dirichletTest_fieldDerivative_mul_smooth hn ψ hG (contDiff_const (c := d))
  dsimp only at h
  have hz (x : E n) : dirichletVectorDivergence (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (fun _ => d) x = 0 := by simp [dirichletVectorDivergence]
  simpa only [hz, mul_zero, add_zero] using h

/-- Twice differentiating the elliptic equation represents the matrix
contraction of the fourth derivative by an L² function. -/
theorem IsDirichletWeakSolution.exists_dirichletFourthDerivativeSliceL2 {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hH : HasDirichletHessianEntriesL2 b u) (hT : HasDirichletThirdDerivativeEntriesL2 b u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    (d e : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      dirichletFourthDerivativeSlice b u ψ (b d) (b e) hA = ∫ x, ψ x * F x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let D (x : E n) := fderiv ℝ A x (b d)
  let E' (x : E n) := fderiv ℝ A x (b e)
  let DE (x : E n) := fderiv ℝ D x (b e)
  let ED (x : E n) := fderiv ℝ E' x (b d)
  have hD : ContDiff ℝ ∞ D := (hA.fderiv_right (by simp)).clm_apply contDiff_const
  have hE : ContDiff ℝ ∞ E' := (hA.fderiv_right (by simp)).clm_apply contDiff_const
  have hDE : ContDiff ℝ ∞ DE := (hD.fderiv_right (by simp)).clm_apply contDiff_const
  have hED : ContDiff ℝ ∞ ED := (hE.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨Y, hY, heY⟩ := exists_dirichletThirdDerivativeSliceL2_of_entries hn b u hT d hE
  obtain ⟨Z, hZ, heZ⟩ := exists_dirichletThirdDerivativeSliceL2_of_entries hn b u hT e hD
  obtain ⟨R, hR, heR⟩ := hasDirichletHessianTraceL2_of_entries hn b u hH hED
  let C := dirichletDivergenceGradientCorrection b u A
  obtain ⟨C₁, _, hC₁, heC₁⟩ :=
    exists_dirichletDivergenceGradientCorrection_weakDerivative_with_weakGradient hn b u hH hT hA e
  obtain ⟨C₂, hC₂, heC₂⟩ := hC₁ (b d)
  let G₁ (x : E n) := fderiv ℝ G x (b e)
  let G₂ (x : E n) := fderiv ℝ G₁ x (b d)
  have hG₁ : ContDiff ℝ ∞ G₁ := (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hG₂ : ContDiff ℝ ∞ G₂ := (hG₁.fderiv_right (by simp)).clm_apply contDiff_const
  have hG₂Lp : MemLp G₂ 2 ν[n] := MemLp.ae_eq (Eventually.of_forall fun x => mul_one (G₂ x))
    (memLp_dirichlet_mul_of_continuousOn hG₂.continuous.continuousOn (memLp_const (1 : ℝ)))
  refine ⟨fun x => -G₂ x - C₂ x - Y x - Z x - R x,
    (((hG₂Lp.neg.sub hC₂).sub hY).sub hZ).sub hR, fun ψ => ?_⟩
  let ψd := dirichletTestFieldDerivative ψ (fun _ => b d) contDiff_const
  let ψe := dirichletTestFieldDerivative ψ (fun _ => b e) contDiff_const
  let ψde := dirichletTestFieldDerivative ψd (fun _ => b e) contDiff_const
  have hFirst := dirichletFourthDerivativeSlice_eq_hessianTrace hn b u ψ (b d) (b e) hA
    hD hE hDE
  change dirichletFourthDerivativeSlice b u ψ (b d) (b e) hA =
    dirichletHessianTrace b u ψde hA + dirichletHessianTrace b u ψd hE +
      dirichletHessianTrace b u ψe hD + dirichletHessianTrace b u ψ hDE at hFirst
  have hThird₁ := dirichletThirdDerivativeSlice_eq_neg_hessianTrace hn b u ψ (b d) hE hED
  have hThird₂ := dirichletThirdDerivativeSlice_eq_neg_hessianTrace hn b u ψ (b e) hD hDE
  change dirichletThirdDerivativeSlice b u ψ (b d) hE =
    -dirichletHessianTrace b u ψd hE - dirichletHessianTrace b u ψ hED at hThird₁
  change dirichletThirdDerivativeSlice b u ψ (b e) hD =
    -dirichletHessianTrace b u ψe hD - dirichletHessianTrace b u ψ hDE at hThird₂
  rw [heY ψ, heR ψ] at hThird₁
  rw [heZ ψ] at hThird₂
  have hC_eq : (∫ x, ψde x * C x ∂ν[n]) = ∫ x, ψ x * C₂ x ∂ν[n] := by
    have h₁ := heC₁ ψd
    have h₂ := heC₂ ψ
    change (∫ x, ψd x * C₁ x ∂ν[n]) = -(∫ x, ψde x * C x ∂ν[n]) at h₁
    change (∫ x, ψ x * C₂ x ∂ν[n]) = -(∫ x, ψd x * C₁ x ∂ν[n]) at h₂
    linarith only [h₁, h₂]
  have hG_eq : (∫ x, ψde x * g x ∂ν[n]) = ∫ x, ψ x * G₂ x ∂ν[n] := by
    have h₁ := integral_dirichletTest_constDerivative_mul_smooth hn ψd (b e) hG
    have h₂ := integral_dirichletTest_constDerivative_mul_smooth hn ψ (b d) hG₁
    change (∫ x, ψde x * G x ∂ν[n]) = -(∫ x, ψd x * G₁ x ∂ν[n]) at h₁
    change (∫ x, ψd x * G₁ x ∂ν[n]) = -(∫ x, ψ x * G₂ x ∂ν[n]) at h₂
    have hEq : (∫ x, ψde x * g x ∂ν[n]) = ∫ x, ψde x * G x ∂ν[n] := by
      apply integral_congr_ae
      filter_upwards [hRep] with x hx
      rw [hx]
    linarith only [h₁, h₂, hEq]
  have hTrace := hu.dirichletHessianTrace_eq_integral hn b hA ψde
  change dirichletHessianTrace b u ψde hA = -(∫ x, ψde x * g x ∂ν[n]) -
    ∫ x, ψde x * C x ∂ν[n] at hTrace
  rw [hG_eq, hC_eq] at hTrace
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  have hNeg : Integrable (fun x => -(ψ x * G₂ x)) ν[n] := (hI hG₂Lp).neg
  have h₁ : Integrable (fun x => -(ψ x * G₂ x) - ψ x * C₂ x) ν[n] :=
    hNeg.sub (hI hC₂)
  have h₂ : Integrable (fun x => -(ψ x * G₂ x) - ψ x * C₂ x - ψ x * Y x) ν[n] := h₁.sub (hI hY)
  have h₃ : Integrable (fun x => -(ψ x * G₂ x) - ψ x * C₂ x - ψ x * Y x - ψ x * Z x) ν[n] :=
    h₂.sub (hI hZ)
  simp only [mul_sub, mul_neg]
  rw [integral_sub h₃ (hI hR), integral_sub h₂ (hI hZ), integral_sub h₁ (hI hY),
    integral_sub hNeg (hI hC₂), integral_neg (f := fun x => ψ x * G₂ x)]
  linarith only [hFirst, hThird₁, hThird₂, hTrace]

end KEBall
