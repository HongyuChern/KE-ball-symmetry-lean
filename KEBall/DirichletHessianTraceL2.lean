import KEBall.DirichletHessianCoefficient
import KEBall.DirichletTangentWeak
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Square-integrable representatives of weak Hessian contractions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- The tested Hessian contraction is represented by an actual L² function. -/
def HasDirichletHessianTraceL2 {n : ℕ} (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (u : DirichletSobolev n) {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) : Prop :=
  ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
    dirichletHessianTrace b u ψ hA = ∫ x, ψ x * F x ∂ν[n]

theorem HasDirichletHessianTraceL2.congr {n : ℕ}
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)} {u : DirichletSobolev n}
    {A B : E n → E n →L[ℝ] E n} {hA : ContDiff ℝ ∞ A} {hB : ContDiff ℝ ∞ B}
    (h : HasDirichletHessianTraceL2 b u hA) (he : A = B) :
    HasDirichletHessianTraceL2 b u hB := by
  subst B
  exact h

theorem HasDirichletHessianTraceL2.smul {n : ℕ}
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)} {u : DirichletSobolev n}
    {A : E n → E n →L[ℝ] E n} {hA : ContDiff ℝ ∞ A}
    (h : HasDirichletHessianTraceL2 b u hA) {m : E n → ℝ} (hm : ContDiff ℝ ∞ m) :
    HasDirichletHessianTraceL2 b u (hm.smul hA) := by
  obtain ⟨F, hF, he⟩ := h
  refine ⟨fun x => m x * F x, memLp_dirichlet_mul_of_continuousOn hm.continuous.continuousOn hF, ?_⟩
  intro ψ
  rw [dirichletHessianTrace_smul b u ψ hA hm, he]
  simp only [dirichletTestMul_apply, mul_assoc]

theorem HasDirichletHessianTraceL2.adjoint {n : ℕ}
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)} {u : DirichletSobolev n}
    {A : E n → E n →L[ℝ] E n} {hA : ContDiff ℝ ∞ A}
    (h : HasDirichletHessianTraceL2 b u hA) (hAdj : ContDiff ℝ ∞ (fun x => (A x).adjoint)) :
    HasDirichletHessianTraceL2 b u hAdj := by
  obtain ⟨F, hF, he⟩ := h
  refine ⟨F, hF, fun ψ => ?_⟩
  rw [dirichletHessianTrace_adjoint b u ψ hA hAdj, he]

theorem HasDirichletHessianTraceL2.sum {n : ℕ} {ι : Type*} (hn : 0 < n)
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)} {u : DirichletSobolev n}
    {A : ι → E n → E n →L[ℝ] E n} {hA : ∀ i, ContDiff ℝ ∞ (A i)}
    (h : ∀ i, HasDirichletHessianTraceL2 b u (hA i)) (s : Finset ι) :
    HasDirichletHessianTraceL2 b u (ContDiff.sum fun i (_ : i ∈ s) => hA i) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  choose F hF he using h
  refine ⟨fun x => ∑ i ∈ s, F i x, memLp_finsetSum s fun i _ => hF i, fun ψ => ?_⟩
  rw [dirichletHessianTrace_sum hn b u ψ hA s]
  simp_rw [he, Finset.mul_sum]
  have hI (i : ι) : Integrable (fun x => ψ x * F i x) ν[n] :=
    ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (((hF i).integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  exact (integral_finsetSum s fun i _ => hI i).symm

theorem HasDirichletHessianTraceL2.add {n : ℕ} (hn : 0 < n)
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)} {u : DirichletSobolev n}
    {A B : E n → E n →L[ℝ] E n} {hA : ContDiff ℝ ∞ A} {hB : ContDiff ℝ ∞ B}
    (h : HasDirichletHessianTraceL2 b u hA) (h' : HasDirichletHessianTraceL2 b u hB) :
    HasDirichletHessianTraceL2 b u (hA.add hB) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  obtain ⟨F, hF, he⟩ := h
  obtain ⟨G, hG, he'⟩ := h'
  refine ⟨F + G, hF.add hG, fun ψ => ?_⟩
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hf.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  rw [dirichletHessianTrace_add hn b u ψ hA hB, he, he', ← integral_add (hI hF) (hI hG)]
  simp only [Pi.add_apply, mul_add]

theorem HasDirichletHessianTraceL2.sub {n : ℕ} (hn : 0 < n)
    {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)} {u : DirichletSobolev n}
    {A B : E n → E n →L[ℝ] E n} {hA : ContDiff ℝ ∞ A} {hB : ContDiff ℝ ∞ B}
    (h : HasDirichletHessianTraceL2 b u hA) (h' : HasDirichletHessianTraceL2 b u hB) :
    HasDirichletHessianTraceL2 b u (hA.sub hB) := by
  have hNeg : HasDirichletHessianTraceL2 b u hB.neg := by
    apply (h'.smul (contDiff_const (c := (-1 : ℝ)))).congr
    funext x
    exact neg_one_smul ℝ (B x)
  exact (h.add hn hNeg).congr (sub_eq_add_neg A B).symm

/-- The weak Dirichlet equation gives an L² contraction with its coefficients. -/
theorem IsDirichletWeakSolution.hasDirichletHessianTraceL2 {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A g u) :
    HasDirichletHessianTraceL2 b u hA := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let U := (u : DirichletBallL2Pair n).snd
  let D (i : Fin (2 * n)) (x : E n) := dirichletColumnDivergence b A (b i) x
  let F (x : E n) := ∑ i, D i x * inner ℝ (b i) (U x)
  have hD (i : Fin (2 * n)) : ContDiff ℝ ∞ (D i) :=
    contDiff_dirichletVectorDivergence b (hA.clm_apply contDiff_const)
  have hF : MemLp F 2 ν[n] :=
    memLp_finsetSum Finset.univ fun i _ =>
      memLp_dirichlet_mul_of_continuousOn (hD i).continuous.continuousOn
        ((Lp.memLp U).const_inner (b i))
  refine ⟨-(g + F), ((Lp.memLp g).add hF).neg, fun ψ => ?_⟩
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hf.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  rw [hu.dirichletHessianTrace_eq_integral hn b hA]
  change -(∫ x, ψ x * g x ∂ν[n]) - (∫ x, ψ x * F x ∂ν[n]) =
    ∫ x, ψ x * (-(g x + F x)) ∂ν[n]
  simp_rw [mul_neg, mul_add, integral_neg, integral_add (hI (Lp.memLp g)) (hI hF),
    sub_eq_add_neg, neg_add]

/-- A smooth coefficient field followed by the tangential projection has
a square-integrable contraction with the weak Hessian. -/
theorem hasDirichletHessianTraceL2_tangentComp {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    HasDirichletHessianTraceL2 b u (contDiff_dirichletTangentTensor.clm_comp hB) := by
  let X (j : Fin (2 * n)) (x : E n) := dirichletTangentTensor x (b j)
  have hX (j : Fin (2 * n)) : ContDiff ℝ ∞ (X j) :=
    contDiff_dirichletTangentTensor.clm_apply contDiff_const
  let R (i j : Fin (2 * n)) (x : E n) := rankOne ℝ (X j x) (b i)
  have hR (i j : Fin (2 * n)) : ContDiff ℝ ∞ (R i j) :=
    contDiff_rankOne_real (hX j) contDiff_const
  have hTrace (i j : Fin (2 * n)) : HasDirichletHessianTraceL2 b u (hR i j) := by
    obtain ⟨F, hF, he⟩ := exists_memLp_dirichletTangentGradient hn hA hl hE hLipA hM₀ hM
      hu (b j) (b i)
    refine ⟨F, hF, fun ψ => ?_⟩
    rw [dirichletHessianTrace_rankOne_basis hn b u ψ (hX j) i, he ψ]
    have hD (x : E n) : dirichletVectorDivergence b (X j) x =
        (1 - (2 : ℝ) * n) * inner ℝ (b j) x := dirichletVectorDivergence_tangentTensor b (b j) x
    simp_rw [hD, X, dirichletTangentTensor_apply, mul_comm (ψ _)]
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hB (b i) (b j)
  have hSum := HasDirichletHessianTraceL2.sum hn (fun i =>
    HasDirichletHessianTraceL2.sum hn (fun j => (hTrace i j).smul (hc i j)) Finset.univ) Finset.univ
  apply hSum.congr
  funext x
  ext y : 1
  simp only [sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ i, ∑ j, c i j x • (inner ℝ (b i) y • X j x)) =
    dirichletTangentTensor x (B x y)
  have hInner (i : Fin (2 * n)) :
      dirichletTangentTensor x (B x (b i)) = ∑ j, c i j x • X j x := by
    calc
      _ = dirichletTangentTensor x (∑ j, c i j x • b j) :=
        congrArg (dirichletTangentTensor x) (b.sum_repr' (B x (b i))).symm
      _ = _ := by simp only [map_sum, map_smul, X]
  calc
    _ = ∑ i, inner ℝ (b i) y • dirichletTangentTensor x (B x (b i)) := by
      simp_rw [hInner, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (c i j x)]
    _ = dirichletTangentTensor x (B x (∑ i, inner ℝ (b i) y • b i)) := by
      simp only [map_sum, map_smul]
    _ = _ := by rw [b.sum_repr']

/-- The radial-radial Hessian contraction multiplied by the radial
ellipticity coefficient has an L² representative on the whole ball. -/
theorem hasDirichletHessianTraceL2_weightedRadial {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u) :
    HasDirichletHessianTraceL2 b u
      (((hAc.clm_apply contDiff_id).inner ℝ contDiff_id).smul contDiff_dirichletRadialTensor) := by
  let P := dirichletTangentTensor (n := n)
  let R := dirichletRadialTensor (n := n)
  let C (x : E n) := inner ℝ (A x x) x
  have hP : ContDiff ℝ ∞ P := contDiff_dirichletTangentTensor
  have hR : ContDiff ℝ ∞ R := contDiff_dirichletRadialTensor
  have hC : ContDiff ℝ ∞ C := (hAc.clm_apply contDiff_id).inner ℝ contDiff_id
  have hR₂ : ContDiff ℝ ∞ (fun x : E n => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hR₄ : ContDiff ℝ ∞ (fun x : E n => ‖x‖ ^ 4) := by
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by decide] using hR₂.pow 2
  have hTA := hasDirichletHessianTraceL2_tangentComp hn b hA hl hE hLipA hM₀ hM hu hAc
  have hTB := hasDirichletHessianTraceL2_tangentComp hn b hA hl hE hLipA hM₀ hM hu
    (hAc.clm_comp hR)
  have hMixC := hR.clm_comp (hAc.clm_comp hP)
  have hEq : (fun x => ((P x).comp ((A x).comp (R x))).adjoint) =
      fun x => (R x).comp ((A x).comp (P x)) := by
    funext x
    simp only [P, R, ContinuousLinearMap.adjoint_comp, dirichletTangentTensor_adjoint,
      dirichletRadialTensor_adjoint, hSym, ContinuousLinearMap.comp_assoc]
  have hAdj : ContDiff ℝ ∞ (fun x => ((P x).comp ((A x).comp (R x))).adjoint) := by
    rw [hEq]
    exact hMixC
  have hMix : HasDirichletHessianTraceL2 b u hMixC := (hTB.adjoint hAdj).congr hEq
  have hTrace := (hu.hasDirichletHessianTraceL2 hn b hAc).smul hR₄
  have hSub := (hTrace.sub hn (hTA.smul hR₂)).sub hn hMix
  apply hSub.congr (hB := hC.smul hR)
  funext x
  change ((‖x‖ ^ 4) • A x - (‖x‖ ^ 2) • ((P x).comp (A x))) -
    (R x).comp ((A x).comp (P x)) = C x • R x
  rw [dirichlet_tangent_radial_coefficient_decomposition]
  abel

/-- Extend the reciprocal smoothly across arguments below a positive threshold. -/
theorem exists_smooth_reciprocal_of_pos_threshold {a : ℝ} (ha : 0 < a) :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧ ∀ t ≥ a, q t * t = 1 := by
  let χ (t : ℝ) := Real.smoothTransition ((t - a / 2) / (a / 2))
  let D (t : ℝ) := a + χ t * (t - a)
  have hχ : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hD : ContDiff ℝ ∞ D := contDiff_const.add (hχ.mul (contDiff_id.sub contDiff_const))
  have hPos (t : ℝ) : 0 < D t := by
    by_cases ht : t ≤ a / 2
    · have h0 : χ t = 0 := Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by positivity))
      simpa [D, h0] using ha
    · have hTa : a / 2 < t := lt_of_not_ge ht
      have hχ₀ : 0 ≤ χ t := Real.smoothTransition.nonneg _
      have hχ₁ : χ t ≤ 1 := Real.smoothTransition.le_one _
      have h₀ : 0 ≤ (1 - χ t) * (a / 2) := mul_nonneg (sub_nonneg.mpr hχ₁) (by positivity)
      have h₁ : 0 ≤ χ t * (t - a / 2) := mul_nonneg hχ₀ (sub_nonneg.mpr hTa.le)
      dsimp only [D]
      nlinarith only [ha, h₀, h₁]
  refine ⟨fun t => (D t)⁻¹, hD.inv (fun t => (hPos t).ne'), fun t ht => ?_⟩
  have h1 : χ t = 1 := Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ (show 0 < a / 2 by positivity)).mpr (by linarith))
  have he : D t = t := by simp [D, h1]
  change (D t)⁻¹ * t = 1
  rw [he, inv_mul_cancel₀ (ha.trans_le ht).ne']

private theorem exists_dirichletHessianTraceL2_of_smul_on {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {m : E n → ℝ} (hm : ContDiff ℝ ∞ m) {a : ℝ} (ha : 0 < a)
    {s : Set (E n)} (hLower : ∀ x ∈ unitBall n, x ∈ s → a ≤ m x)
    {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (he : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ), tsupport (ψ : E n → ℝ) ⊆ s →
      dirichletHessianTrace b u ψ (hm.smul hA) = ∫ x, ψ x * F x ∂ν[n]) :
    ∃ G : E n → ℝ, MemLp G 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ s →
      dirichletHessianTrace b u ψ hA = ∫ x, ψ x * G x ∂ν[n] := by
  obtain ⟨q, hq, hqInv⟩ := exists_smooth_reciprocal_of_pos_threshold ha
  have hqm : ContDiff ℝ ∞ (q ∘ m) := hq.comp hm
  refine ⟨fun x => q (m x) * F x,
    memLp_dirichlet_mul_of_continuousOn hqm.continuous.continuousOn hF, ?_⟩
  intro ψ hSupp
  let χ := dirichletTestMul ψ hqm
  have hχ : tsupport (χ : E n → ℝ) ⊆ s := tsupport_mul_subset_left.trans hSupp
  have hTest : dirichletTestMul χ hm = ψ := by
    apply TestFunction.ext
    intro x
    change (ψ x * q (m x)) * m x = ψ x
    by_cases hx : x ∈ tsupport (ψ : E n → ℝ)
    · rw [mul_assoc, hqInv (m x) (hLower x (ψ.tsupport_subset hx) (hSupp hx)), mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have h := he χ hχ
  rw [dirichletHessianTrace_smul b u χ hA hm, hTest] at h
  simpa only [χ, dirichletTestMul_apply, Function.comp_apply, mul_assoc] using h

/-- On tests supported away from the center, the radial-radial weak
Hessian contraction itself is represented by a square-integrable function. -/
theorem exists_dirichletRadialHessianL2_on_annulus {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {r : ℝ} (hr : 0 < r) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ {x | r < ‖x‖} →
      dirichletHessianTrace b u ψ contDiff_dirichletRadialTensor =
        ∫ x, ψ x * F x ∂ν[n] := by
  let C (x : E n) := inner ℝ (A x x) x
  have hC : ContDiff ℝ ∞ C := (hAc.clm_apply contDiff_id).inner ℝ contDiff_id
  have hAE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v :=
    (ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)).mono fun x hx => hE x hx
  have hRadial : HasDirichletHessianTraceL2 b u (hC.smul contDiff_dirichletRadialTensor) :=
    hasDirichletHessianTraceL2_weightedRadial hn b hA hAc hSym hl hAE hLipA hM₀ hM hu
  obtain ⟨F, hF, he⟩ := hRadial
  refine exists_dirichletHessianTraceL2_of_smul_on b u contDiff_dirichletRadialTensor hC
    (a := l * r ^ 2) (by positivity) ?_ hF (fun ψ _ => he ψ)
  intro x hx hxr
  exact dirichlet_radialCoefficient_ge hl.le hr.le x (le_of_lt hxr) (hE x hx)

/-- On each annulus the complete weak Hessian can be contracted with
any smooth coefficient field to give a square-integrable representative. -/
theorem exists_dirichletHessianTraceL2_on_annulus {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    (hBAdj : ContDiff ℝ ∞ (fun x => (B x).adjoint)) {r : ℝ} (hr : 0 < r) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ {x | r < ‖x‖} →
      dirichletHessianTrace b u ψ hB = ∫ x, ψ x * F x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let P := dirichletTangentTensor (n := n)
  let R := dirichletRadialTensor (n := n)
  let C (x : E n) := inner ℝ (B x x) x
  have hP : ContDiff ℝ ∞ P := contDiff_dirichletTangentTensor
  have hR : ContDiff ℝ ∞ R := contDiff_dirichletRadialTensor
  have hC : ContDiff ℝ ∞ C := (hB.clm_apply contDiff_id).inner ℝ contDiff_id
  have hR₂ : ContDiff ℝ ∞ (fun x : E n => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hR₄ : ContDiff ℝ ∞ (fun x : E n => ‖x‖ ^ 4) := by
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by decide] using hR₂.pow 2
  have hAE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v :=
    (ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)).mono fun x hx => hE x hx
  obtain ⟨F, hF, heF⟩ := exists_dirichletRadialHessianL2_on_annulus hn b hA hAc hSym hl hE
    hLipA hM₀ hM hu hr
  have hLeft := hR₂.smul (hP.clm_comp hB)
  have hLeftRep : HasDirichletHessianTraceL2 b u hLeft :=
    (hasDirichletHessianTraceL2_tangentComp hn b hA hl hAE hLipA hM₀ hM hu hB).smul hR₂
  have hRight := hR.clm_comp (hB.clm_comp hP)
  have hRightRep : HasDirichletHessianTraceL2 b u hRight := by
    have hT := hasDirichletHessianTraceL2_tangentComp hn b hA hl hAE hLipA hM₀ hM
      hu (hBAdj.clm_comp hR)
    have hEq : (fun x => ((P x).comp ((B x).adjoint.comp (R x))).adjoint) =
        fun x => (R x).comp ((B x).comp (P x)) := by
      funext x
      simp only [P, R, ContinuousLinearMap.adjoint_comp, dirichletTangentTensor_adjoint,
        dirichletRadialTensor_adjoint, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
    have hAdj : ContDiff ℝ ∞ (fun x => ((P x).comp ((B x).adjoint.comp (R x))).adjoint) := by
      rw [hEq]
      exact hRight
    exact (hT.adjoint hAdj).congr hEq
  obtain ⟨T, hT, heT⟩ := hLeftRep.add hn hRightRep
  let Q (x : E n) := C x * F x
  have hQ : MemLp Q 2 ν[n] := memLp_dirichlet_mul_of_continuousOn hC.continuous.continuousOn hF
  apply exists_dirichletHessianTraceL2_of_smul_on b u hB hR₄ (a := r ^ 4)
    (by positivity) (fun x _ hx => pow_le_pow_left₀ hr.le (le_of_lt hx) 4) (hT.add hQ)
  intro ψ hSupp
  have he : (fun x => ‖x‖ ^ 4 • B x) =
      ((fun x => ‖x‖ ^ 2 • (P x).comp (B x)) +
        (fun x => (R x).comp ((B x).comp (P x)))) + (fun x => C x • R x) := by
    funext x
    exact dirichlet_tangent_radial_coefficient_decomposition x (B x)
  have hSupp' : tsupport (dirichletTestMul ψ hC : E n → ℝ) ⊆ {x | r < ‖x‖} :=
    tsupport_mul_subset_left.trans hSupp
  rw [dirichletHessianTrace_congr b u ψ (hR₄.smul hB) ((hLeft.add hRight).add (hC.smul hR)) he,
    dirichletHessianTrace_add hn b u ψ (hLeft.add hRight) (hC.smul hR), heT,
    dirichletHessianTrace_smul b u ψ hR hC, heF (dirichletTestMul ψ hC) hSupp']
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hf.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  simp only [dirichletTestMul_apply, mul_assoc]
  change (∫ x, ψ x * T x ∂ν[n]) + (∫ x, ψ x * Q x ∂ν[n]) =
    ∫ x, ψ x * (T x + Q x) ∂ν[n]
  simp_rw [mul_add, integral_add (hI hT) (hI hQ)]

/-- Every coordinate of the weak Hessian has an L² representative on
tests supported in any annulus that stays away from the origin. -/
theorem exists_dirichletHessianEntryL2_on_annulus {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {r : ℝ} (hr : 0 < r) (i j : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ {x | r < ‖x‖} →
      dirichletHessianEntry u ψ (b j) (b i) = ∫ x, ψ x * F x ∂ν[n] := by
  let B (_ : E n) := rankOne ℝ (b j) (b i)
  have hB : ContDiff ℝ ∞ B := contDiff_const
  have hBAdj : ContDiff ℝ ∞ (fun x => (B x).adjoint) := by
    change ContDiff ℝ ∞ (fun _ : E n => (rankOne ℝ (b j) (b i)).adjoint)
    exact contDiff_const
  obtain ⟨F, hF, he⟩ := exists_dirichletHessianTraceL2_on_annulus hn b hA hAc hSym hl hE
    hLipA hM₀ hM hu hB hBAdj hr
  refine ⟨F, hF, fun ψ hSupp => ?_⟩
  have h := he ψ hSupp
  have hX : ContDiff ℝ ∞ (fun _ : E n => b j) := contDiff_const
  have hRank := dirichletHessianTrace_rankOne_basis hn b u ψ hX i
  have hz (x : E n) : dirichletVectorDivergence b (fun _ : E n => b j) x = 0 := by
    simp [dirichletVectorDivergence]
  rw [← h]
  simpa only [dirichletHessianEntry, hz, mul_zero, add_zero] using hRank.symm

end KEBall
