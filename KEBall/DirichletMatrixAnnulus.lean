import KEBall.DirichletHessianTraceL2

/-! Recovery of weak matrix contractions from tangential and elliptic contractions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set
open scoped ContDiff Distributions

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Contract two weak derivative entries against a smooth coefficient matrix. -/
noncomputable def dirichletMatrixContraction {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (entry : 𝓓B[n] → E n → E n → ℝ) (ψ : 𝓓B[n])
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) : ℝ :=
  ∑ i, ∑ j, entry (dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hB (b i) (b j)))
    (b j) (b i)

theorem dirichletMatrixContraction_add {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (entry : 𝓓B[n] → E n → E n → ℝ) (ψ : 𝓓B[n]) {A B : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hAdd : ∀ ψ φ v w, entry (ψ + φ) v w = entry ψ v w + entry φ v w) :
    dirichletMatrixContraction b entry ψ (hA.add hB) =
      dirichletMatrixContraction b entry ψ hA + dirichletMatrixContraction b entry ψ hB := by
  unfold dirichletMatrixContraction
  simp_rw [← Finset.sum_add_distrib, ← hAdd]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply TestFunction.ext
  intro x
  simp [add_apply, inner_add_right, mul_add]

theorem dirichletMatrixContraction_smul {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (entry : 𝓓B[n] → E n → E n → ℝ) (ψ : 𝓓B[n])
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {m : E n → ℝ} (hm : ContDiff ℝ ∞ m) :
    dirichletMatrixContraction b entry ψ (hm.smul hA) =
      dirichletMatrixContraction b entry (dirichletTestMul ψ hm) hA := by
  unfold dirichletMatrixContraction
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply TestFunction.ext
  intro x
  simp [real_inner_smul_right, mul_assoc]

theorem dirichletMatrixContraction_adjoint {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (entry : 𝓓B[n] → E n → E n → ℝ) (ψ : 𝓓B[n])
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hAdj : ContDiff ℝ ∞ (fun x => (A x).adjoint))
    (hSym : ∀ ψ v w, entry ψ v w = entry ψ w v) :
    dirichletMatrixContraction b entry ψ hAdj = dirichletMatrixContraction b entry ψ hA := by
  unfold dirichletMatrixContraction
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hSym _ (b j) (b i)]
  congr 1
  apply TestFunction.ext
  intro x
  simp only [dirichletTestMul_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm]

theorem dirichletMatrixContraction_rankOne_basis {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (entry : 𝓓B[n] → E n → E n → ℝ) (ψ : 𝓓B[n]) (i j : Fin (2 * n))
    (hZero : ∀ v w, entry 0 v w = 0) :
    dirichletMatrixContraction b entry ψ (contDiff_const (c := rankOne ℝ (b j) (b i))) =
      entry ψ (b j) (b i) := by
  let B (_ : E n) := rankOne ℝ (b j) (b i)
  let hB : ContDiff ℝ ∞ B := contDiff_const
  have hTest (a c : Fin (2 * n)) :
      dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hB (b a) (b c)) =
        if a = i ∧ c = j then ψ else 0 := by
    apply TestFunction.ext
    intro x
    by_cases ha : a = i <;> by_cases hc : c = j
    · subst a
      subst c
      simp [B, rankOne_apply]
    · subst a
      simp [B, rankOne_apply, hc, orthonormal_iff_ite.mp b.orthonormal c j]
    · subst c
      simp [B, rankOne_apply, ha, orthonormal_iff_ite.mp b.orthonormal i a, Ne.symm ha]
    · simp [B, rankOne_apply, ha, orthonormal_iff_ite.mp b.orthonormal i a, Ne.symm ha]
  change dirichletMatrixContraction b entry ψ hB = _
  unfold dirichletMatrixContraction
  simp_rw [hTest]
  rw [Fintype.sum_eq_single i (fun a ha => by simp [ha, hZero])]
  rw [Fintype.sum_eq_single j (fun c hc => by simp [hc, hZero])]
  simp


/-- A square-integrable representative of a matrix contraction on
tests supported in a subset of the ball. -/
def HasDirichletMatrixContractionL2On {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (entry : 𝓓B[n] → E n → E n → ℝ) (s : Set (E n)) {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) : Prop :=
  ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
    tsupport (ψ : E n → ℝ) ⊆ s →
    dirichletMatrixContraction b entry ψ hB = ∫ x, ψ x * F x ∂ν[n]

namespace HasDirichletMatrixContractionL2On

variable {n : ℕ} {b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)}
variable {entry : 𝓓B[n] → E n → E n → ℝ} {s : Set (E n)}
variable {A B : E n → E n →L[ℝ] E n} {hA : ContDiff ℝ ∞ A} {hB : ContDiff ℝ ∞ B}

theorem add (hn : 0 < n)
    (hAdd : ∀ ψ φ v w, entry (ψ + φ) v w = entry ψ v w + entry φ v w)
    (h : HasDirichletMatrixContractionL2On b entry s hA)
    (h' : HasDirichletMatrixContractionL2On b entry s hB) :
    HasDirichletMatrixContractionL2On b entry s (hA.add hB) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  obtain ⟨F, hF, heF⟩ := h
  obtain ⟨G, hG, heG⟩ := h'
  refine ⟨F + G, hF.add hG, fun ψ hψ => ?_⟩
  rw [dirichletMatrixContraction_add b entry ψ hA hB hAdd, heF ψ hψ, heG ψ hψ]
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  simp_rw [Pi.add_apply, mul_add, integral_add (hI hF) (hI hG)]

theorem of_add_left (hn : 0 < n)
    (hAdd : ∀ ψ φ v w, entry (ψ + φ) v w = entry ψ v w + entry φ v w)
    (h : HasDirichletMatrixContractionL2On b entry s (hA.add hB))
    (h' : HasDirichletMatrixContractionL2On b entry s hA) :
    HasDirichletMatrixContractionL2On b entry s hB := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  obtain ⟨F, hF, heF⟩ := h
  obtain ⟨G, hG, heG⟩ := h'
  refine ⟨F - G, hF.sub hG, fun ψ hψ => ?_⟩
  have he := heF ψ hψ
  rw [dirichletMatrixContraction_add b entry ψ hA hB hAdd, heG ψ hψ] at he
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  simp_rw [Pi.sub_apply, mul_sub, integral_sub (hI hF) (hI hG)]
  linarith only [he]

theorem smul (h : HasDirichletMatrixContractionL2On b entry s hA)
    {m : E n → ℝ} (hm : ContDiff ℝ ∞ m) :
    HasDirichletMatrixContractionL2On b entry s (hm.smul hA) := by
  obtain ⟨F, hF, he⟩ := h
  refine ⟨fun x => m x * F x, memLp_dirichlet_mul_of_continuousOn hm.continuous.continuousOn hF,
    fun ψ hψ => ?_⟩
  rw [dirichletMatrixContraction_smul b entry ψ hA hm,
    he (dirichletTestMul ψ hm) (tsupport_mul_subset_left.trans hψ)]
  simp only [dirichletTestMul_apply, mul_assoc]

theorem of_smul (m : E n → ℝ) (hm : ContDiff ℝ ∞ m) {a : ℝ} (ha : 0 < a)
    (hLower : ∀ x ∈ unitBall n, x ∈ s → a ≤ m x)
    (h : HasDirichletMatrixContractionL2On b entry s (hm.smul hA)) :
    HasDirichletMatrixContractionL2On b entry s hA := by
  obtain ⟨q, hq, hqInv⟩ := exists_smooth_reciprocal_of_pos_threshold ha
  have hqm : ContDiff ℝ ∞ (q ∘ m) := hq.comp hm
  obtain ⟨F, hF, he⟩ := h
  refine ⟨fun x => q (m x) * F x,
    memLp_dirichlet_mul_of_continuousOn hqm.continuous.continuousOn hF, fun ψ hψ => ?_⟩
  let τ := dirichletTestMul ψ hqm
  have hτ : tsupport (τ : E n → ℝ) ⊆ s := tsupport_mul_subset_left.trans hψ
  have hTest : dirichletTestMul τ hm = ψ := by
    apply TestFunction.ext
    intro x
    change (ψ x * q (m x)) * m x = ψ x
    by_cases hx : x ∈ tsupport (ψ : E n → ℝ)
    · rw [mul_assoc, hqInv (m x) (hLower x (ψ.tsupport_subset hx) (hψ hx)), mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have heτ := he τ hτ
  rw [dirichletMatrixContraction_smul b entry τ hA hm, hTest] at heτ
  simpa only [τ, dirichletTestMul_apply, Function.comp_apply, mul_assoc] using heτ

theorem congr (h : HasDirichletMatrixContractionL2On b entry s hA) (he : A = B) :
    HasDirichletMatrixContractionL2On b entry s hB := by
  subst B
  exact h

theorem adjoint (h : HasDirichletMatrixContractionL2On b entry s hA)
    (hAdj : ContDiff ℝ ∞ (fun x => (A x).adjoint))
    (hSym : ∀ ψ v w, entry ψ v w = entry ψ w v) :
    HasDirichletMatrixContractionL2On b entry s hAdj := by
  obtain ⟨F, hF, he⟩ := h
  exact ⟨F, hF, fun ψ hψ => (dirichletMatrixContraction_adjoint b entry ψ hA hAdj hSym).trans (he ψ hψ)⟩

end HasDirichletMatrixContractionL2On

/-- On an annulus, the elliptic contraction and the tangential contractions
determine an L² representative for the contraction with every smooth matrix. -/
theorem hasDirichletMatrixContractionL2On_annulus {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (entry : 𝓓B[n] → E n → E n → ℝ)
    (hAdd : ∀ ψ φ v w, entry (ψ + φ) v w = entry ψ v w + entry φ v w)
    (hEntrySym : ∀ ψ v w, entry ψ v w = entry ψ w v)
    {A B : E n → E n →L[ℝ] E n} (hAc : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hSym : ∀ x, (A x).adjoint = A x) (hBAdj : ContDiff ℝ ∞ (fun x => (B x).adjoint))
    {l r : ℝ} (hl : 0 < l) (hr : 0 < r)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hTrace : HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖} hAc)
    (hTangent : ∀ {D : E n → E n →L[ℝ] E n} (hD : ContDiff ℝ ∞ D),
      HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖}
        (contDiff_dirichletTangentTensor.clm_comp hD)) :
    HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖} hB := by
  let P := dirichletTangentTensor (n := n)
  let R := dirichletRadialTensor (n := n)
  let hP : ContDiff ℝ ∞ P := contDiff_dirichletTangentTensor
  let hR : ContDiff ℝ ∞ R := contDiff_dirichletRadialTensor
  let hR₂ : ContDiff ℝ ∞ (fun x : E n => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hR₄ : ContDiff ℝ ∞ (fun x : E n => ‖x‖ ^ 4) := by
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by decide] using hR₂.pow 2
  have hTerms {D : E n → E n →L[ℝ] E n} (hD : ContDiff ℝ ∞ D)
      (hDAdj : ContDiff ℝ ∞ (fun x => (D x).adjoint)) :
      HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖}
        ((hR₂.smul (hP.clm_comp hD)).add (hR.clm_comp (hD.clm_comp hP))) := by
    have hLeft := (hTangent hD).smul hR₂
    let hRight := hR.clm_comp (hD.clm_comp hP)
    have hEq : (fun x => ((P x).comp ((D x).adjoint.comp (R x))).adjoint) =
        fun x => (R x).comp ((D x).comp (P x)) := by
      funext x
      simp only [P, R, ContinuousLinearMap.adjoint_comp, dirichletTangentTensor_adjoint,
        dirichletRadialTensor_adjoint, ContinuousLinearMap.adjoint_adjoint,
        ContinuousLinearMap.comp_assoc]
    have hAdj : ContDiff ℝ ∞ (fun x => ((P x).comp ((D x).adjoint.comp (R x))).adjoint) := by
      rw [hEq]
      exact hRight
    have hMixed : HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖} hRight :=
      ((hTangent (hDAdj.clm_comp hR)).adjoint hAdj hEntrySym).congr hEq
    exact hLeft.add hn hAdd hMixed
  have hDecomp (D : E n → E n →L[ℝ] E n) :
      (fun x => ‖x‖ ^ 4 • D x) =
        ((fun x => ‖x‖ ^ 2 • (P x).comp (D x)) + (fun x => (R x).comp ((D x).comp (P x)))) +
          (fun x => inner ℝ (D x x) x • R x) := by
    funext x
    exact dirichlet_tangent_radial_coefficient_decomposition x (D x)
  have hAAdj : ContDiff ℝ ∞ (fun x => (A x).adjoint) := by
    simpa only [hSym] using hAc
  let C (x : E n) := inner ℝ (A x x) x
  let hC : ContDiff ℝ ∞ C := (hAc.clm_apply contDiff_id).inner ℝ contDiff_id
  have hWeighted : HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖} (hC.smul hR) :=
    ((hTrace.smul hR₄).congr (hDecomp A)).of_add_left hn hAdd (hTerms hAc hAAdj)
  have hRad : HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖} hR := by
    apply hWeighted.of_smul C hC (a := l * r ^ 2) (by positivity)
    intro x hx hxr
    exact dirichlet_radialCoefficient_ge hl.le hr.le x (le_of_lt hxr) (hE x hx)
  have hCB : ContDiff ℝ ∞ (fun x => inner ℝ (B x x) x) :=
    (hB.clm_apply contDiff_id).inner ℝ contDiff_id
  have hFull := (hTerms hB hBAdj).add hn hAdd (hRad.smul hCB)
  have hScaled : HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖} (hR₄.smul hB) :=
    hFull.congr (hDecomp B).symm
  exact hScaled.of_smul (fun x => ‖x‖ ^ 4) hR₄ (a := r ^ 4) (by positivity)
    (fun x _ hx => pow_le_pow_left₀ hr.le (le_of_lt hx) 4)

end KEBall
