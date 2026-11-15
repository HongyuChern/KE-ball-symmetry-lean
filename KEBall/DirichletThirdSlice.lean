import KEBall.DirichletThirdTrace

/-! Matrix contraction of one constant-direction slice of the third derivative. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- Contract the last two slots of a third distributional derivative against a
smooth matrix, with the first slot held in a fixed direction. -/
noncomputable def dirichletThirdDerivativeSlice {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d : E n) {A : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) : ℝ :=
  ∑ i, ∑ j, dirichletThirdDerivativeEntry u
    (dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hA (b i) (b j))) d (b j) (b i)

private theorem dirichletThirdDerivativeEntry_zero {n : ℕ} (u : DirichletSobolev n)
    (d e w : E n) : dirichletThirdDerivativeEntry u 0 d e w = 0 := by
  have hTest : dirichletTestFieldDerivative (0 : 𝓓(dirichletBallOpens n, ℝ))
      (fun _ => d) contDiff_const = 0 := by
    apply TestFunction.ext
    intro x
    change fderiv ℝ (fun _ : E n => (0 : ℝ)) x d = 0
    simp
  simp [dirichletThirdDerivativeEntry, hTest, dirichletHessianEntry]

theorem dirichletThirdDerivativeTrace_const_basis {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (k : Fin (2 * n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) :
    dirichletThirdDerivativeTrace b u ψ hA (contDiff_const (c := b k)) =
      dirichletThirdDerivativeSlice b u ψ (b k) hA := by
  unfold dirichletThirdDerivativeTrace dirichletThirdDerivativeSlice
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  let τ := dirichletTestMul ψ (contDiff_dirichletCoefficientEntry hA (b i) (b j))
  have hTest (l : Fin (2 * n)) :
      dirichletTestMul τ ((innerSL ℝ (b l)).contDiff.comp (contDiff_const (c := b k))) =
        if l = k then τ else 0 := by
    by_cases h : l = k
    · subst l
      simp only [if_true]
      apply TestFunction.ext
      intro x
      simp [dirichletTestMul_apply]
    · simp only [if_neg h]
      apply TestFunction.ext
      intro x
      simp [dirichletTestMul_apply, orthonormal_iff_ite.mp b.orthonormal l k, h]
  change (∑ l, dirichletThirdDerivativeEntry u
    (dirichletTestMul τ ((innerSL ℝ (b l)).contDiff.comp (contDiff_const (c := b k))))
      (b l) (b j) (b i)) = _
  simp_rw [hTest]
  rw [Fintype.sum_eq_single k (fun l hl => by
    rw [if_neg hl]
    simp [dirichletThirdDerivativeEntry_zero])]
  simp [τ]

theorem dirichletThirdDerivativeEntry_add {n : ℕ} (hn : 0 < n)
    (u : DirichletSobolev n) (ψ χ : 𝓓(dirichletBallOpens n, ℝ)) (d e w : E n) :
    dirichletThirdDerivativeEntry u (ψ + χ) d e w =
      dirichletThirdDerivativeEntry u ψ d e w + dirichletThirdDerivativeEntry u χ d e w := by
  have hTest :
      dirichletTestFieldDerivative (ψ + χ) (fun _ => d) contDiff_const =
      dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const +
        dirichletTestFieldDerivative χ (fun _ => d) contDiff_const := by
    apply TestFunction.ext
    intro x
    change fderiv ℝ (fun y => ψ y + χ y) x d =
      fderiv ℝ (ψ : E n → ℝ) x d + fderiv ℝ (χ : E n → ℝ) x d
    rw [fderiv_fun_add (ψ.contDiff.differentiable (by simp) x)
      (χ.contDiff.differentiable (by simp) x), add_apply]
  simp only [dirichletThirdDerivativeEntry, hTest, dirichletHessianEntry_add hn, neg_add]

private theorem dirichletThirdDerivativeEntry_sum {n : ℕ} {ι : Type*} (hn : 0 < n)
    (u : DirichletSobolev n) (s : Finset ι) (ψ : ι → 𝓓(dirichletBallOpens n, ℝ))
    (d e w : E n) :
    dirichletThirdDerivativeEntry u (∑ i ∈ s, ψ i) d e w =
      ∑ i ∈ s, dirichletThirdDerivativeEntry u (ψ i) d e w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [dirichletThirdDerivativeEntry_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, dirichletThirdDerivativeEntry_add hn, ih]

theorem dirichletThirdDerivativeSlice_add {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d : E n) {A B : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    dirichletThirdDerivativeSlice b u ψ d (hA.add hB) =
      dirichletThirdDerivativeSlice b u ψ d hA + dirichletThirdDerivativeSlice b u ψ d hB := by
  unfold dirichletThirdDerivativeSlice
  simp_rw [← Finset.sum_add_distrib, ← dirichletThirdDerivativeEntry_add hn]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply TestFunction.ext
  intro x
  simp [add_apply, inner_add_right, mul_add]

theorem dirichletThirdDerivativeSlice_smul {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {m : E n → ℝ} (hm : ContDiff ℝ ∞ m) :
    dirichletThirdDerivativeSlice b u ψ d (hm.smul hA) =
      dirichletThirdDerivativeSlice b u (dirichletTestMul ψ hm) d hA := by
  unfold dirichletThirdDerivativeSlice
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply TestFunction.ext
  intro x
  simp [real_inner_smul_right, mul_assoc]

theorem dirichletThirdDerivativeSlice_adjoint {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hAdj : ContDiff ℝ ∞ (fun x => (A x).adjoint)) :
    dirichletThirdDerivativeSlice b u ψ d hAdj = dirichletThirdDerivativeSlice b u ψ d hA := by
  unfold dirichletThirdDerivativeSlice
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [dirichletThirdDerivativeEntry_comm₂₃ u _ d (b j) (b i)]
  congr 1
  apply TestFunction.ext
  intro x
  simp only [dirichletTestMul_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm]

theorem dirichletThirdDerivativeSlice_congr {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d : E n)
    {A B : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (he : A = B) :
    dirichletThirdDerivativeSlice b u ψ d hA = dirichletThirdDerivativeSlice b u ψ d hB := by
  subst B
  rfl

/-- Square-integrable representatives of the tangential derivatives of
the Hessian entries give an L² contraction with any matrix followed by the
tangential projection. -/
theorem exists_dirichletThirdDerivativeSlice_tangentComp {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n) (d : E n)
    (hTan : ∀ e w z : E n, ∃ F T : E n → ℝ, MemLp F 2 ν[n] ∧ MemLp T 2 ν[n] ∧
      ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        dirichletHessianEntry u ψ e w = (∫ x, ψ x * F x ∂ν[n]) ∧
        (∫ x, ψ x * T x ∂ν[n]) =
          -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • z - inner ℝ z x • x) +
            ((1 - (2 : ℝ) * n) * inner ℝ z x) * ψ x) * F x ∂ν[n]))
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeSlice b u ψ d (contDiff_dirichletTangentTensor.clm_comp hB) =
        ∫ x, ψ x * T x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let P := dirichletTangentTensor (n := n)
  let hP : ContDiff ℝ ∞ P := contDiff_dirichletTangentTensor
  let X (j : Fin (2 * n)) (x : E n) := P x (b j)
  let hX (j : Fin (2 * n)) : ContDiff ℝ ∞ (X j) := hP.clm_apply contDiff_const
  have hTan' (i j : Fin (2 * n)) := hTan d (b i) (b j)
  choose F T hF hT he using hTan'
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hB (b i) (b j)
  have hTerm (i j : Fin (2 * n)) : MemLp (fun x => c i j x * T i j x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hc i j).continuous.continuousOn (hT i j)
  have hSum (i : Fin (2 * n)) : MemLp (fun x => ∑ j, c i j x * T i j x) 2 ν[n] :=
    memLp_finsetSum Finset.univ fun j _ => hTerm i j
  refine ⟨fun x => ∑ i, ∑ j, c i j x * T i j x,
    memLp_finsetSum Finset.univ (fun i _ => hSum i), fun ψ => ?_⟩
  let φ (i j : Fin (2 * n)) := dirichletTestMul ψ (hc i j)
  let τ (i j k : Fin (2 * n)) := dirichletTestMul (φ i j) ((innerSL ℝ (b k)).contDiff.comp (hX j))
  have hField (i j : Fin (2 * n)) :
      (∑ k, dirichletThirdDerivativeEntry u (τ i j k) (b k) d (b i)) =
        ∫ x, ψ x * (c i j x * T i j x) ∂ν[n] := by
    change (∑ k, dirichletThirdDerivativeEntry u
      (dirichletTestMul (φ i j) ((innerSL ℝ (b k)).contDiff.comp (hX j)))
      (b k) d (b i)) = _
    rw [sum_dirichletThirdDerivativeEntry_eq_field hn b u (φ i j) d (b i)
      (hX j) (hF i j) (fun χ => (he i j χ).1)]
    have hDiv (x : E n) : dirichletVectorDivergence b (X j) x =
        (1 - (2 : ℝ) * n) * inner ℝ (b j) x :=
      dirichletVectorDivergence_tangentTensor b (b j) x
    simp_rw [hDiv, mul_comm (φ i j _)]
    simp only [X, P, dirichletTangentTensor_apply]
    rw [← (he i j (φ i j)).2]
    simp only [φ, dirichletTestMul_apply, mul_assoc]
  have hTest (i k : Fin (2 * n)) :
      dirichletTestMul ψ
        (contDiff_dirichletCoefficientEntry (hP.clm_comp hB) (b i) (b k)) =
      ∑ j, τ i j k := by
    apply TestFunction.ext
    intro x
    change ψ x * inner ℝ (b k) (P x (B x (b i))) = (∑ j, τ i j k) x
    rw [← b.sum_repr' (B x (b i)), map_sum, inner_sum]
    let ev : 𝓓(dirichletBallOpens n, ℝ) →+ ℝ :=
      { toFun := fun χ => χ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    rw [show (∑ j, τ i j k) x = ∑ j, τ i j k x from map_sum ev _ _]
    simp only [map_smul, real_inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ψ x * (c i j x * _) = (ψ x * c i j x) * _
    rw [mul_assoc]
    rfl
  unfold dirichletThirdDerivativeSlice
  simp_rw [hTest, dirichletThirdDerivativeEntry_sum hn]
  have hSwap : (∑ i, ∑ k, ∑ j, dirichletThirdDerivativeEntry u (τ i j k) d (b k) (b i)) =
      ∑ i, ∑ j, ∑ k, dirichletThirdDerivativeEntry u (τ i j k) (b k) d (b i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      dirichletThirdDerivativeEntry_comm₁₂ u _ d (b k) (b i)
  rw [hSwap]
  simp_rw [hField, Finset.mul_sum]
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI (hTerm i j)))]
  exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ (fun j _ => hI (hTerm i j))).symm

theorem dirichletThirdDerivativeSlice_rankOne_basis {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d : E n) (i j : Fin (2 * n)) :
    dirichletThirdDerivativeSlice b u ψ d (contDiff_const (c := rankOne ℝ (b j) (b i))) =
      dirichletThirdDerivativeEntry u ψ d (b j) (b i) := by
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
  change dirichletThirdDerivativeSlice b u ψ d hB = _
  unfold dirichletThirdDerivativeSlice
  simp_rw [hTest]
  rw [Fintype.sum_eq_single i (fun a ha => by simp [ha, dirichletThirdDerivativeEntry_zero])]
  rw [Fintype.sum_eq_single j (fun c hc => by simp [hc, dirichletThirdDerivativeEntry_zero])]
  simp

end KEBall
