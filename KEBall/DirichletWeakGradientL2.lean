import KEBall.DirichletThirdField

/-! L² directional weak derivatives of scalar forcing on the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

/-- Each constant-direction weak derivative of a scalar function on the
ball is represented in L². -/
def HasDirichletWeakGradientL2 {n : ℕ} (f : E n → ℝ) : Prop :=
  ∀ d : E n, ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
    (∫ x, ψ x * F x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n])

/-- Smooth representatives have the expected weak derivatives. -/
theorem HasDirichletWeakGradientL2.of_smooth_ae {n : ℕ} (hn : 0 < n)
    {f G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : f =ᵐ[ν[n]] G) :
    HasDirichletWeakGradientL2 f := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  intro d
  let DG (x : E n) := fderiv ℝ G x d
  have hDG : ContDiff ℝ ∞ DG := (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hL : MemLp DG 2 ν[n] := MemLp.ae_eq (Eventually.of_forall fun x => mul_one (DG x))
    (memLp_dirichlet_mul_of_continuousOn hDG.continuous.continuousOn (memLp_const (1 : ℝ)))
  refine ⟨DG, hL, fun ψ => ?_⟩
  have h := integral_dirichletTest_fieldDerivative_mul_smooth hn ψ hG (contDiff_const (c := d))
  dsimp only at h
  have hz (x : E n) : dirichletVectorDivergence b[n] (fun _ => d) x = 0 := by
    simp [dirichletVectorDivergence]
  simp only [hz, mul_zero, add_zero] at h
  rw [← neg_neg (∫ x, ψ x * DG x ∂ν[n]), ← h]
  congr 1
  apply integral_congr_ae
  filter_upwards [hRep] with x hx
  rw [hx]

/-- A scalar with an L² weak gradient can be weakly differentiated along
any smooth vector field, using the divergence of the field times the test. -/
theorem dirichletWeakFieldDerivative_of_basis {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f : E n → ℝ}
    (hF : MemLp f 2 ν[n])
    (F : Fin (2 * n) → E n → ℝ) (hF' : ∀ i, MemLp (F i) 2 ν[n])
    (he : ∀ i (ψ : 𝓓B[n]), (∫ x, ψ x * F i x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (b i) * f x ∂ν[n]))
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) :
    let R (x : E n) := ∑ i, inner ℝ (b i) (X x) * F i x
    MemLp R 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (∫ x, ψ x * R x ∂ν[n]) =
        -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) +
          ψ x * dirichletVectorDivergence b X x) * f x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let c (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (X x)
  have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) := (innerSL ℝ (b i)).contDiff.comp hX
  have hLp (i : Fin (2 * n)) : MemLp (fun x => c i x * F i x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hc i).continuous.continuousOn (hF' i)
  refine ⟨memLp_finsetSum Finset.univ fun i _ => hLp i,
    fun ψ => ?_⟩
  let τ (i : Fin (2 * n)) := dirichletTestMul ψ (hc i)
  let D (i : Fin (2 * n)) := dirichletTestFieldDerivative (τ i) (fun _ => b i) contDiff_const
  have hI (φ : 𝓓B[n]) {f : E n → ℝ} (hf : MemLp f 2 ν[n]) :
      Integrable (fun x => φ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hf).integrable (by norm_num)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hI ψ (hLp i))]
  have hT (i : Fin (2 * n)) :
      (∫ x, ψ x * (c i x * F i x) ∂ν[n]) =
        -(∫ x, D i x * f x ∂ν[n]) := by
    have h := he i (τ i)
    change (∫ x, (ψ x * c i x) * F i x ∂ν[n]) = -(∫ x, D i x * f x ∂ν[n]) at h
    simpa only [mul_assoc] using h
  simp_rw [hT, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun i _ => hI (D i) hF)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ i, D i x * f x) = _
    rw [← Finset.sum_mul]
    exact congrArg (fun a : ℝ => a * f x) (sum_dirichletTestFieldDerivative_mul_eq b ψ hX x)

/-- A scalar with an L² weak gradient can be weakly differentiated along
any smooth vector field, using the divergence of the field times the test. -/
theorem HasDirichletWeakGradientL2.exists_fieldDerivative {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f : E n → ℝ}
    (hF : MemLp f 2 ν[n]) (hWeak : HasDirichletWeakGradientL2 f)
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) :
    ∃ R : E n → ℝ, MemLp R 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (∫ x, ψ x * R x ∂ν[n]) =
        -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) +
          ψ x * dirichletVectorDivergence b X x) * f x ∂ν[n]) := by
  have hb (i : Fin (2 * n)) := hWeak (b i)
  choose F hF' he using hb
  exact ⟨_, dirichletWeakFieldDerivative_of_basis hn b hF F hF' he hX⟩

/-- The product rule with an explicitly chosen weak derivative. -/
theorem dirichletWeakDerivative_mul {n : ℕ} (hn : 0 < n)
    {f F c : E n → ℝ} (hf : MemLp f 2 ν[n]) (hF' : MemLp F 2 ν[n])
    (hc : ContDiff ℝ ∞ c) (d : E n)
    (he : ∀ ψ : 𝓓B[n], (∫ x, ψ x * F x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n])) :
    MemLp (fun x => c x * F x + fderiv ℝ c x d * f x) 2 ν[n] ∧
    ∀ ψ : 𝓓B[n], (∫ x, ψ x * (c x * F x + fderiv ℝ c x d * f x) ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * (c x * f x) ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let D (x : E n) := fderiv ℝ c x d
  have hD : ContDiff ℝ ∞ D := (hc.fderiv_right (by simp)).clm_apply contDiff_const
  have hCF : MemLp (fun x => c x * F x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hc.continuous.continuousOn hF'
  have hDf : MemLp (fun x => D x * f x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hD.continuous.continuousOn hf
  have hcf : MemLp (fun x => c x * f x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hc.continuous.continuousOn hf
  refine ⟨hCF.add hDf, fun ψ => ?_⟩
  let τ := dirichletTestMul ψ hc
  let δ := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
  have hI (φ : 𝓓B[n]) {w : E n → ℝ} (hw : MemLp w 2 ν[n]) :
      Integrable (fun x => φ x * w x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hw).integrable (by norm_num)
  have hProduct (x : E n) : fderiv ℝ (τ : E n → ℝ) x d * f x =
      δ x * (c x * f x) + ψ x * (D x * f x) := by
    change fderiv ℝ (fun y => ψ y * c y) x d * f x =
      fderiv ℝ (ψ : E n → ℝ) x d * (c x * f x) + ψ x * (fderiv ℝ c x d * f x)
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (hc.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have h := he τ
  simp_rw [hProduct, integral_add (hI δ hcf) (hI ψ hDf)] at h
  simp only [τ, dirichletTestMul_apply, mul_assoc] at h
  change (∫ x, ψ x * (c x * F x + D x * f x) ∂ν[n]) =
    -(∫ x, δ x * (c x * f x) ∂ν[n])
  simp_rw [mul_add, integral_add (hI ψ hCF) (hI ψ hDf)]
  linarith only [h]

/-- Multiplying by a smooth scalar preserves the L² weak gradient. -/
theorem HasDirichletWeakGradientL2.mul_smooth {n : ℕ} (hn : 0 < n)
    {f c : E n → ℝ} (hF : MemLp f 2 ν[n]) (hWeak : HasDirichletWeakGradientL2 f)
    (hc : ContDiff ℝ ∞ c) : HasDirichletWeakGradientL2 (fun x => c x * f x) := by
  intro d
  obtain ⟨F, hF', he⟩ := hWeak d
  exact ⟨_, dirichletWeakDerivative_mul hn hF hF' hc d he⟩

/-- A weak L² gradient supplies the angular forcing in the rotation equation. -/
theorem HasDirichletWeakGradientL2.exists_angularDerivative {n : ℕ} (hn : 0 < n)
    (g : DirichletBallL2 n ℝ) (hg : HasDirichletWeakGradientL2 (g : E n → ℝ))
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ gS : DirichletBallL2 n ℝ, ∀ ψ : 𝓓B[n],
      (∫ x, ψ x * gS x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n]) := by
  obtain ⟨R, hR, heR⟩ := hg.exists_fieldDerivative hn b[n] (Lp.memLp g) S.contDiff
  refine ⟨hR.toLp R, fun ψ => ?_⟩
  have he : (∫ x, ψ x * hR.toLp R x ∂ν[n]) = ∫ x, ψ x * R x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hR] with x hx
    rw [hx]
  rw [he, heR]
  have hDiv (x : E n) : dirichletVectorDivergence b[n] (S : E n → E n) x = 0 :=
    (dirichletVectorDivergence_basisFun_eq_euclideanDivergence S x).trans
      (euclideanDivergence_skew_field S hS x)
  simp only [hDiv, mul_zero, add_zero]

theorem HasDirichletWeakGradientL2.congr {n : ℕ} {f g : E n → ℝ}
    (hF : HasDirichletWeakGradientL2 f) (hfg : f =ᵐ[ν[n]] g) :
    HasDirichletWeakGradientL2 g := by
  intro d
  obtain ⟨F, hF₂, he⟩ := hF d
  refine ⟨F, hF₂, fun ψ => ?_⟩
  rw [he]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

theorem HasDirichletWeakGradientL2.add {n : ℕ} (hn : 0 < n) {f g : E n → ℝ}
    (hf : MemLp f 2 ν[n]) (hg : MemLp g 2 ν[n])
    (hF : HasDirichletWeakGradientL2 f) (hG : HasDirichletWeakGradientL2 g) :
    HasDirichletWeakGradientL2 (f + g) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  intro d
  obtain ⟨F, hF₂, heF⟩ := hF d
  obtain ⟨G, hG₂, heG⟩ := hG d
  refine ⟨F + G, hF₂.add hG₂, fun ψ => ?_⟩
  let τ := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
  have hI (φ : 𝓓B[n]) {w : E n → ℝ} (hw : MemLp w 2 ν[n]) :
      Integrable (fun x => φ x * w x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hw).integrable (by norm_num)
  change (∫ x, ψ x * (F x + G x) ∂ν[n]) =
    -(∫ x, τ x * (f x + g x) ∂ν[n])
  simp_rw [mul_add]
  rw [integral_add (hI ψ hF₂) (hI ψ hG₂), integral_add (hI τ hf) (hI τ hg), neg_add]
  exact congrArg₂ (· + ·) (heF ψ) (heG ψ)

theorem HasDirichletWeakGradientL2.finsetSum {n : ℕ} {ι : Type*} (hn : 0 < n)
    (s : Finset ι) {f : ι → E n → ℝ} (hf : ∀ i ∈ s, MemLp (f i) 2 ν[n])
    (hF : ∀ i ∈ s, HasDirichletWeakGradientL2 (f i)) :
    HasDirichletWeakGradientL2 (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro d
      exact ⟨0, MemLp.zero, by simp⟩
  | insert i s hi ih =>
      have hs : ∀ j ∈ s, MemLp (f j) 2 ν[n] :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hs' : ∀ j ∈ s, HasDirichletWeakGradientL2 (f j) :=
        fun j hj => hF j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi, Pi.add_def] using
        (hF i (Finset.mem_insert_self i s)).add hn (hf i (Finset.mem_insert_self i s))
          (memLp_finsetSum s hs) (ih hs hs')

/-- Combine a specified family of weak coordinate derivatives in a fixed
direction using the orthonormal coordinates of that direction. -/
theorem dirichletWeakDerivative_of_basis {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f : E n → ℝ} (hf : MemLp f 2 ν[n])
    (F : Fin (2 * n) → E n → ℝ) (hF : ∀ i, MemLp (F i) 2 ν[n])
    (he : ∀ i (ψ : 𝓓B[n]), (∫ x, ψ x * F i x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (b i) * f x ∂ν[n]))
    (d : E n) :
    let R (x : E n) := ∑ i, inner ℝ (b i) d * F i x
    MemLp R 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (∫ x, ψ x * R x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let c (i : Fin (2 * n)) := inner ℝ (b i) d
  have hT (i : Fin (2 * n)) : MemLp (fun x => c i * F i x) 2 ν[n] := (hF i).const_smul (c i)
  refine ⟨memLp_finsetSum Finset.univ fun i _ => hT i,
    fun ψ => ?_⟩
  let τ (i : Fin (2 * n)) := dirichletTestFieldDerivative ψ (fun _ => b i) contDiff_const
  have hI (φ : 𝓓B[n]) {w : E n → ℝ} (hw : MemLp w 2 ν[n]) :
      Integrable (fun x => φ x * w x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hw).integrable (by norm_num)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hI ψ (hT i))]
  have hEq (i : Fin (2 * n)) :
      (∫ x, ψ x * (c i * F i x) ∂ν[n]) =
        -(∫ x, c i * (τ i x * f x) ∂ν[n]) := by
    simp_rw [mul_left_comm (ψ _) (c i), integral_const_mul]
    rw [he i ψ, mul_neg]
    rfl
  simp_rw [hEq, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun i _ => (hI (τ i) hf).const_mul (c i))]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    congr 1
    have he' : (∑ i, c i * τ i x) =
        fderiv ℝ (ψ : E n → ℝ) x (∑ i, c i • b i) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl
    rw [he', b.sum_repr']

/-- L² weak derivatives in the directions of an orthonormal basis suffice
to obtain them in every fixed direction. -/
theorem HasDirichletWeakGradientL2.of_basis {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f : E n → ℝ}
    (hf : MemLp f 2 ν[n])
    (h : ∀ i : Fin (2 * n), ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (∫ x, ψ x * F x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (b i) * f x ∂ν[n])) :
    HasDirichletWeakGradientL2 f := by
  choose F hF he using h
  intro d
  exact ⟨_, dirichletWeakDerivative_of_basis hn b hf F hF he d⟩

end KEBall
