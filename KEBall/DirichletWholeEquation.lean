import KEBall.DirichletWholeTranslation

/-! An energy estimate for translation difference quotients of the weak equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal

namespace KEBall

private noncomputable def euclideanCoefficientEval (n : ℕ) :
    (E n →L[ℝ] E n) →L[ℝ] E n →L[ℝ] E n :=
  (ContinuousLinearMap.apply (E := E n) ℝ (E n)).flip

/-- Application of an essentially bounded coefficient field to an ambient L² field. -/
noncomputable def euclideanCoefficientAction {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ (volume0 n)) : EuclideanL2 n (E n) →L[ℝ] EuclideanL2 n (E n) :=
  (euclideanCoefficientEval n).holderL (volume0 n) ⊤ 2 2 (hA.toLp A)

theorem euclideanCoefficientAction_ae {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ (volume0 n)) (f : EuclideanL2 n (E n)) :
    euclideanCoefficientAction hA f =ᵐ[volume0 n] fun x => A x (f x) := by
  refine ((euclideanCoefficientEval n).coeFn_holder (hA.toLp A) f).trans ?_
  filter_upwards [MemLp.coeFn_toLp hA] with x hx
  change (hA.toLp A) x (f x) = A x (f x)
  rw [hx]

private theorem norm_euclideanCoefficientAction_le {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ (volume0 n)) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂volume0 n, ‖A x‖ ≤ C) (v : EuclideanL2 n (E n)) :
    ‖euclideanCoefficientAction hA v‖ ≤ C * ‖v‖ := by
  have hEval : ‖euclideanCoefficientEval n‖ ≤ 1 := by
    apply (euclideanCoefficientEval n).opNorm_le_bound₂ (by norm_num)
    intro T x
    simpa only [euclideanCoefficientEval, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.apply_apply, one_mul] using T.le_opNorm x
  have hNorm : ‖hA.toLp A‖ ≤ C := by
    rw [Lp.norm_toLp, eLpNorm_exponent_top]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hBound)).trans_eq
      (ENNReal.toReal_ofReal hC)
  change ‖(euclideanCoefficientEval n).holder 2 (hA.toLp A) v‖ ≤ _
  calc
    _ ≤ ‖euclideanCoefficientEval n‖ * ‖hA.toLp A‖ * ‖v‖ :=
      (euclideanCoefficientEval n).norm_holder_apply_apply_le (hA.toLp A) v
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul hEval hNorm (norm_nonneg _) zero_le_one) (norm_nonneg v)

/-- The whole-space divergence-form equation on the closed Sobolev graph. -/
def IsEuclideanWeakSolution {n : ℕ} {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ (volume0 n))
    (g : EuclideanL2 n ℝ) (u : EuclideanSobolev n) : Prop :=
  ∀ w : EuclideanSobolev n,
    inner ℝ (euclideanCoefficientAction hA (u : EuclideanL2Pair n).snd) (w : EuclideanL2Pair n).snd =
      inner ℝ g (w : EuclideanL2Pair n).fst

/-- The smooth test formulation extends to all graph tests by continuity. -/
theorem IsEuclideanWeakSolution.of_test {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ (volume0 n)) (g : EuclideanL2 n ℝ) (u : EuclideanSobolev n)
    (hTest : ∀ ψ : 𝓓((⊤ : Opens (E n)), ℝ),
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((u : EuclideanL2Pair n).snd x)) ∂volume0 n) =
        ∫ x, ψ x * g x ∂volume0 n) :
    IsEuclideanWeakSolution hA g u := by
  let F := euclideanCoefficientAction hA (u : EuclideanL2Pair n).snd
  let L : EuclideanL2Pair n →L[ℝ] ℝ := (innerSL ℝ F).comp (WithLp.sndL 2 ℝ _ _)
  let R : EuclideanL2Pair n →L[ℝ] ℝ := (innerSL ℝ g).comp (WithLp.fstL 2 ℝ _ _)
  let S : Set (EuclideanL2Pair n) := {z | L z = R z}
  have hClosed : IsClosed S := isClosed_eq L.continuous R.continuous
  have hRange : ((compactTestL2Graph (volume0 n) (Ω := ⊤)).range : Set (EuclideanL2Pair n)) ⊆ S := by
    rintro _ ⟨ψ, rfl⟩
    change inner ℝ F (compactTestGradientToL2 (volume0 n) ψ) =
      inner ℝ g (compactTestToL2 (volume0 n) ψ)
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine Eq.trans ?_ ((hTest ψ).trans ?_)
    · apply integral_congr_ae
      filter_upwards [euclideanCoefficientAction_ae hA (u : EuclideanL2Pair n).snd,
        compactTestGradientToL2_ae (volume0 n) ψ] with x hF hψ
      change F x = _ at hF
      rw [hF, hψ, real_inner_comm, inner_gradient_left]
    · apply integral_congr_ae
      filter_upwards [compactTestToL2_ae (volume0 n) ψ] with x hx
      rw [hx, Real.inner_apply, mul_comm]
  intro w
  exact closure_minimal hRange hClosed w.property

theorem euclideanL2Translate_inner {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (a : E n) (f g : EuclideanL2 n F) :
    inner ℝ (euclideanL2Translate a f) g = inner ℝ f (euclideanL2Translate (-a) g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ x, inner ℝ (f (x + a)) (g x) ∂volume0 n := by
      apply integral_congr_ae
      filter_upwards [euclideanL2Translate_ae a f] with x hx
      rw [hx]
    _ = ∫ x, inner ℝ (f x) (g (x + -a)) ∂volume0 n := by
      have h := (euclideanTranslate_measurePreserving a).integral_comp
        (Homeomorph.addRight a).toMeasurableEquiv.measurableEmbedding
        (fun x => inner ℝ (f x) (g (x + -a)))
      simpa only [add_neg_cancel_right] using h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [euclideanL2Translate_ae (-a) g] with x hx
      rw [hx]

private theorem euclideanCoefficientAction_coercive {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ (volume0 n)) {l : ℝ}
    (hE : ∀ᵐ x ∂volume0 n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (z : EuclideanL2 n (E n)) :
    l * ‖z‖ ^ 2 ≤ inner ℝ (euclideanCoefficientAction hA z) z := by
  rw [← real_inner_self_eq_norm_sq z, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  rw [← integral_const_mul]
  have hi : Integrable (fun x => ‖z x‖ ^ 2) (volume0 n) := by
    simpa only [real_inner_self_eq_norm_sq] using MeasureTheory.L2.integrable_inner (𝕜 := ℝ) z z
  apply integral_mono_ae (hi.const_mul _) (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) _ _)
  filter_upwards [hE, euclideanCoefficientAction_ae hA z] with x hx hx'
  rw [hx']
  exact hx (z x)

set_option maxHeartbeats 900000 in
/-- The weak equation controls the whole-space gradient of each difference
quotient using the L² forcing and the Lipschitz coefficient field. -/
theorem norm_euclideanSobolevDifferenceQuotient_gradient_le {n : ℕ}
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ (volume0 n)) {l : ℝ}
    (hE : ∀ᵐ x ∂volume0 n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLip : LipschitzWith K A)
    {g : EuclideanL2 n ℝ} {u : EuclideanSobolev n} (hu : IsEuclideanWeakSolution hA g u)
    (v : E n) {h : ℝ} (hh : h ≠ 0) :
    l * ‖(euclideanSobolevDifferenceQuotient v h u : EuclideanL2Pair n).snd‖ ≤
      (‖g‖ + (K : ℝ) * ‖(u : EuclideanL2Pair n).snd‖) * ‖v‖ := by
  let μ := volume0 n
  let a := h • v
  let U := (u : EuclideanL2Pair n).snd
  let UT := euclideanL2Translate a U
  let q := euclideanSobolevDifferenceQuotient v h u
  let Z := (q : EuclideanL2Pair n).snd
  let p := (q : EuclideanL2Pair n).fst
  let F := euclideanCoefficientAction hA U
  let FT := euclideanL2Translate a F
  let D : EuclideanL2 n (E n) := h⁻¹ • (FT - F)
  let pT := euclideanL2Translate (-a) p
  let B (x : E n) := h⁻¹ • (A x - A (x + a))
  have hB : MemLp B ⊤ μ :=
    (hA.sub (hA.comp_measurePreserving (euclideanTranslate_measurePreserving a))).const_smul h⁻¹
  let P := euclideanCoefficientAction hB UT
  have hZ : Z = h⁻¹ • (UT - U) := rfl
  have hP : euclideanCoefficientAction hA Z = D + P := by
    apply Lp.ext
    filter_upwards [euclideanCoefficientAction_ae hA Z, Lp.coeFn_add D P,
      euclideanCoefficientAction_ae hB UT, euclideanL2Translate_ae a U,
      euclideanL2Translate_ae a F,
      (euclideanTranslate_measurePreserving a).quasiMeasurePreserving.tendsto_ae.eventually
        (euclideanCoefficientAction_ae hA U),
      euclideanCoefficientAction_ae hA U, Lp.coeFn_smul h⁻¹ (UT - U), Lp.coeFn_sub UT U,
      Lp.coeFn_smul h⁻¹ (FT - F), Lp.coeFn_sub FT F] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁
    change UT x = U (x + a) at h₄
    change FT x = F (x + a) at h₅
    change F (x + a) = A (x + a) (U (x + a)) at h₆
    change F x = A x (U x) at h₇
    have h₈' : Z x = h⁻¹ • (U (x + a) - U x) := by
      rw [hZ, h₈, Pi.smul_apply, h₉, Pi.sub_apply, h₄]
    have h₁₀' : D x = h⁻¹ • (A (x + a) (U (x + a)) - A x (U x)) := by
      change (h⁻¹ • (FT - F)) x = _
      rw [h₁₀, Pi.smul_apply, h₁₁, Pi.sub_apply, h₅, h₆, h₇]
    rw [h₁, h₂, Pi.add_apply, h₃, h₈', h₁₀', h₄]
    simp only [B, map_smul, map_sub, smul_apply, sub_apply, ← smul_add]
    congr 1
    abel
  have hBbound (x : E n) : ‖B x‖ ≤ (K : ℝ) * ‖v‖ := by
    have hd := hLip.dist_le_mul x (x + a)
    rw [dist_eq_norm, dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg] at hd
    rw [show ‖a‖ = ‖h‖ * ‖v‖ from norm_smul _ _, Real.norm_eq_abs] at hd
    change ‖h⁻¹ • (A x - A (x + a))‖ ≤ _
    rw [norm_smul, norm_inv, Real.norm_eq_abs]
    calc
      _ ≤ |h|⁻¹ * ((K : ℝ) * (|h| * ‖v‖)) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by field_simp [abs_ne_zero.mpr hh]
  have hPbound : inner ℝ P Z ≤ ((K : ℝ) * ‖v‖ * ‖U‖) * ‖Z‖ := by
    have hN := norm_euclideanCoefficientAction_le hB (by positivity)
      (Eventually.of_forall hBbound) UT
    change ‖P‖ ≤ (K : ℝ) * ‖v‖ * ‖UT‖ at hN
    rw [show ‖UT‖ = ‖U‖ from (euclideanL2Translate a).norm_map U] at hN
    exact (real_inner_le_norm P Z).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg Z))
  have hData : inner ℝ D Z = inner ℝ g (h⁻¹ • (pT - p)) := by
    have hshift := hu (euclideanSobolevTranslate (-a) q)
    change inner ℝ F (euclideanL2Translate (-a) Z) = inner ℝ g pT at hshift
    have hbase := hu q
    change inner ℝ F Z = inner ℝ g p at hbase
    change inner ℝ (h⁻¹ • (FT - F)) Z = _
    rw [real_inner_smul_left, inner_sub_left, real_inner_smul_right, inner_sub_right,
      show inner ℝ FT Z = inner ℝ F (euclideanL2Translate (-a) Z) from euclideanL2Translate_inner a F Z,
      hshift, hbase]
  have hNorm : ‖h⁻¹ • (pT - p)‖ ≤ ‖v‖ * ‖Z‖ := by
    have hBound := norm_euclideanSobolevDifferenceQuotient_value_le q v (neg_ne_zero.mpr hh)
    change ‖(-h)⁻¹ • (euclideanL2Translate ((-h) • v) p - p)‖ ≤ ‖v‖ * ‖Z‖ at hBound
    simpa only [neg_smul, ← show -a = -(h • v) from rfl, norm_smul, norm_inv, norm_neg, pT] using hBound
  have hDBound : inner ℝ D Z ≤ (‖g‖ * ‖v‖) * ‖Z‖ := by
    rw [hData, mul_assoc]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hNorm (norm_nonneg g))
  have hCoer := euclideanCoefficientAction_coercive hA hE Z
  rw [hP, inner_add_left] at hCoer
  have hEnergy : (l * ‖Z‖) * ‖Z‖ ≤
      ((‖g‖ + (K : ℝ) * ‖U‖) * ‖v‖) * ‖Z‖ := by
    nlinarith only [hCoer, hDBound, hPbound]
  change l * ‖Z‖ ≤ _
  rcases (norm_nonneg Z).lt_or_eq with hz | hz
  · exact (mul_le_mul_iff_of_pos_right hz).mp hEnergy
  · rw [← hz, mul_zero]
    positivity

end KEBall
