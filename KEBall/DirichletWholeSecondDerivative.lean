import KEBall.DirichletInteriorCoefficients

/-! Identification of the weak limit of the gradient difference quotients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bornology Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions NNReal Topology

namespace KEBall

private theorem tendsto_integral_translate_test {n : ℕ}
    (ψ : 𝓓((⊤ : Opens (E n)), ℝ)) (v : E n)
    {f : E n → ℝ} (hf : MemLp f 2 (volume0 n)) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝[≠] 0)) (ht₀ : ∀ j, t j ≠ 0) (ht₁ : ∀ j, |t j| ≤ 1) :
    Tendsto (fun j => ∫ x, ((t j)⁻¹ * (ψ (x + (-t j) • v) - ψ x)) * f x ∂volume0 n)
      atTop (𝓝 (-(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * f x ∂volume0 n))) := by
  obtain ⟨k, hLip⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport ψ.contDiff ψ.hasCompactSupport
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : E n)).mp ψ.hasCompactSupport.isBounded
  let C := closedBall (0 : E n) (R + ‖v‖)
  let F := C.indicator f
  have hF : Integrable F (volume0 n) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      ((hf.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _))
  have hSmall (j : ℕ) : ‖(-t j) • v‖ ≤ ‖v‖ := by
    rw [norm_smul, norm_neg, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (ht₁ j)
  have hOff (j : ℕ) (x : E n) (hx : x ∉ C) : ψ (x + (-t j) • v) = 0 ∧ ψ x = 0 := by
    have h₁ : x + (-t j) • v ∉ tsupport (ψ : E n → ℝ) := by
      intro h
      apply hx
      apply mem_closedBall_zero_iff.mpr
      calc
        ‖x‖ = ‖x + (-t j) • v - (-t j) • v‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖x + (-t j) • v‖ + ‖(-t j) • v‖ := norm_sub_le _ _
        _ ≤ R + ‖v‖ := add_le_add (mem_closedBall_zero_iff.mp (hR h)) (hSmall j)
    have h₂ : x ∉ tsupport (ψ : E n → ℝ) := by
      intro h
      exact hx (mem_closedBall_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hR h)).trans
        (le_add_of_nonneg_right (norm_nonneg _))))
    exact ⟨image_eq_zero_of_notMem_tsupport h₁, image_eq_zero_of_notMem_tsupport h₂⟩
  rw [← integral_neg]
  apply tendsto_integral_of_dominated_convergence (fun x => ((k : ℝ) * ‖v‖) * ‖F x‖)
  · intro j
    have hC : Continuous (fun x => (t j)⁻¹ * (ψ (x + (-t j) • v) - ψ x)) :=
      continuous_const.mul ((ψ.continuous.comp (continuous_id.add continuous_const)).sub ψ.continuous)
    exact hC.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hF.norm.const_mul _
  · intro j
    filter_upwards with x
    by_cases hx : x ∈ C
    · have hMove := hLip.dist_le_mul (x + (-t j) • v) x
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_neg, Real.norm_eq_abs] at hMove
      simp only [F, indicator_of_mem hx, norm_mul, Real.norm_eq_abs ((t j)⁻¹), abs_inv]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        _ ≤ |t j|⁻¹ * ((k : ℝ) * (|t j| * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hMove (by positivity)
        _ = _ := by field_simp [abs_ne_zero.mpr (ht₀ j)]
    · obtain ⟨h₁, h₂⟩ := hOff j x hx
      rw [h₁, h₂]
      simp [F, indicator_of_notMem hx]
  · filter_upwards with x
    have hγ : HasDerivAt (fun s : ℝ => x + s • (-v)) (-v) 0 := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (-v)).const_add x
    have hD := ((ψ.contDiff.differentiable (by simp) x).hasFDerivAt).comp_hasDerivAt_of_eq
      (0 : ℝ) hγ (by simp)
    have hN : HasDerivAt (fun s : ℝ => ψ (x + (-s) • v))
        (-(fderiv ℝ (ψ : E n → ℝ) x v)) 0 := by
      simpa only [Function.comp_def, smul_neg, neg_smul, map_neg] using hD
    have hSlope := (hasDerivAt_iff_tendsto_slope_zero.mp hN).comp ht
    have hLim : Tendsto (fun j => (t j)⁻¹ * (ψ (x + (-t j) • v) - ψ x))
        atTop (𝓝 (-(fderiv ℝ (ψ : E n → ℝ) x v))) := by
      simpa only [Function.comp_def, zero_add, neg_zero, zero_smul, add_zero, smul_eq_mul] using hSlope
    simpa only [neg_mul] using hLim.mul_const (f x)

private noncomputable def euclideanVectorTest {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ψ : 𝓓((⊤ : Opens (E n)), ℝ))
    (e : F) : 𝓓((⊤ : Opens (E n)), F) :=
  ⟨fun x => ψ x • e, ψ.contDiff.smul contDiff_const, ψ.hasCompactSupport.smul_right, subset_univ _⟩

private theorem euclideanL2_differenceQuotient_test {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (U : EuclideanL2 n F) (ψ : 𝓓((⊤ : Opens (E n)), ℝ)) (v : E n) (e : F) (h : ℝ) :
    let Q := h⁻¹ • (euclideanL2Translate (h • v) U - U)
    (∫ x, ψ x * inner ℝ e (Q x) ∂volume0 n) =
      ∫ x, (h⁻¹ * (ψ (x + (-h) • v) - ψ x)) * inner ℝ e (U x) ∂volume0 n := by
  let Q := h⁻¹ • (euclideanL2Translate (h • v) U - U)
  let a := h • v
  let V := compactTestToL2 (volume0 n) (euclideanVectorTest ψ e)
  let T := euclideanL2Translate (-a) V
  have hTransfer : inner ℝ T U = inner ℝ V (euclideanL2Translate a U) := by
    simpa only [T, neg_neg] using euclideanL2Translate_inner (-a) V U
  have hPush : inner ℝ V Q = inner ℝ (h⁻¹ • (T - V)) U := by
    change inner ℝ V (h⁻¹ • (euclideanL2Translate a U - U)) = _
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_left, inner_sub_left, hTransfer]
  have hL : inner ℝ V Q = ∫ x, ψ x * inner ℝ e (Q x) ∂volume0 n := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [compactTestToL2_ae (volume0 n) (euclideanVectorTest ψ e)] with x hx
    change V x = ψ x • e at hx
    rw [hx, real_inner_smul_left]
  have hR : inner ℝ (h⁻¹ • (T - V)) U =
      ∫ x, (h⁻¹ * (ψ (x + (-h) • v) - ψ x)) * inner ℝ e (U x) ∂volume0 n := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul h⁻¹ (T - V), Lp.coeFn_sub T V,
      euclideanL2Translate_ae (-a) V, compactTestToL2_ae (volume0 n) (euclideanVectorTest ψ e),
      (euclideanTranslate_measurePreserving (-a)).quasiMeasurePreserving.tendsto_ae.eventually
        (compactTestToL2_ae (volume0 n) (euclideanVectorTest ψ e))] with x h₁ h₂ h₃ h₄ h₅
    change T x = V (x + -a) at h₃
    change V x = ψ x • e at h₄
    change V (x + -a) = ψ (x + -a) • e at h₅
    rw [h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, h₄, h₅]
    simp only [a, neg_smul, inner_sub_left, real_inner_smul_left, mul_sub]
    ring
  exact hL.symm.trans (hPush.trans hR)

set_option maxHeartbeats 700000 in
/-- A whole-space weak solution has a directional derivative in the
function–gradient graph, with both components identified on smooth tests. -/
theorem exists_euclideanSobolev_weakDerivative {n : ℕ}
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ (volume0 n)) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂volume0 n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLip : LipschitzWith K A)
    {g : EuclideanL2 n ℝ} {u : EuclideanSobolev n} (hu : IsEuclideanWeakSolution hA g u)
    (v : E n) :
    ∃ w : EuclideanSobolev n,
      (∀ ψ : 𝓓((⊤ : Opens (E n)), ℝ),
        (∫ x, ψ x * (w : EuclideanL2Pair n).fst x ∂volume0 n) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * (u : EuclideanL2Pair n).fst x ∂volume0 n)) ∧
      (∀ (ψ : 𝓓((⊤ : Opens (E n)), ℝ)) (e : E n),
        (∫ x, ψ x * inner ℝ e ((w : EuclideanL2Pair n).snd x) ∂volume0 n) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ e ((u : EuclideanL2Pair n).snd x) ∂volume0 n)) := by
  let t (j : ℕ) := 1 / ((j : ℝ) + 1)
  have ht₀ (j : ℕ) : t j ≠ 0 := by dsimp [t]; positivity
  have ht₁ (j : ℕ) : |t j| ≤ 1 := by
    dsimp [t]
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    simp
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun j => ht₀ j⟩
  let q (j : ℕ) := euclideanSobolevDifferenceQuotient v (t j) u
  let C₀ := ‖v‖ * ‖(u : EuclideanL2Pair n).snd‖
  let C₁ := ((‖g‖ + (K : ℝ) * ‖(u : EuclideanL2Pair n).snd‖) * ‖v‖) / l
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hQ (j : ℕ) : ‖q j‖ ≤ C₀ + C₁ := by
    have hF : ‖(q j : EuclideanL2Pair n).fst‖ ≤ C₀ :=
      norm_euclideanSobolevDifferenceQuotient_value_le u v (ht₀ j)
    have hG : ‖(q j : EuclideanL2Pair n).snd‖ ≤ C₁ :=
      (le_div_iff₀ hl).mpr (by
        rw [mul_comm]
        exact norm_euclideanSobolevDifferenceQuotient_gradient_le hA hE hLip hu v (ht₀ j))
    have h := WithLp.prod_norm_sq_eq_of_L2 (q j : EuclideanL2Pair n)
    have h₀ := pow_le_pow_left₀ (norm_nonneg _) hF 2
    have h₁ := pow_le_pow_left₀ (norm_nonneg _) hG 2
    have hMul := mul_nonneg hC₀ hC₁
    change ‖(q j : EuclideanL2Pair n)‖ ≤ C₀ + C₁
    apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hC₀ hC₁)).mp
    nlinarith only [h, h₀, h₁, hMul]
  obtain ⟨w, hw⟩ := realHilbert_exists_weakClusterPoint_of_bound hQ
  have hPair {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      (P : EuclideanSobolev n →L[ℝ] EuclideanL2 n F)
      (hP : ∀ j, P (q j) = (t j)⁻¹ • (euclideanL2Translate ((t j) • v) (P u) - P u))
      (ψ : 𝓓((⊤ : Opens (E n)), ℝ)) (e : F) :
      (∫ x, ψ x * inner ℝ e (P w x) ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ e (P u x) ∂volume0 n) := by
    let V := compactTestToL2 (volume0 n) (euclideanVectorTest ψ e)
    let L : EuclideanSobolev n →L[ℝ] ℝ := (innerSL ℝ V).comp P
    have hL (z : EuclideanSobolev n) : L z = ∫ x, ψ x * inner ℝ e (P z x) ∂volume0 n := by
      change inner ℝ V (P z) = _
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [compactTestToL2_ae (volume0 n) (euclideanVectorTest ψ e)] with x hx
      change V x = ψ x • e at hx
      rw [hx, real_inner_smul_left]
    have hLc : Continuous (fun z : WeakSpace ℝ (EuclideanSobolev n) =>
        L ((toWeakSpace ℝ (EuclideanSobolev n)).symm z)) :=
      WeakBilin.eval_continuous (topDualPairing ℝ (EuclideanSobolev n)).flip L
    have hCluster : MapClusterPt (L w) atTop (fun j => L (q j)) :=
      MapClusterPt.continuousAt_comp (X := WeakSpace ℝ (EuclideanSobolev n)) hLc.continuousAt hw
    have hLim : Tendsto (fun j => L (q j)) atTop
        (𝓝 (-(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ e (P u x) ∂volume0 n))) := by
      apply (tendsto_integral_translate_test ψ v ((Lp.memLp (P u)).const_inner e) ht ht₀ ht₁).congr
      intro j
      rw [hL, hP j]
      exact (euclideanL2_differenceQuotient_test (P u) ψ v e (t j)).symm
    obtain ⟨φ, hφ, hSub⟩ := hCluster.tendsto_subseq
    exact (hL w).symm.trans (tendsto_nhds_unique hSub (hLim.comp hφ.tendsto_atTop))
  refine ⟨w, ?_, ?_⟩
  · intro ψ
    let P : EuclideanSobolev n →L[ℝ] EuclideanL2 n ℝ :=
      (WithLp.fstL 2 ℝ _ _).comp (euclideanSobolevSubmodule n).subtypeL
    have h := hPair P (fun _ => rfl) ψ (1 : ℝ)
    change (∫ x, ψ x * inner ℝ (1 : ℝ) ((w : EuclideanL2Pair n).fst x) ∂volume0 n) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v *
        inner ℝ (1 : ℝ) ((u : EuclideanL2Pair n).fst x) ∂volume0 n) at h
    simpa only [Real.inner_apply, one_mul] using h
  · intro ψ e
    let P : EuclideanSobolev n →L[ℝ] EuclideanL2 n (E n) :=
      (WithLp.sndL 2 ℝ _ _).comp (euclideanSobolevSubmodule n).subtypeL
    exact hPair P (fun _ => rfl) ψ e

/-- Every fixed translation direction gives an L² weak derivative of the
gradient of a whole-space solution with Lipschitz coefficients. -/
theorem exists_euclideanGradient_weakDerivative {n : ℕ}
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ (volume0 n)) {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂volume0 n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLip : LipschitzWith K A)
    {g : EuclideanL2 n ℝ} {u : EuclideanSobolev n} (hu : IsEuclideanWeakSolution hA g u)
    (v : E n) :
    ∃ H : EuclideanL2 n (E n), ∀ (ψ : 𝓓((⊤ : Opens (E n)), ℝ)) (e : E n),
      (∫ x, ψ x * inner ℝ e (H x) ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ e ((u : EuclideanL2Pair n).snd x) ∂volume0 n) := by
  obtain ⟨w, _, hw⟩ := exists_euclideanSobolev_weakDerivative hA hl hE hLip hu v
  exact ⟨(w : EuclideanL2Pair n).snd, hw⟩

end KEBall
