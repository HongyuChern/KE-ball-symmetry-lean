import KEBall.DirichletTaylorLine
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! A closed-ball uniform bound obtained by averaging Taylor's formula. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Interval Pointwise Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "σ" => Measure.restrict (volume : Measure ℝ) (Ioc 0 1)

private theorem integrable_dirichlet_of_continuous {n : ℕ} {f : E n → ℝ}
    (hf : Continuous f) : Integrable f ν[n] :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
    ball_subset_closedBall

private theorem chord_mem_unitBall {n : ℕ} {x y : E n} (hx : x ∈ closedUnitBall n)
    (hy : y ∈ unitBall n) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    (1 - t) • y + t • x ∈ unitBall n := by
  have hy' : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  apply mem_ball_zero_iff.mpr
  calc
    _ ≤ (1 - t) * ‖y‖ + t * ‖x‖ := by
      refine (norm_add_le _ _).trans_eq ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht₁.le), abs_of_nonneg ht₀]
    _ < (1 - t) * 1 + t * 1 := add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left hy' (sub_pos.mpr ht₁)) (mul_le_mul_of_nonneg_left hx' ht₀)
    _ = 1 := by ring

private theorem setIntegral_chord_comp {n : ℕ} (G : E n → ℝ) (x : E n)
    {t : ℝ} (ht : t < 1) :
    (∫ y, G ((1 - t) • y + t • x) ∂ν[n]) =
      ((1 - t) ^ (2 * n))⁻¹ * ∫ z in (Homeomorph.addRight (t • x)) '' ((1 - t) • unitBall n),
        G z ∂volume0 n := by
  have hHaar : (volume0 n).IsAddHaarMeasure := by
    unfold volume0
    exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
  let e := Homeomorph.addRight (t • x)
  have he := (measurePreserving_add_right (volume : Measure (E n)) (t • x)).smul_measure
    (ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n))
  change MeasurePreserving e (volume0 n) (volume0 n) at he
  change (∫ y in unitBall n, (G ∘ e) ((1 - t) • y) ∂volume0 n) = _
  rw [Measure.setIntegral_comp_smul_of_pos (volume0 n) (G ∘ e) (unitBall n) (sub_pos.mpr ht),
    smul_eq_mul, finrank_E]
  congr 1
  calc
    _ = ∫ z in e '' ((1 - t) • unitBall n), G z ∂Measure.map e (volume0 n) := by
      have hMap := setIntegral_map_equiv (μ := volume0 n) e.toMeasurableEquiv G
        (e '' ((1 - t) • unitBall n))
      have hSet : e.toMeasurableEquiv ⁻¹' (e '' ((1 - t) • unitBall n)) =
          (1 - t) • unitBall n := e.toEquiv.preimage_image _
      rw [hSet] at hMap
      exact hMap.symm
    _ = _ := by rw [he.map_eq]

/-- The factor in the Taylor remainder cancels the chord Jacobian. -/
private theorem weighted_setIntegral_chord_le {n : ℕ} (hn : 0 < n)
    {G : E n → ℝ} (hG : Continuous G) (hG₀ : ∀ z, 0 ≤ G z) {x : E n}
    (hx : x ∈ closedUnitBall n) {t : ℝ} (ht : t ∈ Ioc 0 1) :
    (∫ y, (1 - t) ^ (2 * n) * G ((1 - t) • y + t • x) ∂ν[n]) ≤ ∫ y, G y ∂ν[n] := by
  rcases ht.2.eq_or_lt with he | ht'
  · subst t
    simpa [zero_pow (by omega : 2 * n ≠ 0)] using (integral_nonneg (μ := ν[n]) hG₀)
  rw [integral_const_mul, setIntegral_chord_comp G x ht', ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (sub_pos.mpr ht').ne'), one_mul]
  have hsub : (Homeomorph.addRight (t • x)) '' ((1 - t) • unitBall n) ⊆ unitBall n := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact chord_mem_unitBall hx hy ht.1.le ht'
  refine setIntegral_mono_set (integrable_dirichlet_of_continuous hG) (Eventually.of_forall hG₀) ?_
  exact Eventually.of_forall hsub

private theorem integral_chord_weighted_le {n : ℕ} (hn : 0 < n)
    {G : E n → ℝ} (hG : Continuous G) (hG₀ : ∀ z, 0 ≤ G z) {x : E n}
    (hx : x ∈ closedUnitBall n) :
    (∫ y, (∫ t in (0 : ℝ)..1, (1 - t) ^ (2 * n) * G (y + t • (x - y))) ∂ν[n]) ≤
      ∫ y, G y ∂ν[n] := by
  have hC : Continuous (fun p : E n × ℝ => (1 - p.2) ^ (2 * n) *
      G (p.1 + p.2 • (x - p.1))) := by fun_prop
  have hProd : Integrable (fun p : E n × ℝ => (1 - p.2) ^ (2 * n) *
      G (p.1 + p.2 • (x - p.1))) (ν[n].prod σ) := by
    rw [Measure.prod_restrict]
    exact (hC.continuousOn.integrableOn_compact ((isCompact_closedBall (0 : E n) 1).prod
      (isCompact_Icc (α := ℝ) (a := 0) (b := 1)))).mono_set
        (prod_mono ball_subset_closedBall Ioc_subset_Icc_self)
  have hChord (y : E n) (t : ℝ) : y + t • (x - y) = (1 - t) • y + t • x := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  have hSwap := integral_integral_swap
    (f := fun y t => (1 - t) ^ (2 * n) * G (y + t • (x - y))) hProd
  simp only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [hSwap]
  refine (integral_mono_ae hProd.integral_prod_right (integrable_const (∫ y, G y ∂ν[n])) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))]
      with t ht
    simp_rw [hChord]
    exact weighted_setIntegral_chord_le hn hG hG₀ hx ht
  · simp

private theorem norm_sub_le_two_of_mem_closedUnitBall {n : ℕ} {x y : E n}
    (hx : x ∈ closedUnitBall n) (hy : y ∈ closedUnitBall n) : ‖x - y‖ ≤ 2 := by
  have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hy' : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
  exact (norm_sub_le _ _).trans (by linarith)

private theorem norm_iteratedFDeriv_apply_sub_le {n : ℕ} (f : E n → ℝ)
    {x y : E n} (hx : x ∈ closedUnitBall n) (hy : y ∈ closedUnitBall n)
    (k : ℕ) (z : E n) :
    ‖iteratedFDeriv ℝ k f z (fun _ => x - y)‖ ≤ (2 : ℝ) ^ k * ‖iteratedFDeriv ℝ k f z‖ := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm ((2 : ℝ) ^ k)] using
    ((iteratedFDeriv ℝ k f z).le_opNorm_mul_prod_of_le
      (fun _ => norm_sub_le_two_of_mem_closedUnitBall hx hy) :
        ‖iteratedFDeriv ℝ k f z (fun _ => x - y)‖ ≤
          ‖iteratedFDeriv ℝ k f z‖ * ∏ _ : Fin k, (2 : ℝ))

private theorem norm_taylor_remainder_le {n : ℕ} {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    {x y : E n} (hx : x ∈ closedUnitBall n) (hy : y ∈ closedUnitBall n) (m : ℕ) :
    ‖∫ t in (0 : ℝ)..1, ((1 - t) ^ m / m.factorial) *
      iteratedFDeriv ℝ (m + 1) f (y + t • (x - y)) (fun _ => x - y)‖ ≤
      ((2 : ℝ) ^ (m + 1) / m.factorial) *
        ∫ t in (0 : ℝ)..1, (1 - t) ^ m * ‖iteratedFDeriv ℝ (m + 1) f (y + t • (x - y))‖ := by
  let H (t : ℝ) := ‖iteratedFDeriv ℝ (m + 1) f (y + t • (x - y))‖
  let R (t : ℝ) := ((1 - t) ^ m / m.factorial) *
    iteratedFDeriv ℝ (m + 1) f (y + t • (x - y)) (fun _ => x - y)
  let c : ℝ := (2 : ℝ) ^ (m + 1) / m.factorial
  have hD : Continuous (iteratedFDeriv ℝ (m + 1) f) :=
    hf.continuous_iteratedFDeriv (show ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hLine : Continuous (fun t : ℝ => y + t • (x - y)) := by fun_prop
  have hH : Continuous H := (hD.comp hLine).norm
  have hR : Continuous R := by
    have hApply := (continuous_eval_const (fun _ : Fin (m + 1) => x - y)).comp (hD.comp hLine)
    exact (((continuous_const.sub continuous_id).pow m).div_const _).mul hApply
  calc
    ‖∫ t in (0 : ℝ)..1, R t‖ ≤ ∫ t in (0 : ℝ)..1, ‖R t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, c * ((1 - t) ^ m * H t) := by
      refine intervalIntegral.integral_mono_on (by norm_num) (hR.norm.intervalIntegrable _ _)
        ((continuous_const.mul (((continuous_const.sub continuous_id).pow m).mul hH)).intervalIntegrable _ _) ?_
      intro t ht
      have ht₁ : t ≤ 1 := ht.2
      have hc : 0 ≤ (1 - t) ^ m / (m.factorial : ℝ) := by positivity
      dsimp only [R]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc]
      apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_apply_sub_le f hx hy (m + 1)
        (y + t • (x - y))) hc).trans_eq
      dsimp only [c, H]
      ring
    _ = _ := intervalIntegral.integral_const_mul c (fun t => (1 - t) ^ m * H t)

/-- Sobolev control on the closed ball by integrals of derivative norms.
The exponent of the Taylor remainder is the real dimension. -/
theorem norm_le_integral_iteratedFDeriv_closedUnitBall {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ContDiff ℝ ∞ f) {x : E n} (hx : x ∈ closedUnitBall n) :
    ‖f x‖ ≤ (∑ k ∈ Finset.range (2 * n + 1),
      ((2 : ℝ) ^ k / k.factorial) * ∫ y, ‖iteratedFDeriv ℝ k f y‖ ∂ν[n]) +
      ((2 : ℝ) ^ (2 * n + 1) / (2 * n).factorial) *
        ∫ y, ‖iteratedFDeriv ℝ (2 * n + 1) f y‖ ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  let m := 2 * n
  let G (k : ℕ) (y : E n) := ‖iteratedFDeriv ℝ k f y‖
  let c (k : ℕ) : ℝ := (2 : ℝ) ^ k / k.factorial
  have hG (k : ℕ) : Continuous (G k) :=
    (hf.continuous_iteratedFDeriv (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).norm
  have hc (k : ℕ) : 0 ≤ c k := by dsimp only [c]; positivity
  let H (y : E n) := ∫ t in (0 : ℝ)..1, (1 - t) ^ m * G (m + 1) (y + t • (x - y))
  have hAt (y : E n) (hy : y ∈ unitBall n) : ‖f x‖ ≤
      (∑ k ∈ Finset.range (m + 1), c k * G k y) +
        ((2 : ℝ) ^ (m + 1) / m.factorial) * H y := by
    have hy' : y ∈ closedUnitBall n := ball_subset_closedBall hy
    rw [segment_taylor_integral hf x y m]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_taylor_remainder_le hf hx hy' m))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)⁻¹)]
    exact (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_apply_sub_le f hx hy' k y)
      (by positivity)).trans_eq (by dsimp only [c, G]; ring)
  have hProd : Integrable (fun p : E n × ℝ => (1 - p.2) ^ m *
      G (m + 1) (p.1 + p.2 • (x - p.1))) (ν[n].prod σ) := by
    rw [Measure.prod_restrict]
    have hC : Continuous (fun p : E n × ℝ => (1 - p.2) ^ m *
        G (m + 1) (p.1 + p.2 • (x - p.1))) := by fun_prop
    exact (hC.continuousOn.integrableOn_compact ((isCompact_closedBall (0 : E n) 1).prod
      (isCompact_Icc (α := ℝ) (a := 0) (b := 1)))).mono_set
        (prod_mono ball_subset_closedBall Ioc_subset_Icc_self)
  have hH : Integrable H ν[n] := by
    simpa only [H, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hProd.integral_prod_left
  have hSum : Integrable (fun y => ∑ k ∈ Finset.range (m + 1), c k * G k y) ν[n] :=
    integrable_finsetSum _ fun k _ => (integrable_dirichlet_of_continuous (hG k)).const_mul _
  have hAvg := integral_mono_ae (integrable_const (μ := ν[n]) ‖f x‖)
    (hSum.add (hH.const_mul ((2 : ℝ) ^ (m + 1) / m.factorial)))
    ((ae_restrict_mem measurableSet_ball).mono hAt)
  change (∫ _ : E n, ‖f x‖ ∂ν[n]) ≤
    ∫ y, (∑ k ∈ Finset.range (m + 1), c k * G k y) +
      ((2 : ℝ) ^ (m + 1) / m.factorial) * H y ∂ν[n] at hAvg
  rw [integral_const, probReal_univ, one_smul,
    integral_add hSum (hH.const_mul ((2 : ℝ) ^ (m + 1) / m.factorial)),
    integral_finsetSum _ (fun k _ => (integrable_dirichlet_of_continuous (hG k)).const_mul _),
    integral_const_mul] at hAvg
  have hCoeff : 0 ≤ (2 : ℝ) ^ (m + 1) / m.factorial := by positivity
  have hRem := mul_le_mul_of_nonneg_left
    (integral_chord_weighted_le hn (hG (m + 1)) (fun _ => norm_nonneg _) hx) hCoeff
  have hMain := hAvg.trans (add_le_add_right hRem
    (∑ k ∈ Finset.range (m + 1), ∫ y, c k * G k y ∂ν[n]))
  simpa only [integral_const_mul, m, c, G] using hMain

end KEBall
