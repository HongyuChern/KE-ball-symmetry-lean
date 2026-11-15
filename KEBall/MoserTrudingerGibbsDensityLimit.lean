import KEBall.MoserTrudingerSmoothGibbs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Convergence of Gibbs densities on bounded sets of potentials
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped Topology

namespace KEBall.MoserTrudinger

variable {n : ℕ}

local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)

private theorem weight_bounds {γ B a : ℝ} (hγ : 0 ≤ γ) (ha : a ∈ Icc (-B) 0) :
    1 ≤ Real.exp (-γ * a) ∧ Real.exp (-γ * a) ≤ Real.exp (γ * B) := by
  constructor
  · rw [← Real.exp_zero, Real.exp_le_exp]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) ha.2
  · apply Real.exp_le_exp.mpr
    simpa only [neg_mul_neg] using mul_le_mul_of_nonpos_left ha.1 (neg_nonpos.mpr hγ)

private theorem normalizer_ge_one (hn : 0 < n) {γ B : ℝ} (hγ : 0 ≤ γ)
    {u : E n → ℝ} (hu : AEMeasurable u ν[n]) (hB : ∀ᵐ x ∂ν[n], u x ∈ Icc (-B) 0) :
    1 ≤ normalizingIntegral γ u := by
  let : NeZero n := ⟨hn.ne'⟩
  have hMeas : AEMeasurable (fun x => Real.exp (-γ * u x)) ν[n] :=
    Real.continuous_exp.measurable.comp_aemeasurable (aemeasurable_const.mul hu)
  have hInt : Integrable (fun x => Real.exp (-γ * u x)) ν[n] := by
    apply (integrable_const (Real.exp (γ * B))).mono' hMeas.aestronglyMeasurable
    filter_upwards [hB] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact (weight_bounds hγ hx).2
  have h := integral_mono_ae (integrable_const (1 : ℝ)) hInt (hB.mono fun _ hx => (weight_bounds hγ hx).1)
  simpa only [integral_const, probReal_univ, one_smul, normalizingIntegral] using h

/-- The normalizer and density converge for an almost-everywhere convergent
sequence in a fixed bounded interval of nonpositive potentials. -/
theorem gibbsDensity_tendsto_of_ae_of_bounded (hn : 0 < n) {γ B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} {w : E n → ℝ}
    (hu : ∀ j, AEMeasurable (u j) ν[n]) (hw : AEMeasurable w ν[n])
    (hB : ∀ j, ∀ᵐ x ∂ν[n], u j x ∈ Icc (-B) 0)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun j => u j x) atTop (𝓝 (w x))) :
    1 ≤ normalizingIntegral γ w ∧
      Tendsto (fun j => normalizingIntegral γ (u j)) atTop (𝓝 (normalizingIntegral γ w)) ∧
      (∀ j, ∀ᵐ x ∂ν[n], 0 ≤ gibbsDensity γ (u j) x ∧ gibbsDensity γ (u j) x ≤ Real.exp (γ * B)) ∧
      ∀ᵐ x ∂ν[n], Tendsto (fun j => gibbsDensity γ (u j) x) atTop (𝓝 (gibbsDensity γ w x)) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hWB : ∀ᵐ x ∂ν[n], w x ∈ Icc (-B) 0 := by
    filter_upwards [hLim, ae_all_iff.mpr hB] with x hx hI
    exact isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall hI)
  have hZ := normalizer_ge_one hn hγ hw hWB
  have hZ' (j : ℕ) := normalizer_ge_one hn hγ (hu j) (hB j)
  have hW : ∀ᵐ x ∂ν[n], Tendsto (fun j => Real.exp (-γ * u j x)) atTop (𝓝 (Real.exp (-γ * w x))) := by
    filter_upwards [hLim] with x hx
    exact Real.continuous_exp.continuousAt.tendsto.comp (hx.const_mul (-γ))
  have hIntegral : Tendsto (fun j => normalizingIntegral γ (u j)) atTop (𝓝 (normalizingIntegral γ w)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp (γ * B))
    · intro j
      exact (Real.continuous_exp.measurable.comp_aemeasurable (aemeasurable_const.mul (hu j))).aestronglyMeasurable
    · exact integrable_const _
    · intro j
      filter_upwards [hB j] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact (weight_bounds hγ hx).2
    · exact hW
  refine ⟨hZ, hIntegral, ?_, ?_⟩
  · intro j
    filter_upwards [hB j] with x hx
    unfold gibbsDensity
    exact ⟨div_nonneg (Real.exp_pos _).le (zero_le_one.trans (hZ' j)),
      (div_le_self (Real.exp_pos _).le (hZ' j)).trans (weight_bounds hγ hx).2⟩
  · filter_upwards [hW] with x hx
    exact hx.div hIntegral (zero_lt_one.trans_le hZ).ne'

theorem gibbsDensity_aemeasurable {γ : ℝ} {u : E n → ℝ} (hu : AEMeasurable u ν[n]) :
    AEMeasurable (gibbsDensity γ u) ν[n] :=
  (Real.continuous_exp.measurable.comp_aemeasurable (aemeasurable_const.mul hu)).div_const _

end KEBall.MoserTrudinger
