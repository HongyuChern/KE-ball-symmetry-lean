import KEBall.MoserTrudingerSmooth
import KEBall.PaperBridges20261016
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The critical limit from subcritical variational bounds

The hypothesis is the subcritical variational estimate with the radial value.
The conclusion bounds the extended integral before taking its logarithm.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace KEBall.MoserTrudinger

private theorem iSup_rpow_of_tendsto_one {t : ℕ → ℝ}
    (ht : ∀ k, t k ∈ Ioo (0 : ℝ) 1) (hlim : Tendsto t atTop (𝓝 1))
    {w : ℝ≥0∞} (hw : 1 ≤ w) :
    (⨆ k, w ^ t k) = w := by
  by_cases htop : w = ∞
  · subst w
    simp [ENNReal.top_rpow_of_pos (ht _).1]
  · have hle (k : ℕ) : w ^ t k ≤ w := by
      simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le hw (ht k).2.le
    have hwreal : 1 ≤ w.toReal := by
      simpa using ENNReal.toReal_mono htop hw
    have hpow (k : ℕ) : ENNReal.ofReal (w.toReal ^ t k) = w ^ t k := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (ht k).1.le,
        ENNReal.ofReal_toReal htop]
    have hpowlim : Tendsto (fun k => w ^ t k) atTop (𝓝 w) := by
      have hc : ContinuousAt (fun r : ℝ => w.toReal ^ r) 1 :=
        Real.continuousAt_const_rpow (ne_of_gt (zero_lt_one.trans_le hwreal))
      have h := (ENNReal.continuous_ofReal.tendsto (w.toReal ^ (1 : ℝ))).comp
        (hc.tendsto.comp hlim)
      simpa only [Function.comp_def, Real.rpow_one, ENNReal.ofReal_toReal htop, hpow] using h
    exact le_antisymm (iSup_le hle) (le_of_tendsto hpowlim
      (Eventually.of_forall fun k => le_iSup (fun k => w ^ t k) k))

/-- The final analytic passage applies even when the weight has infinite
values. The subcritical variational bound is an explicit hypothesis. -/
theorem critical_integral_le_of_subcritical {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (n : ℕ) (w : X → ℝ≥0∞) (hw : Measurable w) (hw₁ : ∀ x, 1 ≤ w x)
    {energy : ℝ} (hE : 0 ≤ energy)
    (hsub : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∫⁻ x, w x ^ t ∂μ) ≤ ENNReal.ofReal (Real.exp (t * energy + radialValue n t))) :
    (∫⁻ x, w x ∂μ) ≤ ENNReal.ofReal (Real.exp (energy + harmonicConstant n)) := by
  obtain ⟨t, hmono, ht, hlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
  let f : ℕ → X → ℝ≥0∞ := fun k x => w x ^ t k
  have hf (k : ℕ) : Measurable (f k) :=
    ENNReal.continuous_rpow_const.measurable.comp hw
  have hfmono : Monotone f := by
    intro j k hjk x
    exact ENNReal.rpow_le_rpow_of_exponent_le (hw₁ x) (hmono.monotone hjk)
  have hw' : (fun x => ⨆ k, f k x) = w := by
    funext x
    exact iSup_rpow_of_tendsto_one ht hlim (hw₁ x)
  rw [← hw', lintegral_iSup hf hfmono]
  apply iSup_le
  intro k
  exact (hsub (t k) (ht k)).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (add_le_add (by simpa using mul_le_mul_of_nonneg_right (ht k).2.le hE)
      (radialValue_le_harmonicConstant n (ht k).1.le (ht k).2))))

private theorem smoothEnergy_congr {n : ℕ} {u v : E n → ℝ}
    (heq : EqOn u v (unitBall n)) : smoothEnergy u = smoothEnergy v := by
  have ho : IsOpen (unitBall n) := Metric.isOpen_ball
  have hm : (d0TopMeasure u).restrict (unitBall n) = (d0TopMeasure v).restrict (unitBall n) := by
    rw [d0TopMeasure_eq_density, d0TopMeasure_eq_density,
      restrict_withDensity ho.measurableSet, restrict_withDensity ho.measurableSet]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    have he : u =ᶠ[𝓝 x] v := by
      filter_upwards [ho.mem_nhds hx] with y hy
      exact heq hy
    rw [complexHessian_congr_of_eventuallyEq he]
  unfold smoothEnergy
  rw [hm]
  apply setIntegral_congr_fun ho.measurableSet
  intro x hx
  simp only [heq hx]

/-- The critical upper bound follows from subcritical maximization.
The variational hypothesis is expressed for one target weight `w = exp(-u)`.
Here `energy` is the energy of `u` multiplied by the stated coefficient.
The smooth maximizer has the coupling `(n+1)t` and is identified using the
existing mean-field classification. -/
theorem critical_log_bound_of_meanField_maximizers {n : ℕ} (hn : 2 ≤ n)
    (w : E n → ℝ≥0∞) (hw : Measurable w) (hw₁ : ∀ x, 1 ≤ w x)
    {energy : ℝ} (hE : 0 ≤ energy)
    (hmax : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ φ : E n → ℝ,
      Paper20261016.IsMeanFieldSolution n ((n + 1 : ℝ) * t) φ ∧
        (∫⁻ x in unitBall n, w x ^ t ∂volume0 n) ≤ ENNReal.ofReal
          (Real.exp (t * energy +
            (Real.log (normalizingIntegral ((n + 1 : ℝ) * t) φ) - t * smoothEnergy φ)))) :
    (∫⁻ x in unitBall n, w x ∂volume0 n) < ∞ ∧
      Real.log (∫⁻ x in unitBall n, w x ∂volume0 n).toReal ≤ energy + harmonicConstant n := by
  let μ := (volume0 n).restrict (unitBall n)
  have hupper := critical_integral_le_of_subcritical μ n w hw hw₁ hE ?_
  · have hpos : 1 ≤ ∫⁻ x, w x ∂μ := by
      calc
        1 = ∫⁻ _ : E n, (1 : ℝ≥0∞) ∂μ := by
          simp [μ, volume0_unitBall n (by omega)]
        _ ≤ _ := lintegral_mono hw₁
    have hfinite := hupper.trans_lt ENNReal.ofReal_lt_top
    have hrpos : 0 < (∫⁻ x, w x ∂μ).toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le hpos).ne' hfinite.ne
    have hrle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hrle
    exact ⟨hfinite, (Real.log_le_log hrpos hrle).trans_eq (Real.log_exp _)⟩
  · intro t ht
    obtain ⟨φ, hφ, hbound⟩ := hmax t ht
    let γ : ℝ := (n + 1 : ℝ) * t
    have hφ' := (Paper20261016.meanField_iff_normalized n γ φ).mp hφ
    have hEq : EqOn φ (profile n t) (unitBall n) :=
      (hφ'.eqOn_normalizedPotential hn).2.mono Metric.ball_subset_closedBall
    have hI : normalizingIntegral γ φ = (1 - t)⁻¹ := by
      rw [hφ'.normalizingIntegral_eq hn]
      dsimp [γ]
      rw [mul_div_cancel_left₀ _ (by positivity : (n + 1 : ℝ) ≠ 0)]
    have hvalue :
        Real.log (normalizingIntegral γ φ) - t * smoothEnergy φ = radialValue n t := by
      rw [hI, Real.log_inv, smoothEnergy_congr hEq, energy_profile hn ht.1 ht.2]
      ring
    change (∫⁻ x, w x ^ t ∂μ) ≤ ENNReal.ofReal (Real.exp (t * energy + radialValue n t))
    change Real.log (normalizingIntegral ((n + 1 : ℝ) * t) φ) -
      t * smoothEnergy φ = radialValue n t at hvalue
    rw [hvalue] at hbound
    exact hbound

#print axioms critical_integral_le_of_subcritical
#print axioms critical_log_bound_of_meanField_maximizers

end KEBall.MoserTrudinger
