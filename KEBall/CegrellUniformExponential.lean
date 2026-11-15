import KEBall.CegrellExponentialConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Continuity of the exponential term under a higher moment bound
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

private theorem lintegral_tendsto_of_uniform_rpow_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : ℕ → X → ℝ≥0∞} {g : X → ℝ≥0∞}
    (hf : ∀ k, Measurable (f k))
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x)))
    {r : ℝ} (hr : 1 < r) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ k, (∫⁻ x, f k x ^ r ∂μ) ≤ C) :
    Tendsto (fun k => ∫⁻ x, f k x ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)) := by
  have hlower : (∫⁻ x, g x ∂μ) ≤ liminf (fun k => ∫⁻ x, f k x ∂μ) atTop := by
    rw [lintegral_congr_ae (hconv.mono fun _ h => h.liminf_eq.symm)]
    exact lintegral_liminf_le hf
  have hUpper (R : ℝ≥0∞) (hR₀ : 0 < R) (hR₁ : R ≠ ⊤) :
      limsup (fun k => ∫⁻ x, f k x ∂μ) atTop ≤ (∫⁻ x, g x ∂μ) + C * R ^ (1 - r) := by
    have htr : Tendsto (fun k => ∫⁻ x, min (f k x) R ∂μ) atTop
        (𝓝 (∫⁻ x, min (g x) R ∂μ)) := by
      apply tendsto_lintegral_of_dominated_convergence (fun _ => R)
        (fun k => (hf k).min measurable_const)
        (fun _ => Eventually.of_forall fun _ => min_le_right _ _)
      · rw [lintegral_const]
        exact ENNReal.mul_ne_top hR₁ (measure_ne_top _ _)
      · exact hconv.mono fun x hx => hx.min tendsto_const_nhds
    have htail (y : ℝ≥0∞) : y ≤ min y R + y ^ r * R ^ (1 - r) := by
      by_cases hy : y ≤ R
      · rw [min_eq_left hy]
        exact le_self_add
      · have hR : R < y := lt_of_not_ge hy
        have hRP : 0 < R ^ (r - 1) := ENNReal.rpow_pos hR₀ hR₁
        have hRF : R ^ (r - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hR₁
        refine (show y ≤ y ^ r * R ^ (1 - r) from ?_).trans le_add_self
        rw [show 1 - r = -(r - 1) by ring, ENNReal.rpow_neg, ← div_eq_mul_inv]
        apply (ENNReal.le_div_iff_mul_le (Or.inl hRP.ne') (Or.inl hRF)).mpr
        calc
          _ ≤ y * y ^ (r - 1) := mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hR.le (by linarith))
          _ = y ^ (1 : ℝ) * y ^ (r - 1) := by rw [ENNReal.rpow_one]
          _ = _ := by
            rw [← ENNReal.rpow_add_of_nonneg 1 (r - 1)
              (by norm_num) (by linarith), show 1 + (r - 1) = r by ring]
    have hI (k : ℕ) : (∫⁻ x, f k x ∂μ) ≤ (∫⁻ x, min (f k x) R ∂μ) + C * R ^ (1 - r) := by
      refine (lintegral_mono fun x => htail (f k x)).trans ?_
      have hp : Measurable (fun x => f k x ^ r) := ENNReal.continuous_rpow_const.measurable.comp (hf k)
      rw [lintegral_add_left ((hf k).min measurable_const), lintegral_mul_const _ hp]
      exact add_le_add le_rfl (mul_le_mul' (hbound k) le_rfl)
    calc
      _ ≤ limsup (fun k => (∫⁻ x, min (f k x) R ∂μ) + C * R ^ (1 - r)) atTop :=
        limsup_le_limsup (Eventually.of_forall hI)
      _ = (∫⁻ x, min (g x) R ∂μ) + C * R ^ (1 - r) :=
        (htr.add tendsto_const_nhds).limsup_eq
      _ ≤ _ := add_le_add (lintegral_mono fun _ => min_le_left _ _) le_rfl
  apply tendsto_of_le_liminf_of_limsup_le hlower
  have hpow : Tendsto (fun k : ℕ => ((2 : ℝ≥0∞) ^ k) ^ (1 - r)) atTop (𝓝 0) := by
    have hh : (2 : ℝ≥0∞) ^ (1 - r) < 1 :=
      ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have he (k : ℕ) : ((2 : ℝ≥0∞) ^ k) ^ (1 - r) = ((2 : ℝ≥0∞) ^ (1 - r)) ^ k := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        mul_comm (k : ℝ)]
    simp_rw [he]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hh
  have hlim : Tendsto (fun k : ℕ => (∫⁻ x, g x ∂μ) + C * (((2 : ℝ≥0∞) ^ k) ^ (1 - r)))
      atTop (𝓝 (∫⁻ x, g x ∂μ)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hpow (Or.inr hC))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun k =>
    hUpper ((2 : ℝ≥0∞) ^ k) (pos_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))) (ENNReal.pow_ne_top (by norm_num))

/-- Almost-everywhere convergence of finite-energy potentials and a uniform
exponential moment at a larger coupling give continuity of the integral
at the smaller coupling. -/
theorem exponentialIntegral_tendsto_of_uniform_higher {n : ℕ} (hn : 0 < n)
    {u : ℕ → ComplexModel n → EReal} {v : ComplexModel n → EReal}
    (hu : ∀ k, IsE1 (complexUnitBall n) (u k))
    (hconv : ∀ᵐ x ∂(volume0 n).restrict (unitBall n),
      Tendsto (fun k => u k (complexCoordinates n x)) atTop (𝓝 (v (complexCoordinates n x))))
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ k, exponentialIntegral β (u k) ≤ C) :
    Tendsto (fun k => exponentialIntegral α (u k)) atTop (𝓝 (exponentialIntegral α v)) := by
  let μ := (volume0 n).restrict (unitBall n)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, volume0_unitBall n hn]
    exact ENNReal.one_lt_top⟩
  let f (k : ℕ) (x : E n) := finiteEnergyWeight (u k) x ^ α
  let g (x : E n) := finiteEnergyWeight v x ^ α
  have hf (k : ℕ) : Measurable (f k) :=
    ENNReal.continuous_rpow_const.measurable.comp (finiteEnergyWeight_measurable (hu k))
  have hAE : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x)) := by
    filter_upwards [hconv, ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hxB
    simpa only [f, g, finiteEnergyWeight, if_pos hxB, Function.comp_def] using
      (ENNReal.continuous_rpow_const.tendsto _).comp ((continuous_expNeg.tendsto _).comp hx)
  have hB (k : ℕ) : (∫⁻ x, f k x ^ (β / α) ∂μ) ≤ C := by
    simp only [f, ← ENNReal.rpow_mul, mul_div_cancel₀ _ hα.ne']
    exact hbound k
  exact lintegral_tendsto_of_uniform_rpow_bound hf hAE ((one_lt_div hα).mpr hαβ) hC hB

end KEBall.MoserTrudinger
