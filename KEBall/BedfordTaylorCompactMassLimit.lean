import KEBall.BedfordTaylorCompactDifference
import KEBall.BedfordTaylorLocallyBoundedMonotone

/-!
# Compact mass bounds under decreasing Bedford–Taylor convergence
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

/-- An eventual mass bound on a common open neighborhood bounds the
limiting mass of every compact subset of that neighborhood. -/
theorem topMeasure_apply_compact_le_of_decreasing {n : ℕ}
    {Ω V : Opens (ComplexModel n)} {u : ComplexModel n → ℝ} {q : ℕ → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    (hV : V ≤ Ω) {K : Set (ComplexModel n)} (hK : IsCompact K) (hKV : K ⊆ V) {M : ℝ≥0∞}
    (hm : ∀ᶠ j in atTop, topMeasure (hq j) (V : Set (ComplexModel n)) ≤ M) :
    topMeasure hu K ≤ M := by
  obtain ⟨χ, hχ, hχK⟩ := exists_testFunction_one_on hK hKV
  let φ : 𝓓(Ω, ℝ) := ⟨χ, χ.contDiff, χ.hasCompactSupport, χ.tsupport_subset.trans hV⟩
  have hEq {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v) :
      ENNReal.ofReal (∫ x, χ x ∂topMeasure hv) =
        ∫⁻ x, ENNReal.ofReal (χ x) ∂topMeasure hv :=
    ofReal_integral_eq_lintegral_ofReal (integrable_test_topMeasure hv φ)
      (Eventually.of_forall fun x => (hχ x).1)
  have hUpper {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v) :
      ENNReal.ofReal (∫ x, χ x ∂topMeasure hv) ≤ topMeasure hv (V : Set (ComplexModel n)) := by
    rw [hEq hv]
    calc
      _ ≤ ∫⁻ x, (V : Set (ComplexModel n)).indicator 1 x ∂topMeasure hv := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ V
        · rw [indicator_of_mem hx, Pi.one_apply, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hχ x).2
        · have hs : x ∉ tsupport χ := fun h => hx (χ.tsupport_subset h)
          simp only [indicator_of_notMem (show x ∉ (V : Set (ComplexModel n)) from hx),
            image_eq_zero_of_notMem_tsupport hs, ENNReal.ofReal_zero, le_refl]
      _ = _ := by
        rw [lintegral_indicator V.isOpen.measurableSet]
        simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply_univ]
  have hWeak := ENNReal.tendsto_ofReal (tendsto_topMeasure_of_decreasing hu hq hanti hlim
    χ χ.continuous χ.hasCompactSupport (χ.tsupport_subset.trans hV))
  have hbound := le_of_tendsto hWeak (hm.mono fun j hj => (hUpper (hq j)).trans hj)
  have hKmass : topMeasure hu K = ∫⁻ x in K, ENNReal.ofReal (χ x) ∂topMeasure hu := by
    rw [← Measure.restrict_apply_univ K]
    rw [← lintegral_one]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [hχK hx, Pi.one_apply, ENNReal.ofReal_one]
  calc
    _ = ∫⁻ x in K, ENNReal.ofReal (χ x) ∂topMeasure hu := hKmass
    _ ≤ ∫⁻ x, ENNReal.ofReal (χ x) ∂topMeasure hu := lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ M := (hEq hu) ▸ hbound

end KEBall.BedfordTaylor
