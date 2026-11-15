import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Increasing sequences of measures
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace KEBall.Cegrell

variable {X : Type*} [MeasurableSpace X]

private theorem iSup_measure_iUnion (μ : ℕ → Measure X) (hμ : Monotone μ)
    {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A)) :
    (⨆ j, μ j (⋃ i, A i)) = ∑' i, ⨆ j, μ j (A i) := by
  simp_rw [measure_iUnion hd hA, ENNReal.tsum_eq_iSup_sum]
  conv_rhs =>
    arg 1
    ext s
    rw [ENNReal.finsetSum_iSup_of_monotone (fun i a b hab => hμ hab (A i))]
  exact iSup_comm

/-- The measure given on measurable sets by the pointwise supremum
of an increasing sequence of measures. -/
noncomputable def increasingMeasureLimit (μ : ℕ → Measure X) (hμ : Monotone μ) : Measure X :=
  Measure.ofMeasurable (fun A _ => ⨆ j, μ j A) (by simp) (fun {A} hA hd => iSup_measure_iUnion μ hμ (A := A) hA hd)

theorem increasingMeasureLimit_apply (μ : ℕ → Measure X) (hμ : Monotone μ)
    {A : Set X} (hA : MeasurableSet A) :
    increasingMeasureLimit μ hμ A = ⨆ j, μ j A :=
  Measure.ofMeasurable_apply _ hA

theorem le_increasingMeasureLimit (μ : ℕ → Measure X) (hμ : Monotone μ) (j : ℕ) :
    μ j ≤ increasingMeasureLimit μ hμ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [increasingMeasureLimit_apply μ hμ hA]
  exact le_iSup (fun i => μ i A) j

private theorem simpleFunc_lintegral_increasingMeasureLimit (μ : ℕ → Measure X) (hμ : Monotone μ)
    (f : SimpleFunc X ℝ≥0∞) :
    f.lintegral (increasingMeasureLimit μ hμ) = ⨆ j, f.lintegral (μ j) := by
  simp only [SimpleFunc.lintegral]
  have h (t : ℝ≥0∞) := increasingMeasureLimit_apply μ hμ (f.measurableSet_fiber t)
  simp_rw [h, ENNReal.mul_iSup]
  apply ENNReal.finsetSum_iSup_of_monotone
  intro t a b hab
  exact mul_le_mul_right (hμ hab (f ⁻¹' {t})) t

theorem lintegral_increasingMeasureLimit (μ : ℕ → Measure X) (hμ : Monotone μ) (f : X → ℝ≥0∞) :
    (∫⁻ x, f x ∂increasingMeasureLimit μ hμ) = ⨆ j, ∫⁻ x, f x ∂μ j := by
  apply le_antisymm
  · rw [lintegral]
    apply iSup₂_le
    intro g hg
    rw [simpleFunc_lintegral_increasingMeasureLimit μ hμ]
    exact iSup_le fun j => (SimpleFunc.lintegral_eq_lintegral g (μ j)).symm.le.trans
      ((lintegral_mono hg).trans (le_iSup (fun i => ∫⁻ x, f x ∂μ i) j))
  · exact iSup_le fun j => lintegral_mono' (le_increasingMeasureLimit μ hμ j) le_rfl

end KEBall.Cegrell
