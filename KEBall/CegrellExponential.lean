import KEBall.CegrellScaling
import KEBall.MoserTrudingerCriticalLimit
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Exponential integrals of finite-energy potentials
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Classical ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

/-- The extended exponential weight `exp (-a)`. -/
noncomputable def expNeg (a : EReal) : ℝ≥0∞ := EReal.exp (-a)

@[simp]
theorem expNeg_coe (a : ℝ) : expNeg (a : EReal) = ENNReal.ofReal (Real.exp (-a)) := by
  rw [expNeg, ← EReal.coe_neg, EReal.exp_coe]

theorem continuous_expNeg : Continuous expNeg := ENNReal.continuous_exp.comp continuous_neg

theorem measurable_expNeg : Measurable expNeg := continuous_expNeg.measurable

theorem expNeg_antitone : Antitone expNeg :=
  fun _ _ hab => EReal.exp_monotone (EReal.neg_le_neg_iff.mpr hab)

theorem expNeg_ge_one {a : EReal} (ha : a ≤ 0) : 1 ≤ expNeg a :=
  EReal.one_le_exp_iff.mpr (EReal.neg_nonneg.mpr ha)

theorem expNeg_const_mul (a : EReal) (c : ℝ) :
    expNeg ((c : EReal) * a) = expNeg a ^ c := by
  rw [expNeg, EReal.mul_comm (c : EReal) a, ← EReal.neg_mul, EReal.exp_mul]
  rfl

/-- Extend the exponential weight by one outside the unit ball in the
real coordinate model, so it can be used with the existing volume. -/
noncomputable def finiteEnergyWeight (u : ComplexModel n → EReal) (x : E n) : ℝ≥0∞ :=
  if x ∈ unitBall n then expNeg (u (complexCoordinates n x)) else 1

theorem finiteEnergyWeight_measurable {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) : Measurable (finiteEnergyWeight u) := by
  apply measurable_of_restrict_of_restrict_compl (s := unitBall n) Metric.isOpen_ball.measurableSet
  · have hMaps : MapsTo (complexCoordinates n) (unitBall n) (complexUnitBall n : Set (ComplexModel n)) :=
      fun x hx => by simpa only [← mem_preimage, preimage_complexUnitBall] using hx
    have hUpper : UpperSemicontinuousOn (u ∘ complexCoordinates n) (unitBall n) :=
      hu.1.upperSemicontinuousOn.comp (complexCoordinates n).continuous.continuousOn hMaps
    have hMeas : Measurable (fun x : ↥(unitBall n) => u (complexCoordinates n x)) :=
      (upperSemicontinuousOn_iff_restrict.mpr hUpper).measurable
    change Measurable (fun x : ↥(unitBall n) => finiteEnergyWeight u x)
    have hEq : (fun x : ↥(unitBall n) => finiteEnergyWeight u x) =
        fun x : ↥(unitBall n) => expNeg (u (complexCoordinates n x)) := by
      funext x
      exact if_pos x.property
    rw [hEq]
    exact measurable_expNeg.comp hMeas
  · change Measurable (fun x : ↥((unitBall n)ᶜ) => finiteEnergyWeight u x)
    have hEq : (fun x : ↥((unitBall n)ᶜ) => finiteEnergyWeight u x) =
        fun _ : ↥((unitBall n)ᶜ) => 1 := by
      funext x
      exact if_neg x.property
    rw [hEq]
    exact measurable_const

theorem finiteEnergyWeight_ge_one (hn : 0 < n) {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) (x : E n) : 1 ≤ finiteEnergyWeight u x := by
  by_cases hx : x ∈ unitBall n
  · rw [finiteEnergyWeight, if_pos hx]
    exact expNeg_ge_one (hu.nonpositive_unitBall hn (complexCoordinates n x)
      (by
        change x ∈ (complexCoordinates n) ⁻¹' (complexUnitBall n : Set (ComplexModel n))
        rwa [preimage_complexUnitBall]))
  · simp only [finiteEnergyWeight, if_neg hx, le_refl]

/-- The normalized exponential integral in the variational functional. -/
noncomputable def exponentialIntegral (γ : ℝ) (u : ComplexModel n → EReal) : ℝ≥0∞ :=
  ∫⁻ x in unitBall n, finiteEnergyWeight u x ^ γ ∂volume0 n

theorem exponentialIntegral_ge_one (hn : 0 < n) {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) {γ : ℝ} (hγ : 0 ≤ γ) :
    1 ≤ exponentialIntegral γ u := by
  unfold exponentialIntegral
  calc
    1 = ∫⁻ _ in unitBall n, (1 : ℝ≥0∞) ∂volume0 n := by simp [lintegral_const, volume0_unitBall n hn]
    _ ≤ _ := lintegral_mono fun x => by
      simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow (finiteEnergyWeight_ge_one hn hu x) hγ

theorem exponentialIntegral_const_mul (u : ComplexModel n → EReal) (c γ : ℝ) :
    exponentialIntegral γ (fun x => (c : EReal) * u x) = exponentialIntegral (c * γ) u := by
  unfold exponentialIntegral
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet : MeasurableSet (unitBall n))] with x hx
  rw [finiteEnergyWeight, finiteEnergyWeight, if_pos hx, if_pos hx, expNeg_const_mul _ c,
    ← ENNReal.rpow_mul]

/-- The actual variational functional, valued in the extended reals so
that an infinite exponential integral is represented by `⊤`. -/
noncomputable def finiteEnergyFunctional (γ : ℝ) {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) : EReal :=
  if exponentialIntegral γ u = ⊤ then ⊤ else
    ((Real.log (exponentialIntegral γ u).toReal / γ -
      (energy hu).toReal / (n + 1 : ℝ) : ℝ) : EReal)

end KEBall.MoserTrudinger
