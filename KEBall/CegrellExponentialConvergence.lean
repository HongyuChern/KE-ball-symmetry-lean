import KEBall.CegrellExponential

/-!
# Exponential integrals under Cegrell approximation
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ} {u : ComplexModel n → EReal}

/-- The exponential integral increases to the actual finite-energy integral
along every defining Cegrell sequence. The conclusion includes infinite values. -/
theorem exponentialIntegral_eq_iSup (p : E1Approximation (complexUnitBall n) u)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    exponentialIntegral γ u =
      ⨆ j, exponentialIntegral γ (fun x => (p.term j x : EReal)) := by
  let f (j : ℕ) (x : E n) : ℝ≥0∞ :=
    finiteEnergyWeight (fun z => (p.term j z : EReal)) x ^ γ
  have hMaps (x : E n) (hx : x ∈ unitBall n) : complexCoordinates n x ∈ complexUnitBall n := by
    change x ∈ (complexCoordinates n) ⁻¹' (complexUnitBall n : Set (ComplexModel n))
    rwa [preimage_complexUnitBall]
  have hMono (x : E n) : Monotone (fun j => f j x) := by
    intro j k hjk
    dsimp only [f]
    apply ENNReal.rpow_le_rpow _ hγ
    by_cases hx : x ∈ unitBall n
    · rw [finiteEnergyWeight, if_pos hx, finiteEnergyWeight, if_pos hx]
      exact expNeg_antitone (EReal.coe_le_coe_iff.mpr (p.antitone _ (hMaps x hx) hjk))
    · simp [finiteEnergyWeight, hx]
  have hEq (x : E n) (hx : x ∈ unitBall n) :
      finiteEnergyWeight u x ^ γ = ⨆ j, f j x := by
    have hlim : Tendsto (fun j => f j x) atTop (𝓝 (finiteEnergyWeight u x ^ γ)) := by
      simpa only [f, finiteEnergyWeight, if_pos hx, Function.comp_def] using
        (ENNReal.continuous_rpow_const.tendsto _).comp
          ((continuous_expNeg.tendsto _).comp (p.pointwise _ (hMaps x hx)))
    exact tendsto_nhds_unique hlim (tendsto_atTop_iSup (hMono x))
  have hf (j : ℕ) : Measurable (f j) :=
    (ENNReal.continuous_rpow_const (y := γ)).measurable.comp
      (finiteEnergyWeight_measurable (p.term_mem j).isE1)
  unfold exponentialIntegral
  calc
    _ = ∫⁻ x in unitBall n, ⨆ j, f j x ∂volume0 n := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      exact hEq x hx
    _ = _ := lintegral_iSup hf (fun j k hjk x => hMono x hjk)

theorem exponentialIntegral_tendsto_of_approximation (p : E1Approximation (complexUnitBall n) u)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    Tendsto (fun j => exponentialIntegral γ (fun x => (p.term j x : EReal)))
      atTop (𝓝 (exponentialIntegral γ u)) := by
  rw [exponentialIntegral_eq_iSup p hγ]
  apply tendsto_atTop_iSup
  intro j k hjk
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  have hx' : complexCoordinates n x ∈ complexUnitBall n := by
    change x ∈ (complexCoordinates n) ⁻¹' (complexUnitBall n : Set (ComplexModel n))
    rwa [preimage_complexUnitBall]
  simp only [finiteEnergyWeight, if_pos hx]
  exact ENNReal.rpow_le_rpow
    (expNeg_antitone (EReal.coe_le_coe_iff.mpr (p.antitone _ hx' hjk))) hγ

end KEBall.MoserTrudinger
