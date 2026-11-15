import KEBall.BedfordTaylorCoordinates
import Drafts.KEBall.ExteriorMeasure
import PshLines.FirstPass.MongeAmpere
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The smooth top measure in the two coordinate models
-/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)

private theorem realHessian_comp_coordinates {n : ℕ} (u : E n → ℝ)
    (z a b : ComplexModel n) :
    PshLines.realHessian (u ∘ (complexCoordinates n).symm) z a b =
      KEBall.realHessian u ((complexCoordinates n).symm z)
        ((complexCoordinates n).symm a) ((complexCoordinates n).symm b) := by
  let e := (complexCoordinates n).symm.toContinuousLinearEquiv
  have h := e.iteratedFDerivWithin_comp_right u
    (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set (E n))) (mem_univ (e z)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have hvec : (fun i => e (![a, b] i)) = ![e a, e b] := by
    ext i
    fin_cases i <;> rfl
  change PshLines.realHessian (u ∘ e) z a b = KEBall.realHessian u (e z) (e a) (e b)
  simp only [PshLines.realHessian, h, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, hvec, iteratedFDeriv_two_apply, KEBall.realHessian]
  rfl

theorem complexHessian_coordinates {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) :
    PshLines.FirstPass.MongeAmpere.complexHessian (u ∘ (complexCoordinates n).symm)
      (complexCoordinates n x) = KEBall.complexHessian u x := by
  have hre (j : Fin n) :
      (complexCoordinates n).symm (EuclideanSpace.single j (1 : ℂ)) = realDirection j := by
    rw [← complexCoordinates_realDirection, LinearIsometryEquiv.symm_apply_apply]
  have him (j : Fin n) :
      (complexCoordinates n).symm (Complex.I • EuclideanSpace.single j (1 : ℂ)) = imagDirection j := by
    rw [← complexCoordinates_imagDirection, LinearIsometryEquiv.symm_apply_apply]
  ext i j : 1
  rw [PshLines.FirstPass.MongeAmpere.complexHessian, KEBall.complexHessian_real_entry hu]
  simp only [realHessian_comp_coordinates, LinearIsometryEquiv.symm_apply_apply,
    PshLines.FirstPass.MongeAmpere.coordinateVector, hre, him]
  push_cast
  ring

/-- The smooth measure used in Bedford–Taylor approximation is exactly
the pushforward of the existing oriented top-form measure on the domain. -/
theorem map_d0TopMeasure_restrict_eq_smoothMeasure {n : ℕ} {u : E n → ℝ}
    (U : Opens (ComplexModel n))
    (hs : PshLines.FirstPass.MongeAmpere.IsSmoothPshOn U (u ∘ (complexCoordinates n).symm)) :
    Measure.map (complexCoordinates n)
      ((d0TopMeasure u).restrict ((complexCoordinates n) ⁻¹' (U : Set (ComplexModel n)))) =
    PshLines.FirstPass.MongeAmpere.smoothMeasure U (u ∘ (complexCoordinates n).symm) hs := by
  let e := (complexCoordinates n).toHomeomorph.toMeasurableEquiv
  let V := e ⁻¹' (U : Set (ComplexModel n))
  let c : ℝ := (n.factorial : ℝ) / Real.pi ^ n
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hV : IsOpen V := U.isOpen.preimage (complexCoordinates n).continuous
  have hm : MeasurePreserving e (volume.restrict V) (volume.restrict (U : Set (ComplexModel n))) := by
    refine ⟨e.measurable, ?_⟩
    have he : Measure.map e (volume : Measure (E n)) = volume :=
      (complexCoordinates_measurePreserving n).map_eq
    rw [← e.restrict_map, he]
  change Measure.map e ((d0TopMeasure u).restrict V) = _
  rw [d0TopMeasure_eq_density, restrict_withDensity hV.measurableSet, volume0,
    Measure.restrict_smul, withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  unfold PshLines.FirstPass.MongeAmpere.smoothMeasure
  ext s hsm
  rw [Measure.map_apply e.measurable hsm, withDensity_apply _ (e.measurable hsm),
    withDensity_apply _ hsm, ← hm.setLIntegral_comp_preimage_emb e.measurableEmbedding]
  apply lintegral_congr_ae
  filter_upwards [ae_mono Measure.restrict_le_self (ae_restrict_mem hV.measurableSet)] with x hx
  have hxU : e x ∈ U := hx
  have hcont : ContDiffAt ℝ ∞ (u ∘ (complexCoordinates n).symm) (e x) :=
    hs.1.contDiffAt (U.isOpen.mem_nhds hxU)
  have hu : ContDiffAt ℝ ∞ u x := by
    change ContDiffAt ℝ ∞ (u ∘ (complexCoordinates n).symm) (complexCoordinates n x) at hcont
    simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using
      hcont.comp x (complexCoordinates n).toContinuousLinearEquiv.contDiff.contDiffAt
  change ENNReal.ofReal c * ENNReal.ofReal (KEBall.complexHessian u x).det.re =
    ENNReal.ofReal (PshLines.FirstPass.MongeAmpere.smoothDensity
      (u ∘ (complexCoordinates n).symm) (complexCoordinates n x))
  rw [← ENNReal.ofReal_mul hc, PshLines.FirstPass.MongeAmpere.smoothDensity,
    complexHessian_coordinates hu]

#print axioms complexHessian_coordinates
#print axioms map_d0TopMeasure_restrict_eq_smoothMeasure

end KEBall.BedfordTaylor
