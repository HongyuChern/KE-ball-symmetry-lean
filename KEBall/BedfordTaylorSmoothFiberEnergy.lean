import KEBall.BedfordTaylorFiberChangeVariables
import KEBall.BedfordTaylorTopMeasure
import KEBall.FiberEnergyDiscDerivative

/-!
# Smooth fiber energy in the Bedford–Taylor normalization
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.BedfordTaylor

open MoserTrudinger
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn smoothDensity smoothMeasure)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

theorem integral_topMeasure_eq_setIntegral_density {n : ℕ} {W : Opens (ComplexModel n)}
    {q : ComplexModel n → ℝ} (hq : IsSmoothPshOn W q) (f : ComplexModel n → ℝ) :
    (∫ x, f x ∂topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hq)) =
      ∫ x in (W : Set (ComplexModel n)), smoothDensity q x * f x := by
  rw [topMeasure_eq_smoothMeasure hq, smoothMeasure]
  let μ := (volume : Measure (ComplexModel n)).restrict W
  have hMeas : AEMeasurable (fun x => ENNReal.ofReal (smoothDensity q x)) μ :=
    ((continuousOn_smoothDensity hq.1).aemeasurable W.isOpen.measurableSet).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hMeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
  rw [PshLines.FirstPass.MongeAmpere.smoothMeasure_weight_toReal W q hq hx, smul_eq_mul]

/-- In the dilated fiber coordinates, the smooth signed energy is the
Bedford–Taylor energy pairing divided by the fiber dimension plus one. -/
theorem fiberEnergy_fiberDilationCoordinates {n : ℕ} {q : ComplexModel (n + 1) → ℝ}
    (hq : ContDiff ℝ ∞ q) {R : ℝ} (hR : 0 < R) (w : E 1)
    (hs : IsSmoothPshOn (⟨ball 0 R, isOpen_ball⟩ : Opens (ComplexModel n))
      (fun y => q ((complexProductCoordinates n 1).symm (y, complexCoordinates 1 w)))) :
    fiberEnergy (q ∘ fiberDilationCoordinates n R) w =
      (∫ y, q ((complexProductCoordinates n 1).symm (y, complexCoordinates 1 w))
        ∂topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hs)) / (n + 1 : ℝ) := by
  let v (y : ComplexModel n) := q ((complexProductCoordinates n 1).symm (y, complexCoordinates 1 w))
  let L := fiberDilationCoordinates n R
  have hDet (z : E n) :
      (KEBall.complexHessian (fun y => q (L (y, w))) z).det.re =
        R ^ (2 * n) * (modelHessian v (R • complexCoordinates n z)).det.re := by
    rw [fiberComplexHessian_fiberDilationCoordinates hq, Matrix.det_smul, Fintype.card_fin,
      ← pow_mul, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  unfold fiberEnergy signedSmoothEnergy
  congr 1
  calc
    _ = ∫ z in unitBall n, R ^ (2 * n) *
        (v (R • complexCoordinates n z) * (modelHessian v (R • complexCoordinates n z)).det.re)
        ∂volume0 n := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change q (L (z, w)) * (KEBall.complexHessian (fun y => q (L (y, w))) z).det.re = _
      rw [hDet]
      change v (R • complexCoordinates n z) * _ = _
      ring
    _ = ((n.factorial : ℝ) / Real.pi ^ n) *
        ∫ y in ball (0 : ComplexModel n) R, v y * (modelHessian v y).det.re :=
      setIntegral_volume0_dilation_coordinates (fun y => v y * (modelHessian v y).det.re) hR
    _ = _ := by
      rw [integral_topMeasure_eq_setIntegral_density hs, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      change ((n.factorial : ℝ) / Real.pi ^ n) * (v y * (modelHessian v y).det.re) =
        ((n.factorial : ℝ) / Real.pi ^ n * (modelHessian v y).det.re) * v y
      ring

end KEBall.BedfordTaylor
