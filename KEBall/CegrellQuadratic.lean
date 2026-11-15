import KEBall.CegrellTruncatedLimit
import KEBall.BedfordTaylorSmoothCriterion

/-!
# Quadratic comparison potentials on the ball
-/

set_option autoImplicit false

open MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere hiding complexHessian

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

theorem smoothPsh_norm_sq (n : ℕ) :
    IsSmoothPshOn (complexUnitBall n) (fun x : ComplexModel n => ‖x‖ ^ 2) := by
  apply isSmoothPshOn_of_coordinateHessian (contDiff_norm_sq ℝ).contDiffOn
  intro x _
  rw [complexHessian_norm_sq]
  exact Matrix.PosSemidef.one

theorem topMeasure_norm_sq (n : ℕ) :
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn (smoothPsh_norm_sq n)) =
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) •
        (volume : Measure (ComplexModel n)).restrict (complexUnitBall n) := by
  rw [topMeasure_eq_smoothMeasure (smoothPsh_norm_sq n), smoothMeasure]
  simp only [smoothDensity, complexHessian_norm_sq, Matrix.det_one, Complex.one_re, mul_one]
  rw [withDensity_const]

noncomputable def ballQuadratic (n : ℕ) (x : ComplexModel n) : ℝ := ‖x‖ ^ 2 - 1

theorem ballQuadratic_neg (n : ℕ) {x : ComplexModel n} (hx : x ∈ complexUnitBall n) :
    ballQuadratic n x < 0 := by
  have hn : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  unfold ballQuadratic
  nlinarith [norm_nonneg x]

theorem ballQuadratic_isE0 (n : ℕ) : IsE0 (complexUnitBall n) (ballQuadratic n) := by
  have hC : ContDiff ℝ ∞ (ballQuadratic n) := (contDiff_norm_sq ℝ).sub contDiff_const
  have hS : IsSmoothPshOn (complexUnitBall n) (ballQuadratic n) := by
    apply isSmoothPshOn_of_coordinateHessian hC.contDiffOn
    intro x _
    have h : modelHessian (ballQuadratic n) x =
        modelHessian (fun x : ComplexModel n => ‖x‖ ^ 2) x := by
      have hdf : fderiv ℝ (ballQuadratic n) =
          fderiv ℝ (fun x : ComplexModel n => ‖x‖ ^ 2) := funext fun _ => fderiv_sub_const _
      ext i j : 1
      simp only [PshLines.FirstPass.MongeAmpere.complexHessian, PshLines.realHessian_eq_fderiv, hdf]
    rw [h, complexHessian_norm_sq]
    exact Matrix.PosSemidef.one
  apply isE0_of_smoothOn_closure (isCompact_closure_complexUnitBall n)
    (W := ⊤) (subset_univ _) hS hC.contDiffOn
  intro x hx
  change x ∈ frontier (ball (0 : ComplexModel n) 1) at hx
  rw [frontier_ball _ one_ne_zero] at hx
  simp only [ballQuadratic, mem_sphere_zero_iff_norm.mp hx, one_pow, sub_self, Pi.zero_apply]

end KEBall.Cegrell
