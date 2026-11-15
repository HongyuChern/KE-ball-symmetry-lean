import KEBall.CegrellQuadratic
import KEBall.CegrellSubextensionComparison

/-!
# Comparison and uniform stability for bounded Dirichlet potentials
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere hiding complexHessian

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

variable {n : ℕ} {u v : ComplexModel n → ℝ}

/-- For zero-boundary potentials, an order on their measures gives the reverse
order on the potentials. -/
theorem IsE0.le_of_topMeasure_le_unitBall (hn : 0 < n)
    (hu : IsE0 (complexUnitBall n) u) (hv : IsE0 (complexUnitBall n) v)
    (hμ : topMeasure hv.locallyBoundedPsh ≤ topMeasure hu.locallyBoundedPsh) :
    ∀ x ∈ complexUnitBall n, u x ≤ v x :=
  hv.subextension_le hn (isCompact_closure_complexUnitBall n) le_rfl
    hu.locallyBoundedPsh (hu.nonpositive_unitBall hn) hμ

/-- A constant error in the measure comparison can be absorbed by a quadratic
with the same zero boundary data. -/
theorem IsE0.add_ballQuadratic_le_of_topMeasure_le (hn : 0 < n)
    (hu : IsE0 (complexUnitBall n) u) (hv : IsE0 (complexUnitBall n) v)
    {c : ℝ} (hc : 0 < c)
    (hμ : topMeasure hu.locallyBoundedPsh ≤ topMeasure hv.locallyBoundedPsh +
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * c ^ n) •
        (volume : Measure (ComplexModel n)).restrict (complexUnitBall n)) :
    ∀ x ∈ complexUnitBall n, v x + c * ballQuadratic n x ≤ u x := by
  let q := locallyBoundedPsh_add_quadratic hv.locallyBoundedPsh hc
  let w (x : ComplexModel n) := v x + c * ‖x‖ ^ 2 + -c
  let hw := locallyBoundedPsh_add_const q (-c)
  have hwEq (x : ComplexModel n) : w x = v x + c * ballQuadratic n x := by
    simp only [w, ballQuadratic, mul_sub, mul_one]
    ring
  have hneg (x : ComplexModel n) (hx : x ∈ complexUnitBall n) : w x ≤ 0 := by
    rw [hwEq]
    exact add_nonpos (hv.nonpositive_unitBall hn x hx)
      (mul_nonpos_of_nonneg_of_nonpos hc.le (ballQuadratic_neg n hx).le)
  have hμ' : topMeasure hu.locallyBoundedPsh ≤ topMeasure hw :=
    hμ.trans ((topMeasure_add_quadratic_ge hn hv.locallyBoundedPsh hc).trans_eq
      (topMeasure_add_const q (-c)).symm)
  intro x hx
  rw [← hwEq]
  exact hu.subextension_le hn (isCompact_closure_complexUnitBall n) le_rfl hw hneg hμ' x hx

/-- Two-sided additive errors in the measures give a pointwise error that
vanishes at the sphere, hence a uniform estimate on the ball. -/
theorem IsE0.abs_sub_le_of_topMeasure_add_bounds (hn : 0 < n)
    (hu : IsE0 (complexUnitBall n) u) (hv : IsE0 (complexUnitBall n) v)
    {c : ℝ} (hc : 0 < c)
    (hμ : topMeasure hu.locallyBoundedPsh ≤ topMeasure hv.locallyBoundedPsh +
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * c ^ n) •
        (volume : Measure (ComplexModel n)).restrict (complexUnitBall n))
    (hν : topMeasure hv.locallyBoundedPsh ≤ topMeasure hu.locallyBoundedPsh +
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * c ^ n) •
        (volume : Measure (ComplexModel n)).restrict (complexUnitBall n)) :
    ∀ x ∈ complexUnitBall n, |u x - v x| ≤ c * (1 - ‖x‖ ^ 2) := by
  intro x hx
  have h₁ := hu.add_ballQuadratic_le_of_topMeasure_le hn hv hc hμ x hx
  have h₂ := hv.add_ballQuadratic_le_of_topMeasure_le hn hu hc hν x hx
  rw [ballQuadratic, mul_sub, mul_one] at h₁ h₂
  rw [abs_le, mul_sub, mul_one]
  exact ⟨by linarith only [h₁], by linarith only [h₂]⟩

private theorem topMeasure_le_add_of_det_le
    (hu : IsSmoothPshOn (complexUnitBall n) u) (hv : IsSmoothPshOn (complexUnitBall n) v)
    {c : ℝ} (hc : 0 < c)
    (hdet : ∀ x ∈ complexUnitBall n,
      (modelHessian u x).det.re ≤ (modelHessian v x).det.re + c ^ n) :
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) ≤
      topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hv) +
        ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * c ^ n) •
          (volume : Measure (ComplexModel n)).restrict (complexUnitBall n) := by
  rw [topMeasure_eq_smoothMeasure hu, topMeasure_eq_smoothMeasure hv, smoothMeasure, smoothMeasure,
    ← withDensity_const, ← withDensity_add_right _ measurable_const]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem (complexUnitBall n).isOpen.measurableSet] with x hx
  simp only [Pi.add_apply]
  rw [← ENNReal.ofReal_add (smoothDensity_nonneg (hv.2.2 x hx)) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [smoothDensity, ← mul_add]
  exact mul_le_mul_of_nonneg_left (hdet x hx) (by positivity)

/-- Smooth zero-boundary solutions with determinants that differ by at most
c^n differ by at most c times the quadratic boundary distance. -/
theorem abs_sub_le_of_det_difference (hn : 0 < n)
    (hu : IsE0 (complexUnitBall n) u) (hv : IsE0 (complexUnitBall n) v)
    (huS : IsSmoothPshOn (complexUnitBall n) u) (hvS : IsSmoothPshOn (complexUnitBall n) v)
    {c : ℝ} (hc : 0 < c)
    (hdet : ∀ x ∈ complexUnitBall n,
      |(modelHessian u x).det.re - (modelHessian v x).det.re| ≤ c ^ n) :
    ∀ x ∈ complexUnitBall n, |u x - v x| ≤ c * (1 - ‖x‖ ^ 2) := by
  apply hu.abs_sub_le_of_topMeasure_add_bounds hn hv hc
  · apply topMeasure_le_add_of_det_le huS hvS hc
    intro x hx
    linarith only [(abs_le.mp (hdet x hx)).2]
  · apply topMeasure_le_add_of_det_le hvS huS hc
    intro x hx
    linarith only [(abs_le.mp (hdet x hx)).1]

end KEBall.Cegrell
