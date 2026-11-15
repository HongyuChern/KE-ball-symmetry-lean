import KEBall.CegrellDirichletComparison
import KEBall.CegrellRadialTests
import KEBall.CegrellScaling
import KEBall.LowerSlope

/-!
# Quadratic bounds from Dirichlet density bounds
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere hiding complexHessian

theorem topMeasure_const_mul_ballQuadratic {n : ℕ} {c : ℝ} (hc : 0 < c) :
    topMeasure ((ballQuadratic_isE0 n).const_mul hc).locallyBoundedPsh =
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * c ^ n) •
        (volume : Measure (ComplexModel n)).restrict (complexUnitBall n) := by
  have hρ : topMeasure (ballQuadratic_isE0 n).locallyBoundedPsh =
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) •
        (volume : Measure (ComplexModel n)).restrict (complexUnitBall n) :=
    (topMeasure_add_const (isLocallyBoundedPshOn_of_isSmoothPshOn (smoothPsh_norm_sq n)) (-1)).trans
      (topMeasure_norm_sq n)
  rw [topMeasure_const_mul (ballQuadratic_isE0 n).locallyBoundedPsh hc, hρ, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), mul_comm (c ^ n)]

/-- A lower and upper bound on the positive determinant sandwich a zero-boundary
potential between two multiples of the quadratic potential. -/
theorem quadratic_bounds_of_det_bounds {n : ℕ} (hn : 0 < n)
    {u : ComplexModel n → ℝ} (hu : IsE0 (complexUnitBall n) u)
    (huS : IsSmoothPshOn (complexUnitBall n) u) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hdet : ∀ x ∈ complexUnitBall n,
      a ^ n ≤ (PshLines.FirstPass.MongeAmpere.complexHessian u x).det.re ∧
        (PshLines.FirstPass.MongeAmpere.complexHessian u x).det.re ≤ b ^ n) :
    ∀ x ∈ complexUnitBall n, b * ballQuadratic n x ≤ u x ∧ u x ≤ a * ballQuadratic n x := by
  have hTop : topMeasure hu.locallyBoundedPsh = smoothMeasure (complexUnitBall n) u huS :=
    topMeasure_eq_smoothMeasure huS
  have hUpper : topMeasure hu.locallyBoundedPsh ≤
      topMeasure ((ballQuadratic_isE0 n).const_mul hb).locallyBoundedPsh := by
    rw [hTop, topMeasure_const_mul_ballQuadratic hb, smoothMeasure, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem (complexUnitBall n).isOpen.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hdet x hx).2 (by positivity))
  have hLower : topMeasure ((ballQuadratic_isE0 n).const_mul ha).locallyBoundedPsh ≤
      topMeasure hu.locallyBoundedPsh := by
    rw [hTop, topMeasure_const_mul_ballQuadratic ha, smoothMeasure, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem (complexUnitBall n).isOpen.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hdet x hx).1 (by positivity))
  exact fun x hx => ⟨((ballQuadratic_isE0 n).const_mul hb).le_of_topMeasure_le_unitBall hn hu hUpper x hx,
    hu.le_of_topMeasure_le_unitBall hn ((ballQuadratic_isE0 n).const_mul ha) hLower x hx⟩

private theorem boundarySlope_scaledQuadratic {n : ℕ} (c : ℝ) {x : E n}
    (hx : x ∈ unitSphere n) :
    boundarySlope (fun y : E n => c * (‖y‖ ^ 2 - 1)) x = c := by
  have h : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have hDiff : DifferentiableAt ℝ (fun y : E n => ‖y‖ ^ 2 - 1) x :=
    (show ContDiff ℝ ∞ (fun y : E n => ‖y‖ ^ 2) from contDiff_norm_sq ℝ).contDiffAt.differentiableAt
      (by simp) |>.sub_const 1
  rw [boundarySlope, fderiv_const_mul hDiff, fderiv_sub_const, fderiv_norm_sq_apply]
  simp [inner_self_eq_norm_sq_to_K, h]

/-- The determinant bounds control both the potential and its boundary slope
in the real coordinates of the Dirichlet problem. -/
theorem quadratic_and_boundarySlope_bounds {n : ℕ} (hn : 0 < n) {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosSemidef)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hdet : ∀ x ∈ unitBall n,
      a ^ n ≤ (complexHessian u x).det.re ∧ (complexHessian u x).det.re ≤ b ^ n) :
    (∀ x ∈ closedUnitBall n, b * (‖x‖ ^ 2 - 1) ≤ u x ∧ u x ≤ a * (‖x‖ ^ 2 - 1)) ∧
      ∀ x ∈ unitSphere n, a ≤ boundarySlope u x ∧ boundarySlope u x ≤ b := by
  let e := complexCoordinates n
  let q := u ∘ e.symm
  have he (x : E n) : e x ∈ complexUnitBall n ↔ x ∈ unitBall n := by
    change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n)) ↔ x ∈ unitBall n
    rw [preimage_complexUnitBall]
  have hq := MoserTrudinger.isE0_onBall_of_smooth_real_model hu huP hu0
  have hqC : ContDiffOn ℝ ∞ q (complexUnitBall n) := by
    obtain ⟨U, _, hBU, hU⟩ := hu
    exact hU.comp e.symm.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun z hz => by
        have hz' : z ∈ complexUnitBall n := hz
        exact hBU (ball_subset_closedBall ((he (e.symm z)).mp (by simpa only [e.apply_symm_apply] using hz'))))
  have hqS : IsSmoothPshOn (complexUnitBall n) q := isSmoothPshOn_of_psh hqC hq.psh
  have hqDet (z : ComplexModel n) (hz : z ∈ complexUnitBall n) :
      a ^ n ≤ (PshLines.FirstPass.MongeAmpere.complexHessian q z).det.re ∧
        (PshLines.FirstPass.MongeAmpere.complexHessian q z).det.re ≤ b ^ n := by
    have hx : e.symm z ∈ unitBall n := (he _).mp (by simpa only [e.apply_symm_apply] using hz)
    have hh := complexHessian_coordinates (hu.contDiffAt (ball_subset_closedBall hx))
    change PshLines.FirstPass.MongeAmpere.complexHessian q (e (e.symm z)) =
      complexHessian u (e.symm z) at hh
    rw [e.apply_symm_apply] at hh
    simpa only [hh] using hdet _ hx
  have hI (x : E n) (hx : x ∈ unitBall n) :
      b * (‖x‖ ^ 2 - 1) ≤ u x ∧ u x ≤ a * (‖x‖ ^ 2 - 1) := by
    have h := quadratic_bounds_of_det_bounds hn hq hqS ha hb hqDet (e x) ((he x).mpr hx)
    change b * (‖e x‖ ^ 2 - 1) ≤ u (e.symm (e x)) ∧
      u (e.symm (e x)) ≤ a * (‖e x‖ ^ 2 - 1) at h
    simpa only [e.norm_map, e.symm_apply_apply] using h
  have hClosed (x : E n) (hx : x ∈ closedUnitBall n) :
      b * (‖x‖ ^ 2 - 1) ≤ u x ∧ u x ≤ a * (‖x‖ ^ 2 - 1) := by
    have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    rcases hx'.lt_or_eq with hlt | heq
    · exact hI x (mem_ball_zero_iff.mpr hlt)
    · have hxS : x ∈ unitSphere n := mem_sphere_zero_iff_norm.mpr heq
      simp [heq, hu0 x hxS]
  refine ⟨hClosed, fun x hx => ?_⟩
  have hEq (c : ℝ) : c * (‖x‖ ^ 2 - 1) = u x := by
    simp [mem_sphere_zero_iff_norm.mp hx, hu0 x hx]
  have hDiff (c : ℝ) : DifferentiableAt ℝ (fun y : E n => c * (‖y‖ ^ 2 - 1)) x :=
    have hC : ContDiff ℝ ∞ (fun y : E n => c * (‖y‖ ^ 2 - 1)) :=
      contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)
    hC.contDiffAt.differentiableAt (by simp)
  have huDiff := (hu.contDiffAt (sphere_subset_closedBall hx)).differentiableAt (by simp)
  have h₁ := boundarySlope_ge_of_le hx huDiff (hDiff a) (fun y hy => (hClosed y hy).2) (hEq a).symm
  have h₂ := boundarySlope_ge_of_le hx (hDiff b) huDiff (fun y hy => (hClosed y hy).1) (hEq b)
  simpa only [boundarySlope_scaledQuadratic _ hx] using And.intro h₁ h₂

end KEBall.Cegrell
