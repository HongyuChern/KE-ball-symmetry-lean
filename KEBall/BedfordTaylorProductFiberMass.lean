import KEBall.BedfordTaylorProductFiberCollar
import KEBall.BedfordTaylorCompactDifference

/-!
# Uniform vertical mass of the smoothed fiber extension
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsSmoothPshOn isSmoothPshOn_of_psh isSmoothPshOn_norm_sq smoothDensity smoothMeasure)
open PshLines.Regularization.HolomorphicPullback

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

private theorem topMeasure_univ_eq_lintegral_det {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u) :
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) univ =
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) *
        ∫⁻ x in (Ω : Set (ComplexModel n)), ENNReal.ofReal (modelHessian u x).det.re := by
  rw [topMeasure_eq_smoothMeasure hu, smoothMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp_rw [smoothDensity, ENNReal.ofReal_mul (by positivity : 0 ≤ (n.factorial : ℝ) / Real.pi ^ n)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- A common quadratic collar gives exact equality of the total vertical
Hessian mass before and after smoothing. -/
theorem lintegral_fiber_det_eq_of_quadratic_collar {n m : ℕ}
    {q : ComplexModel (n + m) → ℝ} {W : Opens (ComplexModel (n + m))}
    (hq : ContDiff ℝ ∞ q) (hP : IsSmoothPshOn W q)
    {w : ComplexModel m} {r R A d : ℝ} (hr : r < R) (hA : 0 < A)
    (hW : ∀ z ∈ ball (0 : ComplexModel n) R, (complexProductCoordinates n m).symm (z, w) ∈ W)
    (hCollar : ∀ z ∈ ball (0 : ComplexModel n) R, r < ‖z‖ →
      q ((complexProductCoordinates n m).symm (z, w)) = A * ‖z‖ ^ 2 + d) :
    (∫⁻ z in ball (0 : ComplexModel n) R,
      ENNReal.ofReal (modelHessian
        (fun y => q ((complexProductCoordinates n m).symm (y, w))) z).det.re) =
      ENNReal.ofReal (A ^ n) * (volume : Measure (ComplexModel n)) (ball 0 R) := by
  let B : Opens (ComplexModel n) := ⟨ball 0 R, isOpen_ball⟩
  let e := complexProductCoordinates n m
  let f (z : ComplexModel n) := q (e.symm (z, w))
  let b (z : ComplexModel n) := A * ‖z‖ ^ 2 + d
  let F (z : ComplexModel n) := e.symm (z, w)
  have hF : Differentiable ℂ F := e.symm.differentiable.comp (differentiable_id.prodMk (differentiable_const w))
  let ei : ComplexModel n × ComplexModel m →L[ℝ] ComplexModel (n + m) :=
    e.symm.toContinuousLinearMap.restrictScalars ℝ
  have hFC : ContDiff ℝ ∞ F := ei.contDiff.comp (contDiff_id.prodMk (contDiff_const (c := w)))
  have hf : IsSmoothPshOn B f := isSmoothPshOn_of_psh (hq.comp hFC).contDiffOn
    (locallyBoundedPsh_comp_holomorphic (U := B) (isLocallyBoundedPshOn_of_isSmoothPshOn hP)
      hF.differentiableOn hW).1
  have hq₀ : IsSmoothPshOn B (fun z => A * ‖z‖ ^ 2) := smoothPsh_const_mul (isSmoothPshOn_norm_sq B) hA
  have hb : IsSmoothPshOn B b := isSmoothPshOn_of_psh
    (hq₀.1.add contDiffOn_const)
    (locallyBoundedPsh_add_const (isLocallyBoundedPshOn_of_isSmoothPshOn hq₀) d).1
  have he : EqOn f b ((B : Set (ComplexModel n)) \ closedBall 0 r) := by
    intro z hz
    apply hCollar z hz.1
    exact lt_of_not_ge (fun h => hz.2 (mem_closedBall_zero_iff.mpr h))
  have hmass := topMeasure_total_eq_of_eq_off_compact
    (isLocallyBoundedPshOn_of_isSmoothPshOn hf) (isLocallyBoundedPshOn_of_isSmoothPshOn hb)
    (isCompact_closedBall (0 : ComplexModel n) r) (closedBall_subset_ball hr) he
  rw [topMeasure_univ_eq_lintegral_det hf, topMeasure_univ_eq_lintegral_det hb] at hmass
  have hmass' := (ENNReal.mul_right_inj
    (by positivity : ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) ≠ 0)
    ENNReal.ofReal_ne_top).mp hmass
  change (∫⁻ z in (B : Set (ComplexModel n)), ENNReal.ofReal (modelHessian f z).det.re) = _
  rw [hmass']
  have hBdet (z : ComplexModel n) : (modelHessian b z).det.re = A ^ n := by
    let p : ComplexModel n → ℝ := fun z => ‖z‖ ^ 2
    have hp : ContDiffAt ℝ 2 p z := (contDiff_norm_sq ℝ).contDiffAt
    have hd : fderiv ℝ b = fderiv ℝ (A • p) :=
      funext fun x => fderiv_add_const d
    have hB : modelHessian b z = modelHessian (A • p) z := by
      ext i j : 1
      simp only [PshLines.FirstPass.MongeAmpere.complexHessian, realHessian_eq_fderiv, hd]
    rw [hB, PshLines.FirstPass.MongeAmpere.complexHessian_smul hp A,
      PshLines.FirstPass.MongeAmpere.complexHessian_norm_sq z,
      Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Complex.ofReal_pow, Complex.ofReal_re]
  simp_rw [hBdet]
  rw [lintegral_const, Measure.restrict_apply_univ]
  rfl

end KEBall.BedfordTaylor
