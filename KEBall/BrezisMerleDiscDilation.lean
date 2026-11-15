import KEBall.BrezisMerleDiscMass
import KEBall.BedfordTaylorFiberChangeVariables

/-!
# The smooth mass estimate on a disk of arbitrary positive radius
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Laplacian

namespace KEBall.BrezisMerle

theorem laplacian_dilate_disc {u : E 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (r : ℝ) (x : E 1) :
    Δ (fun y => u (r • y)) x = r ^ 2 * Δ u (r • x) := by
  let L : E 1 →L[ℝ] E 1 := r • ContinuousLinearMap.id ℝ (E 1)
  have h (a : E 1) :
      realHessian (fun y => u (r • y)) x a a = r ^ 2 * realHessian u (r • x) a a := by
    have he := PshLines.realHessian_comp_affine hu L 0 x a a
    simp only [L, smul_apply, ContinuousLinearMap.id_apply, zero_add,
      PshLines.realHessian_eq_fderiv] at he
    change fderiv ℝ (fderiv ℝ (fun y => u (r • y))) x a a =
      r ^ 2 * fderiv ℝ (fderiv ℝ u) (r • x) a a
    rw [he]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [laplacian_eq_realHessian_disc, h, h, laplacian_eq_realHessian_disc, mul_add]

/-- In dimension two the mass of the pullback to the unit disk is the
Laplacian integral over the original disk with the same normalization. -/
theorem discMass_dilate {u : E 1 → ℝ} (hu : ContDiff ℝ 2 u) {r : ℝ} (hr : 0 < r) :
    discMass (fun y => u (r • y)) = (∫ y in ball (0 : E 1) r, Δ u y) / (4 * Real.pi) := by
  unfold discMass
  simp_rw [laplacian_dilate_disc hu]
  have he := BedfordTaylor.setIntegral_smul_ball (volume : Measure (E 1)) (Δ u) (S := 1) hr
  simpa only [unitBall, finrank_E, mul_one] using congrArg (fun y : ℝ => y / (4 * Real.pi)) he

/-- The shifted exponential estimate on a disk of radius r. -/
theorem lintegral_exp_addBoundary_le_of_ballMass_le {u : E 1 → ℝ} (hu : ContDiff ℝ 2 u)
    {r δ : ℝ} (hr : 0 < r) (hBoundary : ∀ x ∈ sphere (0 : E 1) r, -δ ≤ u x)
    (hΔ : ∀ x ∈ ball (0 : E 1) r, 0 ≤ Δ u x)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hMass : (∫ x in ball (0 : E 1) r, Δ u x) / (4 * Real.pi) ≤ t) :
    (∫⁻ z in ball (0 : E 1) r, ENNReal.ofReal (Real.exp (-(u z + δ))) ∂volume) ≤
      ENNReal.ofReal (r ^ 2 * (4 * Real.pi / (1 - t))) := by
  let L : E 1 →L[ℝ] E 1 := r • ContinuousLinearMap.id ℝ (E 1)
  let w (x : E 1) := u (r • x)
  have hw : ContDiff ℝ 2 w := hu.comp L.contDiff
  have hB (x : E 1) (hx : x ∈ unitSphere 1) : -δ ≤ w x := by
    apply hBoundary
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_of_nonneg hr.le, mem_sphere_zero_iff_norm.mp hx, mul_one]
  have hD (x : E 1) (hx : x ∈ unitBall 1) : 0 ≤ Δ w x := by
    rw [show Δ w x = r ^ 2 * Δ u (r • x) from laplacian_dilate_disc hu r x]
    apply mul_nonneg (sq_nonneg r)
    apply hΔ
    apply mem_ball_zero_iff.mpr
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.mp hx)
  have hM : discMass w ≤ t := (discMass_dilate hu hr).trans_le hMass
  have hExp := lintegral_exp_addBoundary_le_of_discMass_le hw hB hD ht₀ ht₁ hM
  let g (z : E 1) := Real.exp (-(u z + δ))
  have hg : Continuous g := Real.continuous_exp.comp ((hu.continuous.add continuous_const).neg)
  have hInt (R : ℝ) : IntegrableOn g (ball (0 : E 1) R) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hInt' : IntegrableOn (fun x => g (r • x)) (unitBall 1) :=
    ((hg.comp L.continuous).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  have he := BedfordTaylor.setIntegral_smul_ball (volume : Measure (E 1)) g (S := 1) hr
  simp only [finrank_E, mul_one, integral_const_mul] at he
  change (∫⁻ z in ball (0 : E 1) r, ENNReal.ofReal (g z) ∂volume) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal (hInt r) (Eventually.of_forall fun _ => Real.exp_nonneg _),
    ← he, ENNReal.ofReal_mul (sq_nonneg r)]
  change (∫⁻ z in unitBall 1, ENNReal.ofReal (g (r • z)) ∂volume) ≤ _ at hExp
  rw [← ofReal_integral_eq_lintegral_ofReal hInt' (Eventually.of_forall fun _ => Real.exp_nonneg _)] at hExp
  rw [ENNReal.ofReal_mul (sq_nonneg r)]
  exact mul_le_mul_right (show ENNReal.ofReal (∫ x in ball (0 : E 1) 1, g (r • x)) ≤
    ENNReal.ofReal (4 * Real.pi / (1 - t)) from hExp) _

end KEBall.BrezisMerle
