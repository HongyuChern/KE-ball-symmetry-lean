import KEBall.MetricHessian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Stage10 SOURCE_DRAFT_UNCOMPILED.
The degree-two D0 convention is realized by continuous bilinear forms and
the actual exterior derivative in a constant Euclidean frame. No top wedge
power, determinant density, or differential-form measure is assumed here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder

namespace KEBall

/-- The real one-form corresponding to (i/(4*pi)) (dbar - d). -/
noncomputable def dcZeroForm {n : ℕ} (u : E n → ℝ) (x : E n) : E n →L[ℝ] ℝ :=
  (-(4 * Real.pi)⁻¹) • (fderiv ℝ u x).comp (JCLM n)

/-- The concrete candidate D0 two-form, with the frozen real metric convention. -/
noncomputable def d0BilinearForm {n : ℕ} (u : E n → ℝ) (x : E n) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  (2 * Real.pi)⁻¹ • (hermitianRealification (complexHessian u x)).comp (JCLM n)

theorem dcZeroForm_apply {n : ℕ} (u : E n → ℝ) (x v : E n) :
    dcZeroForm u x v = -(4 * Real.pi)⁻¹ * fderiv ℝ u x (J v) := by
  simp only [dcZeroForm, smul_apply, ContinuousLinearMap.comp_apply,
    JCLM_apply, smul_eq_mul]

theorem d0BilinearForm_apply {n : ℕ} (u : E n → ℝ) (x v w : E n) :
    d0BilinearForm u x v w = (2 * Real.pi)⁻¹ * realMetricForm u x (J v) w := by
  simp only [d0BilinearForm, smul_apply, ContinuousLinearMap.comp_apply,
    JCLM_apply, smul_eq_mul, realMetricForm_eq]

theorem fderiv_dcZeroForm_apply {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    fderiv ℝ (fun y => dcZeroForm u y w) x v =
      -(4 * Real.pi)⁻¹ * realHessian u x v (J w) := by
  have hdf := (hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have heval := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const (J w) x)
  have hd := heval.const_mul (-(4 * Real.pi)⁻¹)
  simp_rw [dcZeroForm_apply]
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    add_apply, zero_apply, map_zero, zero_add, realHessian, ContinuousLinearMap.flip_apply]

/-- Actual d(dc0 u), evaluated on constant vector fields v and w. -/
theorem d0BilinearForm_eq_exteriorDerivative {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    d0BilinearForm u x v w =
      fderiv ℝ (fun y => dcZeroForm u y w) x v -
        fderiv ℝ (fun y => dcZeroForm u y v) x w := by
  rw [d0BilinearForm_apply, realMetricForm_eq_average_hessian hu,
    J_sq, fderiv_dcZeroForm_apply hu, fderiv_dcZeroForm_apply hu]
  simp only [map_neg, neg_apply]
  rw [realHessian_symm hu (J v) w]
  field_simp [Real.pi_ne_zero]
  ring

theorem d0BilinearForm_skew {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    d0BilinearForm u x v w = -d0BilinearForm u x w v := by
  rw [d0BilinearForm_eq_exteriorDerivative hu, d0BilinearForm_eq_exteriorDerivative hu]
  ring

theorem d0BilinearForm_alternating {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v : E n) : d0BilinearForm u x v v = 0 := by
  rw [d0BilinearForm_eq_exteriorDerivative hu, sub_self]

theorem d0BilinearForm_J_J {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    d0BilinearForm u x (J v) (J w) = d0BilinearForm u x v w := by
  rw [d0BilinearForm_apply, d0BilinearForm_apply,
    realMetricForm_J_J hu (J v) w]

/-- The positive orientation is (v,Jv), with no missing factor two. -/
theorem d0BilinearForm_on_J_pair {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v : E n) :
    d0BilinearForm u x v (J v) = (2 * Real.pi)⁻¹ * realMetricForm u x v v := by
  rw [d0BilinearForm_apply, realMetricForm_J_J hu]

theorem d0BilinearForm_positive {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (complexHessian u x).PosDef)
    {v : E n} (hv : v ≠ 0) : 0 < d0BilinearForm u x v (J v) := by
  rw [d0BilinearForm_on_J_pair hu, realMetricForm_eq]
  exact mul_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
    (hermitianRealification_pos hpos v hv)

/-- At every point where the metric is realized, D0u = omega_u/(2*pi). -/
theorem d0BilinearForm_eq_metric {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)} {u : E n → ℝ} {x : E n}
    (hg : ∀ v w : E n, g.inner x v w = realMetricForm u x v w) (v w : E n) :
    d0BilinearForm u x v w = (2 * Real.pi)⁻¹ * g.inner x (J v) w := by
  rw [d0BilinearForm_apply, hg]

#print axioms d0BilinearForm_eq_exteriorDerivative
#print axioms d0BilinearForm_positive

end KEBall
