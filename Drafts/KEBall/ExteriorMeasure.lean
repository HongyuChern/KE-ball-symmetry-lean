import Drafts.KEBall.ExteriorEvaluation
import KEBall.SphereMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Positivity

/-!
Stage11 SOURCE_DRAFT_UNCOMPILED.
Euclidean integration of a top form is defined from its actual evaluation
on the oriented standard frame, not from the desired determinant formula.
For arbitrary inputs the definition takes the positive real part. Under
the original solution assumptions the coefficient is real and strictly
positive on the ball, so this truncation does not alter the top form there.
No claim about a separate manifold differential-form integration API is made.
-/
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ContDiff

namespace KEBall

noncomputable def exteriorTopMeasure {n : ℕ} (F : E n → CovectorExterior n) :
    Measure (E n) :=
  volume.withDensity (fun x =>
    ENNReal.ofReal ((exteriorEvaluation (euclideanFrame n) (F x)).re))

noncomputable def d0TopMeasure {n : ℕ} (u : E n → ℝ) : Measure (E n) :=
  exteriorTopMeasure (fun x => d0Exterior u x ^ n)

noncomputable def d1TopMeasure {n : ℕ} (u : E n → ℝ) : Measure (E n) :=
  exteriorTopMeasure (fun x => d1Exterior u x ^ n)

theorem normalizedExteriorVolume_measure (n : ℕ) :
    exteriorTopMeasure (fun _ : E n => normalizedExteriorVolume n) = volume0 n := by
  simp only [exteriorTopMeasure, exteriorEvaluation_normalized_volume, Complex.ofReal_re]
  rw [withDensity_const]
  rfl

/-- A theorem about genuine top-form evaluation; the measure definition contains no det. -/
theorem d0TopMeasure_eq_density {n : ℕ} (u : E n → ℝ) :
    d0TopMeasure u =
      (volume0 n).withDensity (fun x => ENNReal.ofReal (complexHessian u x).det.re) := by
  let c : ℝ := (n.factorial : ℝ) / Real.pi ^ n
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he : (fun x : E n =>
      ENNReal.ofReal ((exteriorEvaluation (euclideanFrame n) (d0Exterior u x ^ n)).re)) =
      ENNReal.ofReal c • (fun x : E n => ENNReal.ofReal (complexHessian u x).det.re) := by
    funext x
    rw [exteriorEvaluation_d0_top]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    change ENNReal.ofReal ((complexHessian u x).det.re * c) = _
    rw [mul_comm, ENNReal.ofReal_mul hc]
    rfl
  unfold d0TopMeasure exteriorTopMeasure
  rw [he, withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    volume0, withDensity_smul_measure]

theorem IsSolution.d0_top_real_positive {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    exteriorEvaluation (euclideanFrame n) (d0Exterior u x ^ n) =
        (((μ * Real.exp (-u x)) * ((n.factorial : ℝ) / Real.pi ^ n) : ℝ) : ℂ) ∧
      0 < (exteriorEvaluation (euclideanFrame n) (d0Exterior u x ^ n)).re := by
  have he : exteriorEvaluation (euclideanFrame n) (d0Exterior u x ^ n) =
      (((μ * Real.exp (-u x)) * ((n.factorial : ℝ) / Real.pi ^ n) : ℝ) : ℂ) := by
    rw [exteriorEvaluation_d0_top, hu.2.2.2.1 x hx]
    simp only [Complex.ofReal_mul]
  refine ⟨he, ?_⟩
  rw [he, Complex.ofReal_re]
  exact mul_pos (mul_pos hu.1 (Real.exp_pos _)) (by positivity)

/-- The original determinant equation becomes the actual Euclidean top-form measure equation. -/
theorem IsSolution.d0TopMeasure_eq {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) :
    (d0TopMeasure u).restrict (unitBall n) =
      ((volume0 n).restrict (unitBall n)).withDensity
        (fun x => ENNReal.ofReal (μ * Real.exp (-u x))) := by
  have hB : MeasurableSet (unitBall n) := Metric.isOpen_ball.measurableSet
  rw [d0TopMeasure_eq_density, restrict_withDensity hB]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet)] with x hx
  rw [hu.2.2.2.1 x hx, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem IsSolution.d1_half_evaluates_derivative {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) (v w : E n) :
    exteriorEvaluation ![v, w] (d1Exterior (fun y => u y / 2) x) =
      ((fderiv ℝ (fun y => dcZeroForm u y w) x v -
        fderiv ℝ (fun y => dcZeroForm u y v) x w : ℝ) : ℂ) := by
  rw [d1Exterior_half (hu.2.1.contDiffAt hx)]
  exact hu.d0Exterior_evaluates_derivative hx v w

/-- D1(u/2)=D0u is used before taking the n-th power and the measure. -/
theorem IsSolution.d1TopMeasure_half {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) :
    (d1TopMeasure (fun y => u y / 2)).restrict (unitBall n) =
      (d0TopMeasure u).restrict (unitBall n) := by
  unfold d1TopMeasure d0TopMeasure exteriorTopMeasure
  have hB : MeasurableSet (unitBall n) := Metric.isOpen_ball.measurableSet
  simp only [restrict_withDensity hB]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet)] with x hx
  rw [d1Exterior_half (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]

#print axioms normalizedExteriorVolume_measure
#print axioms d0TopMeasure_eq_density
#print axioms IsSolution.d0TopMeasure_eq
#print axioms IsSolution.d1TopMeasure_half

end KEBall
