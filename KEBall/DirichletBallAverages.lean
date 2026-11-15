import KEBall.DirichletWeakHarnack
import DifferentialGeometry.External.DeGiorgi.Oscillation.BMO

/-! Exact normalization of local ball averages in real dimension `2n`. -/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

namespace KEBall

def dirichletBallProbability {n : ℕ} (x : E n) (r : ℝ) : Measure (E n) :=
  (volume (ball x r))⁻¹ • volume.restrict (ball x r)

theorem isProbabilityMeasure_dirichletBallProbability {n : ℕ} (x : E n)
    {r : ℝ} (hr : 0 < r) : IsProbabilityMeasure (dirichletBallProbability x r) := by
  constructor
  simp only [dirichletBallProbability, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

theorem ae_dirichletBallProbability_iff {n : ℕ} {x : E n} {r : ℝ} {P : E n → Prop} :
    (∀ᵐ y ∂dirichletBallProbability x r, P y) ↔
      ∀ᵐ y ∂(volume : Measure (E n)).restrict (ball x r), P y :=
  Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)

theorem essSup_dirichletBallProbability {n : ℕ} (x : E n) (r : ℝ) (f : E n → ℝ) :
    essSup f (dirichletBallProbability x r) = essSup f (volume.restrict (ball x r)) := by
  exact essSup_ennreal_smul_measure (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne) f

theorem essInf_dirichletBallProbability {n : ℕ} (x : E n) (r : ℝ) (f : E n → ℝ) :
    essInf f (dirichletBallProbability x r) = essInf f (volume.restrict (ball x r)) := by
  unfold essInf dirichletBallProbability
  rw [Measure.ae_ennreal_smul_measure_eq (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)]

theorem integrable_dirichletBallProbability_iff {n : ℕ} {x : E n} {r : ℝ}
    (hr : 0 < r) {f : E n → ℝ} :
    Integrable f (dirichletBallProbability x r) ↔ IntegrableOn f (ball x r) volume :=
  integrable_inv_smul_measure (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

theorem integral_dirichletBallProbability {n : ℕ} (x : E n) (r : ℝ) (f : E n → ℝ) :
    (∫ y, f y ∂dirichletBallProbability x r) =
      (volume.real (ball x r))⁻¹ * ∫ y in ball x r, f y := by
  rw [dirichletBallProbability, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, Measure.real]

def dirichletQuarterAverageScale (n : ℕ) : ℝ :=
  (4 : ℝ) ^ (2 * n) / volume.real (ball (0 : E n) 1)

theorem dirichletQuarterAverageScale_pos (n : ℕ) : 0 < dirichletQuarterAverageScale n := by
  apply div_pos (by positivity)
  exact ENNReal.toReal_pos (measure_ball_pos volume (0 : E n) zero_lt_one).ne'
    measure_ball_lt_top.ne

/-- Exact factor relating the normalized inner-ball average to the
`R^(-2n)` integral in the pinned scaled Harnack theorem. -/
theorem integral_dirichletBallProbability_quarter {n : ℕ}
    (x : E n) {R : ℝ} (hR : 0 < R) (f : E n → ℝ) :
    (∫ y, f y ∂dirichletBallProbability x (R / 4)) =
      dirichletQuarterAverageScale n *
        ((R ^ (2 * n))⁻¹ * ∫ y in ball x (R / 4), f y) := by
  rw [integral_dirichletBallProbability,
    DeGiorgi.volumeReal_ball_eq x (by positivity : 0 < R / 4), div_pow]
  simp only [dirichletQuarterAverageScale, mul_inv_rev, inv_div, div_eq_mul_inv, inv_inv]
  ring

end KEBall
