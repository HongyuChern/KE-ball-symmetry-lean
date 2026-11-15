import KEBall.BedfordTaylorWeightedLevi
import KEBall.BedfordTaylorWirtinger

/-!
# Measure coefficients of the distributional complex Hessian

The polarization identity expresses every coefficient as a linear
combination of four positive directional Levi measures. It makes
multiplication by a locally bounded PSH weight available coefficientwise.
-/

set_option autoImplicit false

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Opens E}

private noncomputable abbrev secondDirectional (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) (v w : E) : ℝ :=
  directionalDerivative v (directionalDerivative w T) φ

private theorem secondDirectional_add_left (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) (a b w : E) :
    secondDirectional T φ (a + b) w = secondDirectional T φ a w + secondDirectional T φ b w := by
  simp only [secondDirectional, directionalDerivative, Distribution.lineDerivCLM_add, add_apply]

private theorem secondDirectional_add_right (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) (v a b : E) :
    secondDirectional T φ v (a + b) = secondDirectional T φ v a + secondDirectional T φ v b := by
  simp only [secondDirectional, directionalDerivative, Distribution.lineDerivCLM_add, add_apply,
    map_add]

private theorem secondDirectional_neg_left (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) (v w : E) :
    secondDirectional T φ (-v) w = -secondDirectional T φ v w := by
  simp only [secondDirectional, directionalDerivative_neg, neg_apply]

private theorem secondDirectional_neg_right (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) (v w : E) :
    secondDirectional T φ v (-w) = -secondDirectional T φ v w := by
  simp only [secondDirectional, directionalDerivative_neg, map_neg, neg_apply]

private theorem secondDirectional_comm (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) (v w : E) :
    secondDirectional T φ v w = secondDirectional T φ w v :=
  congrArg (fun S : 𝓓'(U, ℝ) => S φ) (directionalDerivative_comm v w T)

variable [NormedSpace ℂ E]

private theorem distributionalComplexHessian_apply (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) (v w : E) :
    distributionalComplexHessian T v w φ =
      ((secondDirectional T φ v w + secondDirectional T φ (Complex.I • v) (Complex.I • w) : ℝ) :
        ℂ) / 4 +
      Complex.I * ((secondDirectional T φ v (Complex.I • w) -
        secondDirectional T φ (Complex.I • v) w : ℝ) : ℂ) / 4 := by
  change ((1 / 2 : ℂ) •
    (directionalDerivative v
        (wirtingerDerivative w (-(Complex.I • w)) (Distribution.mapCLM Complex.ofRealCLM T)) -
      Complex.I • directionalDerivative (Complex.I • v)
        (wirtingerDerivative w (-(Complex.I • w)) (Distribution.mapCLM Complex.ofRealCLM T)))) φ = _
  simp only [directionalDerivative_wirtingerDerivative, directionalDerivative_neg, map_neg,
    directionalDerivative_mapCLM, smul_apply, sub_apply, neg_apply, smul_eq_mul,
    Distribution.mapCLM_apply, Complex.ofRealCLM_apply, Complex.ofReal_add, Complex.ofReal_sub]
  linear_combination -((secondDirectional T φ (Complex.I • v) (Complex.I • w) : ℝ) : ℂ) / 4 *
    Complex.I_mul_I

/-- Polarize a family of real directional distributions to obtain one
complex coefficient. The sign of the imaginary part is the convention of
the `(∂_v ∂̄_w)` Hessian. -/
noncomputable def polarizedLeviDistribution (L : E → 𝓓'(U, ℝ)) (v w : E) : 𝓓'(U, ℂ) :=
  (1 / 4 : ℂ) •
    (Distribution.mapCLM Complex.ofRealCLM (L (v + w) - L (v - w)) +
      Complex.I • Distribution.mapCLM Complex.ofRealCLM
        (L (v + Complex.I • w) - L (v - Complex.I • w)))

theorem polarizedLeviDistribution_apply (L : E → 𝓓'(U, ℝ)) (v w : E) (φ : 𝓓(U, ℝ)) :
    polarizedLeviDistribution L v w φ =
      ((L (v + w) φ - L (v - w) φ : ℝ) : ℂ) / 4 +
        Complex.I * ((L (v + Complex.I • w) φ - L (v - Complex.I • w) φ : ℝ) : ℂ) / 4 := by
  simp only [polarizedLeviDistribution, smul_apply, add_apply, Distribution.mapCLM_apply,
    Complex.ofRealCLM_apply, sub_apply, smul_eq_mul]
  ring

theorem distributionalComplexHessian_eq_polarized (T : 𝓓'(U, ℝ)) (v w : E) :
    distributionalComplexHessian T v w =
      polarizedLeviDistribution (fun z => distributionalLeviCLM z T) v w := by
  ext φ
  rw [distributionalComplexHessian_apply, polarizedLeviDistribution_apply]
  have hdiag (z : E) : distributionalLeviCLM z T φ =
      (secondDirectional T φ z z + secondDirectional T φ (Complex.I • z) (Complex.I • z)) / 4 := by
    simp only [distributionalLeviCLM_apply, secondDirectional, directionalDerivative,
      Distribution.lineDerivCLM_apply, neg_neg]
    ring
  have hdiff (a b : E) : distributionalLeviCLM (a + b) T φ -
      distributionalLeviCLM (a - b) T φ =
        secondDirectional T φ a b + secondDirectional T φ (Complex.I • a) (Complex.I • b) := by
    simp only [hdiag, sub_eq_add_neg, smul_add, smul_neg,
      secondDirectional_add_left, secondDirectional_add_right, secondDirectional_neg_left,
      secondDirectional_neg_right, secondDirectional_comm T φ b a,
      secondDirectional_comm T φ (Complex.I • b) (Complex.I • a)]
    ring
  rw [hdiff, hdiff, smul_smul, Complex.I_mul_I, neg_one_smul, secondDirectional_neg_right]
  congr 2

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}

theorem distributionalComplexHessian_regularDistribution_apply
    (hp : IsLocallyBoundedPshOn Ω p) (v w : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    distributionalComplexHessian
        (regularDistribution volume p
          (PshLines.FirstPass.MongeAmpere.locallyIntegrableOn_of_plurisubharmonicOn_real hp.1))
        v w φ =
      ((∫ x : Ω, φ x ∂directionalLeviMeasure hp (v + w)) -
        (∫ x : Ω, φ x ∂directionalLeviMeasure hp (v - w)) : ℝ) / 4 +
      Complex.I * (((∫ x : Ω, φ x ∂directionalLeviMeasure hp (v + Complex.I • w)) -
        (∫ x : Ω, φ x ∂directionalLeviMeasure hp (v - Complex.I • w)) : ℝ) : ℂ) / 4 := by
  rw [distributionalComplexHessian_eq_polarized, polarizedLeviDistribution_apply]
  simp_rw [distributionalLeviCLM_regularDistribution_apply, ← integral_directionalLeviMeasure hp]

/-- The coefficients of the product of a locally bounded PSH weight with
the complex Hessian of a second PSH function. -/
noncomputable def weightedComplexHessian (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v w : ComplexModel n) : 𝓓'(Ω, ℂ) :=
  polarizedLeviDistribution (weightedLeviDistribution hu hp) v w

theorem weightedComplexHessian_apply (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v w : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    weightedComplexHessian hu hp v w φ =
      ((∫ x : Ω, φ x * u x ∂directionalLeviMeasure hp (v + w)) -
        (∫ x : Ω, φ x * u x ∂directionalLeviMeasure hp (v - w)) : ℝ) / 4 +
      Complex.I * (((∫ x : Ω, φ x * u x ∂directionalLeviMeasure hp (v + Complex.I • w)) -
        (∫ x : Ω, φ x * u x ∂directionalLeviMeasure hp (v - Complex.I • w)) : ℝ) : ℂ) / 4 := by
  rw [weightedComplexHessian, polarizedLeviDistribution_apply]
  simp_rw [weightedLeviDistribution_apply]

end KEBall.BedfordTaylor
