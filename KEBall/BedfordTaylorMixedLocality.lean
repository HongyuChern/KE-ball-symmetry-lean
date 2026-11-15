import KEBall.BedfordTaylorSmoothMixedHessian

/-!
# Restriction of the second mixed Hessian to open subdomains
-/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U V : Opens E}

/-- Regard a test function of an open subdomain as a test function of the
larger open domain. Its values are the same ambient function. -/
noncomputable def extendTest (hVU : V ≤ U) (φ : 𝓓(V, ℝ)) : 𝓓(U, ℝ) :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩

@[simp]
theorem extendTest_apply (hVU : V ≤ U) (φ : 𝓓(V, ℝ)) (x : E) : extendTest hVU φ x = φ x := rfl

theorem lineDeriv_extendTest (hVU : V ≤ U) (φ : 𝓓(V, ℝ)) (a : E) :
    TestFunction.lineDerivCLM ℝ a (extendTest hVU φ) =
      extendTest hVU (TestFunction.lineDerivCLM ℝ a φ) := by
  apply TestFunction.ext
  intro x
  rw [extendTest_apply, testFunction_lineDerivCLM_apply_eq_fderiv,
    testFunction_lineDerivCLM_apply_eq_fderiv]
  rfl

theorem wirtingerDerivative_extendTest (hVU : V ≤ U) {S : 𝓓'(U, ℂ)} {T : 𝓓'(V, ℂ)}
    (h : ∀ φ : 𝓓(V, ℝ), S (extendTest hVU φ) = T φ)
    (a b : E) (φ : 𝓓(V, ℝ)) :
    wirtingerDerivative a b S (extendTest hVU φ) = wirtingerDerivative a b T φ := by
  simp only [wirtingerDerivative, directionalDerivative, Distribution.lineDerivCLM_apply,
    smul_apply, sub_apply, lineDeriv_extendTest hVU, h]

variable {n : ℕ} {Ω A : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}

theorem weightedLeviDistribution_extendTest (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (hA : A ≤ Ω) (v : ComplexModel n) (φ : 𝓓(A, ℝ)) :
    weightedLeviDistribution hu hp v (extendTest hA φ) =
      weightedLeviDistribution (IsLocallyBoundedPshOn.mono hu hA)
        (IsLocallyBoundedPshOn.mono hp hA) v φ := by
  simp only [weightedLeviDistribution_apply, extendTest_apply]
  rw [← integral_ambientDirectionalLeviMeasure hp v (fun x => φ x * u x),
    ← integral_ambientDirectionalLeviMeasure (IsLocallyBoundedPshOn.mono hp hA) v
      (fun x => φ x * u x), ← ambientDirectionalLeviMeasure_restrict hp hA]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (φ.tsupport_subset hs))
  rw [hφ, zero_mul]

theorem weightedLeviDistribution_congr {u₁ p₁ : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hu₁ : IsLocallyBoundedPshOn Ω u₁)
    (hp : IsLocallyBoundedPshOn Ω p) (hp₁ : IsLocallyBoundedPshOn Ω p₁)
    (huEq : EqOn u u₁ Ω) (hpEq : EqOn p p₁ Ω) (v : ComplexModel n) :
    weightedLeviDistribution hu hp v = weightedLeviDistribution hu₁ hp₁ v := by
  have hμ : directionalLeviMeasure hp v = directionalLeviMeasure hp₁ v := by
    let : (directionalLeviMeasure hp v).Regular := directionalLeviMeasure_regular hp v
    let : (directionalLeviMeasure hp₁ v).Regular := directionalLeviMeasure_regular hp₁ v
    apply measure_eq_of_smooth_test
    intro φ
    rw [integral_directionalLeviMeasure, integral_directionalLeviMeasure]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω
    · rw [hpEq hx]
    · rw [leviForm_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)) v,
        mul_zero, mul_zero]
  ext φ
  rw [weightedLeviDistribution_apply, weightedLeviDistribution_apply, hμ]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => congrArg (φ x * ·) (huEq x.property))

private theorem weightedComplexHessian_extendTest (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (hA : A ≤ Ω) (v w : ComplexModel n) (φ : 𝓓(A, ℝ)) :
    weightedComplexHessian hu hp v w (extendTest hA φ) =
      weightedComplexHessian (IsLocallyBoundedPshOn.mono hu hA)
        (IsLocallyBoundedPshOn.mono hp hA) v w φ := by
  simp only [weightedComplexHessian, polarizedLeviDistribution_apply,
    weightedLeviDistribution_extendTest hu hp hA]

theorem secondMixedHessian_extendTest (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (hA : A ≤ Ω)
    (v w : Fin 2 → ComplexModel n) (φ : 𝓓(A, ℝ)) :
    secondMixedHessian hu hp v w (extendTest hA φ) =
      secondMixedHessian (IsLocallyBoundedPshOn.mono hu hA)
        (IsLocallyBoundedPshOn.mono hp hA) v w φ := by
  have hF (a r b s : ComplexModel n) :=
    wirtingerDerivative_extendTest hA (fun ψ => wirtingerDerivative_extendTest hA
      (weightedComplexHessian_extendTest hu hp hA b s) r (-(Complex.I • r)) ψ) a (Complex.I • a) φ
  simp only [secondMixedHessian_eq, add_apply, sub_apply, hF]

end KEBall.BedfordTaylor
