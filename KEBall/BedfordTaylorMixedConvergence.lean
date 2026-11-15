import KEBall.BedfordTaylorSmoothMixedHessian

/-!
# Separate convergence for the second mixed Hessian

A decreasing sequence of weights can be integrated against a fixed Levi
measure. A fixed smooth weight instead permits convergence of the Levi
measures. These two limits permit successive smoothing of the two factors.
-/

set_option autoImplicit false

open Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Opens E}

theorem tendsto_wirtingerDerivative_test {T : ℕ → 𝓓'(U, ℂ)} {S : 𝓓'(U, ℂ)}
    (h : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => T j φ) atTop (𝓝 (S φ)))
    (a b : E) (φ : 𝓓(U, ℝ)) :
    Tendsto (fun j => wirtingerDerivative a b (T j) φ) atTop
      (𝓝 (wirtingerDerivative a b S φ)) := by
  simp only [wirtingerDerivative, directionalDerivative, Distribution.lineDerivCLM_apply,
    smul_apply, sub_apply, smul_eq_mul]
  exact tendsto_const_nhds.mul ((h _).neg.sub (tendsto_const_nhds.mul (h _).neg))

theorem tendsto_polarizedLeviDistribution_test [NormedSpace ℂ E]
    {L : ℕ → E → 𝓓'(U, ℝ)} {S : E → 𝓓'(U, ℝ)}
    (h : ∀ v (φ : 𝓓(U, ℝ)), Tendsto (fun j => L j v φ) atTop (𝓝 (S v φ)))
    (v w : E) (φ : 𝓓(U, ℝ)) :
    Tendsto (fun j => polarizedLeviDistribution (L j) v w φ) atTop
      (𝓝 (polarizedLeviDistribution S v w φ)) := by
  simp_rw [polarizedLeviDistribution_apply]
  have hsub (a b : E) : Tendsto (fun j => ((L j a φ - L j b φ : ℝ) : ℂ)) atTop
      (𝓝 ((S a φ - S b φ : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp ((h a φ).sub (h b φ))
  exact ((hsub (v + w) (v - w)).div_const _).add
    ((tendsto_const_nhds.mul (hsub (v + Complex.I • w) (v - Complex.I • w))).div_const _)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}
  {q : ℕ → ComplexModel n → ℝ}

theorem tendsto_secondMixedHessian_of_weightedComplexHessian_test
    {hu : IsLocallyBoundedPshOn Ω u} {hp : IsLocallyBoundedPshOn Ω p}
    {u' p' : ℕ → ComplexModel n → ℝ}
    {hu' : ∀ j, IsLocallyBoundedPshOn Ω (u' j)} {hp' : ∀ j, IsLocallyBoundedPshOn Ω (p' j)}
    (h : ∀ a b (φ : 𝓓(Ω, ℝ)),
      Tendsto (fun j => weightedComplexHessian (hu' j) (hp' j) a b φ) atTop
        (𝓝 (weightedComplexHessian hu hp a b φ)))
    (v w : Fin 2 → ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => secondMixedHessian (hu' j) (hp' j) v w φ) atTop
      (𝓝 (secondMixedHessian hu hp v w φ)) := by
  have hF (a r b s : ComplexModel n) :=
    tendsto_wirtingerDerivative_test (fun ψ =>
      tendsto_wirtingerDerivative_test (h b s) r (-(Complex.I • r)) ψ) a (Complex.I • a) φ
  simp only [secondMixedHessian_eq, sub_apply, add_apply]
  exact (((hF (v 0) (w 0) (v 1) (w 1)).sub (hF (v 1) (w 0) (v 0) (w 1))).sub
    (hF (v 0) (w 1) (v 1) (w 0))).add (hF (v 1) (w 1) (v 0) (w 0))

/-- Test convergence of the second mixed Hessian when only the weight
decreases and the second potential stays fixed. -/
theorem tendsto_secondMixedHessian_weight_test
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    (v w : Fin 2 → ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => secondMixedHessian (hq j) hp v w φ) atTop
      (𝓝 (secondMixedHessian hu hp v w φ)) := by
  apply tendsto_secondMixedHessian_of_weightedComplexHessian_test _ v w φ
  intro a b ψ
  simp only [weightedComplexHessian]
  apply tendsto_polarizedLeviDistribution_test _ a b ψ
  intro z η
  let : (directionalLeviMeasure hp z).Regular := directionalLeviMeasure_regular hp z
  simp_rw [weightedLeviDistribution_apply]
  exact tendsto_integral_psh_weight_of_antitone hu hq hanti hlim (directionalLeviMeasure hp z) η

/-- Test convergence when the first factor is a fixed smooth weight and
the second potential decreases. -/
theorem tendsto_secondMixedHessian_potential_test
    (hu : IsSmoothPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (p x)))
    (v w : Fin 2 → ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => secondMixedHessian (isLocallyBoundedPshOn_of_isSmoothPshOn hu) (hq j) v w φ)
      atTop (𝓝 (secondMixedHessian (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hp v w φ)) := by
  apply tendsto_secondMixedHessian_of_weightedComplexHessian_test _ v w φ
  intro a b ψ
  simp only [weightedComplexHessian]
  apply tendsto_polarizedLeviDistribution_test _ a b ψ
  intro z η
  simp_rw [weightedLeviDistribution_apply]
  exact tendsto_directionalLeviMeasure_test hp hq hanti hlim z (multiplySmoothTest η hu.1)

end KEBall.BedfordTaylor
