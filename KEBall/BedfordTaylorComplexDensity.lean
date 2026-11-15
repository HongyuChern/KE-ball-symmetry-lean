import KEBall.BedfordTaylorWirtinger
import KEBall.LocalWirtinger
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Regular distributions with complex densities

Integration by parts identifies their distributional Wirtinger derivatives
with the classical derivatives when the density is smooth on the domain.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

namespace KEBall.BedfordTaylor

open KEBallProbe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {U : Opens E}

/-- The regular distribution induced by a locally integrable complex density. -/
noncomputable def complexRegularDistribution (μ : Measure E) (g : E → ℂ)
    (_hg : LocallyIntegrableOn g U μ) : 𝓓'(U, ℂ) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ g

theorem complexRegularDistribution_apply (μ : Measure E) (g : E → ℂ)
    (hg : LocallyIntegrableOn g U μ) (φ : 𝓓(U, ℝ)) :
    complexRegularDistribution μ g hg φ = ∫ x, φ x • g x ∂μ :=
  TestFunction.integralAgainstBilinCLM_eq_integral hg

variable [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem locallyIntegrableOn_of_contDiffOn {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U) :
    LocallyIntegrableOn g U μ :=
  (locallyIntegrableOn_iff U.isOpen.isLocallyClosed).2 fun _ hKU hK =>
    (hg.continuousOn.mono hKU).integrableOn_compact hK

theorem directionalDerivative_complexRegularDistribution {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (v : E) :
    directionalDerivative v (complexRegularDistribution μ g (locallyIntegrableOn_of_contDiffOn hg)) =
      complexRegularDistribution μ (rd v g)
        (locallyIntegrableOn_of_contDiffOn (smoothOn_rd U.isOpen hg v)) := by
  ext φ
  let ψ : 𝓓(U, ℝ) := TestFunction.lineDerivCLM ℝ v φ
  have hψ : ∀ x, ψ x = fderiv ℝ φ x v :=
    fun x => PshLines.testFunction_lineDerivCLM_apply_eq_fderiv φ v x
  have hL := locallyIntegrableOn_of_contDiffOn (μ := μ) hg
  have hD := locallyIntegrableOn_of_contDiffOn (μ := μ) (smoothOn_rd U.isOpen hg v)
  let B : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hleft : Integrable (fun x => B (fderiv ℝ φ x v) (g x)) μ := by
    simpa only [← hψ] using ψ.integrable_bilin B hL
  have hibp := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (v := v) hleft
    (φ.integrable_bilin B hD) (φ.integrable_bilin B hL)
    (fun x _ => φ.contDiff.differentiable (by simp) x)
    (fun x hx => (hg.contDiffAt (U.isOpen.mem_nhds (φ.tsupport_subset hx))).differentiableAt (by simp))
  simp only [directionalDerivative, Distribution.lineDerivCLM_apply, complexRegularDistribution_apply]
  change (∫ x, φ x • rd v g x ∂μ) = - ∫ x, fderiv ℝ φ x v • g x ∂μ at hibp
  simp_rw [← hψ] at hibp
  exact hibp.symm

private theorem complexRegularDistribution_smul_sub {g h : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (a b : ℂ) :
    a • (complexRegularDistribution μ g (locallyIntegrableOn_of_contDiffOn hg) -
        b • complexRegularDistribution μ h (locallyIntegrableOn_of_contDiffOn hh)) =
      complexRegularDistribution μ (fun x => a * (g x - b * h x))
        (locallyIntegrableOn_of_contDiffOn (contDiffOn_const.mul (hg.sub (contDiffOn_const.mul hh)))) := by
  ext φ
  let B : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hg' : Integrable (fun x => φ x • g x) μ :=
    φ.integrable_bilin B (locallyIntegrableOn_of_contDiffOn hg)
  have hh' : Integrable (fun x => φ x • h x) μ :=
    φ.integrable_bilin B (locallyIntegrableOn_of_contDiffOn hh)
  simp only [complexRegularDistribution_apply, smul_apply, sub_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_sub hg' (hh'.const_mul b), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Complex.real_smul]
  ring

theorem wirtingerDerivative_complexRegularDistribution {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (a b : E) :
    wirtingerDerivative a b (complexRegularDistribution μ g (locallyIntegrableOn_of_contDiffOn hg)) =
      complexRegularDistribution μ (dz a b g)
        (locallyIntegrableOn_of_contDiffOn (smoothOn_dz U.isOpen hg a b)) := by
  simp only [wirtingerDerivative, smul_apply, sub_apply]
  rw [directionalDerivative_complexRegularDistribution hg a,
    directionalDerivative_complexRegularDistribution hg b,
    complexRegularDistribution_smul_sub (smoothOn_rd U.isOpen hg a)
      (smoothOn_rd U.isOpen hg b)]
  congr 1
  funext x
  simp only [dz, one_div]

theorem complexRegularDistribution_const_mul {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (c : ℂ) :
    complexRegularDistribution μ (fun x => c * g x)
        (locallyIntegrableOn_of_contDiffOn (contDiffOn_const.mul hg)) =
      c • complexRegularDistribution μ g (locallyIntegrableOn_of_contDiffOn hg) := by
  ext φ
  rw [smul_apply, complexRegularDistribution_apply, complexRegularDistribution_apply,
    smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Complex.real_smul]
  ring

theorem complexRegularDistribution_sum {ι : Type*} {s : Finset ι} {g : ι → E → ℂ}
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) U) :
    complexRegularDistribution μ (fun x => ∑ i ∈ s, g i x)
        (locallyIntegrableOn_of_contDiffOn (ContDiffOn.sum (fun i _ => hg i))) =
      ∑ i ∈ s, complexRegularDistribution μ (g i) (locallyIntegrableOn_of_contDiffOn (hg i)) := by
  ext φ
  have hI (i : ι) : Integrable (fun x => φ x • g i x) μ :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_of_contDiffOn (hg i))
  rw [complexRegularDistribution_apply]
  simp only [Finset.smul_sum]
  rw [integral_finsetSum s (fun i _ => hI i)]
  let e : 𝓓'(U, ℂ) →+ ℂ :=
    { toFun := fun T => T φ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change _ = e (∑ i ∈ s, complexRegularDistribution μ (g i) (locallyIntegrableOn_of_contDiffOn (hg i)))
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (complexRegularDistribution_apply μ (g i) _ φ).symm

/-- Equality of the regular distributions identifies continuous densities
on the open domain. -/
theorem eqOn_of_complexRegularDistribution_eq {g h : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (heq : complexRegularDistribution μ g (locallyIntegrableOn_of_contDiffOn hg) =
      complexRegularDistribution μ h (locallyIntegrableOn_of_contDiffOn hh)) :
    EqOn g h U := by
  have haz : ∀ᵐ x ∂μ, x ∈ U → g x - h x = 0 := by
    apply U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (locallyIntegrableOn_of_contDiffOn (hg.sub hh))
    intro f hfs hfc hfU
    let φ : 𝓓(U, ℝ) := ⟨f, hfs, hfc, hfU⟩
    have hI₁ : Integrable (fun x => f x • g x) μ :=
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_of_contDiffOn hg)
    have hI₂ : Integrable (fun x => f x • h x) μ :=
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_of_contDiffOn hh)
    have hφ := congrArg (fun T : 𝓓'(U, ℂ) => T φ) heq
    rw [complexRegularDistribution_apply, complexRegularDistribution_apply] at hφ
    simp_rw [smul_sub]
    rw [integral_sub hI₁ hI₂]
    exact sub_eq_zero.mpr hφ
  have hae : g =ᵐ[μ.restrict U] h :=
    (ae_restrict_iff' U.isOpen.measurableSet).2 (haz.mono fun _ hx hy => sub_eq_zero.mp (hx hy))
  exact Measure.eqOn_open_of_ae_eq hae U.isOpen hg.continuousOn hh.continuousOn

end KEBall.BedfordTaylor
