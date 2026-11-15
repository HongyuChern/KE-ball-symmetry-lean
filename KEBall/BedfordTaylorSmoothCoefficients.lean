import KEBall.BedfordTaylorLocalLevi
import KEBall.BedfordTaylorPolarization
import KEBall.BedfordTaylorComplexDensity

/-!
# Smooth densities for the weighted complex Hessian
-/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

namespace KEBall.BedfordTaylor

open PshLines KEBallProbe
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsSmoothPshOn IsLocallyBoundedPshOn locallyIntegrableOn_of_plurisubharmonicOn_real)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Opens E}

/-- Multiplication of a real test function by a scalar function smooth on
its domain. The product keeps the original compact support. -/
noncomputable def multiplySmoothTest (φ : 𝓓(U, ℝ)) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) : 𝓓(U, ℝ) := by
  let g : E → ℝ := fun x => φ x * f x
  have hs : tsupport g ⊆ tsupport φ := tsupport_mul_subset_left
  refine ⟨g, ?_, φ.hasCompactSupport.of_isClosed_subset isClosed_closure hs,
    hs.trans φ.tsupport_subset⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact φ.contDiff.contDiffAt.mul (hf.contDiffAt (U.isOpen.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hx' : x ∈ (tsupport φ)ᶜ := fun h => hx (φ.tsupport_subset h)
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx'] with y hy
    change φ y * f y = 0
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

@[simp]
theorem multiplySmoothTest_apply (φ : 𝓓(U, ℝ)) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (x : E) :
    multiplySmoothTest φ hf x = φ x * f x := rfl

variable [NormedSpace ℂ E]

/-- The classical Hessian coefficient evaluated on complex directions. -/
noncomputable def classicalComplexHessianEntry (p : E → ℝ) (v w : E) : E → ℂ :=
  dz v (Complex.I • v) (dz w (-(Complex.I • w)) (fun x => (p x : ℂ)))

theorem contDiffOn_classicalComplexHessianEntry {p : E → ℝ}
    (hp : ContDiffOn ℝ ∞ p U) (v w : E) :
    ContDiffOn ℝ ∞ (classicalComplexHessianEntry p v w) U :=
  smoothOn_dz U.isOpen (smoothOn_dz U.isOpen (Complex.ofRealCLM.contDiff.comp_contDiffOn hp) _ _) _ _

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}

theorem distributionalComplexHessian_eq_density_of_isSmoothPshOn
    (hp : IsSmoothPshOn Ω p) (v w : ComplexModel n) :
    distributionalComplexHessian
        (regularDistribution volume p (locallyIntegrableOn_of_plurisubharmonicOn_real hp.2.1)) v w =
      complexRegularDistribution volume (classicalComplexHessianEntry p v w)
        (locallyIntegrableOn_of_contDiffOn (contDiffOn_classicalComplexHessianEntry hp.1 v w)) := by
  have hpC : ContDiffOn ℝ ∞ (fun x => (p x : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hp.1
  have hc : Distribution.mapCLM Complex.ofRealCLM
        (regularDistribution volume p (locallyIntegrableOn_of_plurisubharmonicOn_real hp.2.1)) =
      complexRegularDistribution volume (fun x => (p x : ℂ))
        (locallyIntegrableOn_of_contDiffOn hpC) := by
    ext φ
    rw [Distribution.mapCLM_apply, regularDistribution_apply, complexRegularDistribution_apply,
      Complex.ofRealCLM_apply, ← integral_complex_ofReal]
    simp only [Complex.ofReal_mul, Complex.real_smul]
  rw [distributionalComplexHessian, hc, wirtingerDerivative_complexRegularDistribution hpC,
    wirtingerDerivative_complexRegularDistribution (smoothOn_dz Ω.isOpen hpC _ _)]
  rfl

/-- With a smooth weight, the measure-based weighting and ordinary
multiplication on the test function give the same distribution. -/
theorem weightedComplexHessian_apply_smoothWeight
    (hu : IsSmoothPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (v w : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    weightedComplexHessian (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hp v w φ =
      distributionalComplexHessian
        (regularDistribution volume p (locallyIntegrableOn_of_plurisubharmonicOn_real hp.1)) v w
        (multiplySmoothTest φ hu.1) := by
  rw [weightedComplexHessian_apply, distributionalComplexHessian_regularDistribution_apply hp]
  simp only [multiplySmoothTest_apply]

theorem weightedComplexHessian_eq_density_of_isSmoothPshOn
    (hu : IsSmoothPshOn Ω u) (hp : IsSmoothPshOn Ω p) (v w : ComplexModel n) :
    weightedComplexHessian (isLocallyBoundedPshOn_of_isSmoothPshOn hu)
        (isLocallyBoundedPshOn_of_isSmoothPshOn hp) v w =
      complexRegularDistribution volume (fun x => (u x : ℂ) * classicalComplexHessianEntry p v w x)
        (locallyIntegrableOn_of_contDiffOn ((Complex.ofRealCLM.contDiff.comp_contDiffOn hu.1).mul
          (contDiffOn_classicalComplexHessianEntry hp.1 v w))) := by
  ext φ
  rw [weightedComplexHessian_apply_smoothWeight hu,
    distributionalComplexHessian_eq_density_of_isSmoothPshOn hp, complexRegularDistribution_apply,
    complexRegularDistribution_apply]
  simp only [multiplySmoothTest_apply, Complex.real_smul, Complex.ofReal_mul, mul_assoc]

end KEBall.BedfordTaylor
