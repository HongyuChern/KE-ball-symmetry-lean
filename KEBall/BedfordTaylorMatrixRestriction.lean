import KEBall.BedfordTaylorMatrixExteriorDerivative
import KEBall.BedfordTaylorMixedLocality
import KEBall.BedfordTaylorPositiveMatrixDistribution

/-!
# Restriction of positive coefficient matrices
-/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace Topology
open scoped ContDiff Distributions

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn coordinateVector)

variable {n k l : ℕ} {U V : Opens (ComplexModel n)}

/-- Restriction to an open subdomain by extension of test functions. -/
noncomputable def restrictCoefficient {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : 𝓓'(U, F)) : 𝓓'(V, F) :=
  T.comp (TestFunction.monoCLM ℝ)

theorem restrictCoefficient_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hVU : V ≤ U) (T : 𝓓'(U, F)) (φ : 𝓓(V, ℝ)) :
    restrictCoefficient T φ = T (extendTest hVU φ) := by
  change T (TestFunction.monoCLM ℝ φ) = _
  congr 1
  apply TestFunction.ext
  intro x
  rw [TestFunction.monoCLM_apply, if_pos ⟨le_rfl, hVU⟩, extendTest_apply]

/-- Restrict each coefficient to the open subdomain. -/
noncomputable def restrictCoordinateMatrix (T : CoordinateDistributions U k l) :
    CoordinateDistributions V k l :=
  Matrix.of fun I J => restrictCoefficient (T I J)

theorem restrictCoordinateMatrix_apply (hVU : V ≤ U) (T : CoordinateDistributions U k l)
    (I : CoordinateTuple n k) (J : CoordinateTuple n l) (φ : 𝓓(V, ℝ)) :
    restrictCoordinateMatrix T I J φ = T I J (extendTest hVU φ) :=
  restrictCoefficient_apply hVU (T I J) φ

private theorem inclusionOpenEmbedding (hVU : V ≤ U) :
    IsOpenEmbedding (Set.inclusion hVU) :=
  .inclusion hVU (V.isOpen.preimage continuous_subtype_val)

private theorem integral_comap_inclusion_of_zero (hVU : V ≤ U) (μ : Measure U)
    (f : ComplexModel n → ℝ) (hf : ∀ x ∈ U, x ∉ V → f x = 0) :
    ∫ x : V, f x ∂(μ.comap (Set.inclusion hVU)) = ∫ x : U, f x ∂μ := by
  have he := (inclusionOpenEmbedding hVU).measurableEmbedding
  calc
    _ = ∫ x : U, f x ∂((μ.comap (Set.inclusion hVU)).map (Set.inclusion hVU)) :=
      (he.integral_map (fun x : U => f x)).symm
    _ = _ := by
      rw [he.map_comap]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact hf x x.property (fun hxV => hx ⟨⟨x, hxV⟩, Subtype.ext rfl⟩)

theorem weightMeasureDifference_restrictCoefficient {u : ComplexModel n → ℝ}
    (hVU : V ≤ U) (hu : IsLocallyBoundedPshOn U u)
    {T : 𝓓'(U, ℝ)} (hT : IsMeasureDifference T)
    (hTV : IsMeasureDifference (restrictCoefficient T : 𝓓'(V, ℝ))) (φ : 𝓓(V, ℝ)) :
    weightMeasureDifference (IsLocallyBoundedPshOn.mono hu hVU) hTV φ =
      weightMeasureDifference hu hT (extendTest hVU φ) := by
  let μ := hT.choose
  let ν := hT.choose_spec.choose
  let : μ.Regular := hT.choose_spec.choose_spec.1
  let : ν.Regular := hT.choose_spec.choose_spec.2.1
  let μV := μ.comap (Set.inclusion hVU)
  let νV := ν.comap (Set.inclusion hVU)
  let : μV.Regular := Measure.Regular.comap' μ (inclusionOpenEmbedding hVU)
  let : νV.Regular := Measure.Regular.comap' ν (inclusionOpenEmbedding hVU)
  have hpair (ψ : 𝓓(U, ℝ)) : T ψ = (∫ x : U, ψ x ∂μ) - ∫ x : U, ψ x ∂ν :=
    hT.choose_spec.choose_spec.2.2 ψ
  have hzero (ψ : 𝓓(V, ℝ)) (x : ComplexModel n) (hx : x ∉ V) : ψ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (ψ.tsupport_subset hs))
  have hpairV (ψ : 𝓓(V, ℝ)) : restrictCoefficient T ψ =
      (∫ x : V, ψ x ∂μV) - ∫ x : V, ψ x ∂νV := by
    rw [restrictCoefficient_apply hVU, hpair,
      integral_comap_inclusion_of_zero hVU μ ψ (fun x _ hx => hzero ψ x hx),
      integral_comap_inclusion_of_zero hVU ν ψ (fun x _ hx => hzero ψ x hx)]
    rfl
  have hzeroMul (x : ComplexModel n) (_ : x ∈ U) (hx : x ∉ V) : φ x * u x = 0 := by
    rw [hzero φ x hx, zero_mul]
  rw [weightMeasureDifference_apply _ hTV hpairV, weightMeasureDifference_apply _ hT hpair,
    integral_comap_inclusion_of_zero hVU μ _ hzeroMul,
    integral_comap_inclusion_of_zero hVU ν _ hzeroMul]
  rfl

theorem restrictCoordinateMatrix_isPositive (hVU : V ≤ U)
    {T : CoordinateDistributions U k k} (hT : IsPositiveMatrixDistribution T) :
    IsPositiveMatrixDistribution (restrictCoordinateMatrix T : CoordinateDistributions V k k) := by
  constructor
  · intro φ
    simpa only [restrictCoordinateMatrix_apply hVU] using hT.1 (extendTest hVU φ)
  · intro φ hφ
    simpa only [restrictCoordinateMatrix_apply hVU] using hT.2 (extendTest hVU φ) hφ

theorem quadraticMeasure_restrict (hVU : V ≤ U) {T : CoordinateDistributions U k k}
    (hT : IsPositiveMatrixDistribution T) (v : CoordinateTuple n k → ℂ) :
    quadraticMeasure (restrictCoordinateMatrix_isPositive hVU hT) v =
      (quadraticMeasure hT v).comap (Set.inclusion hVU) := by
  let μ := quadraticMeasure hT v
  let : μ.Regular := quadraticMeasure_regular hT v
  let : (μ.comap (Set.inclusion hVU)).Regular :=
    Measure.Regular.comap' μ (inclusionOpenEmbedding hVU)
  let : (quadraticMeasure (restrictCoordinateMatrix_isPositive hVU hT) v).Regular :=
    quadraticMeasure_regular (restrictCoordinateMatrix_isPositive hVU hT) v
  apply measure_eq_of_smooth_test
  intro φ
  have hφ (x : ComplexModel n) (_ : x ∈ U) (hx : x ∉ V) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hz => hx (φ.tsupport_subset hz))
  rw [integral_quadraticMeasure, integral_comap_inclusion_of_zero hVU μ φ hφ]
  change (quadraticDistribution _ v φ).re = ∫ x : U, extendTest hVU φ x ∂quadraticMeasure hT v
  rw [integral_quadraticMeasure]
  simp only [quadraticDistribution_apply, restrictCoordinateMatrix_apply hVU]

theorem integral_weightedQuadraticMeasure_restrict (hVU : V ≤ U)
    {u : ComplexModel n → ℝ} {T : CoordinateDistributions U k k}
    (hT : IsPositiveMatrixDistribution T) (v : CoordinateTuple n k → ℂ) (φ : 𝓓(V, ℝ)) :
    (∫ x : V, φ x * u x ∂quadraticMeasure (restrictCoordinateMatrix_isPositive hVU hT) v) =
      ∫ x : U, extendTest hVU φ x * u x ∂quadraticMeasure hT v := by
  rw [quadraticMeasure_restrict hVU hT v]
  apply integral_comap_inclusion_of_zero hVU _ (fun x => φ x * u x)
  intro x _ hx
  rw [image_eq_zero_of_notMem_tsupport (fun hz => hx (φ.tsupport_subset hz)), zero_mul]

theorem weightPositiveMatrixDistribution_restrict (hVU : V ≤ U)
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn U u)
    {T : CoordinateDistributions U k k} (hT : IsPositiveMatrixDistribution T) :
    weightPositiveMatrixDistribution (IsLocallyBoundedPshOn.mono hu hVU) (restrictCoordinateMatrix_isPositive hVU hT) =
      (restrictCoordinateMatrix (weightPositiveMatrixDistribution hu hT) :
        CoordinateDistributions V k k) := by
  ext I J φ
  rw [restrictCoordinateMatrix_apply hVU]
  simp only [weightPositiveMatrixDistribution, Matrix.of_apply, add_apply, smul_apply,
    Distribution.mapCLM_apply, Complex.ofRealCLM_apply]
  have hmap (A : ℂ →L[ℝ] ℝ) :
      Distribution.mapCLM A (restrictCoordinateMatrix T I J : 𝓓'(V, ℂ)) =
        restrictCoefficient (Distribution.mapCLM A (T I J)) := by
    ext ψ
    simp only [Distribution.mapCLM_apply, restrictCoordinateMatrix_apply hVU,
      restrictCoefficient_apply hVU]
  have hRe := weightMeasureDifference_restrictCoefficient hVU hu
    (matrixDistribution_realEntry_isMeasureDifference hT I J)
    (by
      rw [← hmap Complex.reCLM]
      exact matrixDistribution_realEntry_isMeasureDifference
        (restrictCoordinateMatrix_isPositive hVU hT) I J) φ
  have hIm := weightMeasureDifference_restrictCoefficient hVU hu
    (matrixDistribution_imagEntry_isMeasureDifference hT I J)
    (by
      rw [← hmap Complex.imCLM]
      exact matrixDistribution_imagEntry_isMeasureDifference
        (restrictCoordinateMatrix_isPositive hVU hT) I J) φ
  simp only [← hmap] at hRe hIm
  rw [hRe, hIm]

private theorem alternatingDerivative_extendTest {α : Type*} (hVU : V ≤ U)
    (a b : α → ComplexModel n) (S : (Fin k → α) → 𝓓'(U, ℂ))
    (T : (Fin k → α) → 𝓓'(V, ℂ)) (h : ∀ I φ, S I (extendTest hVU φ) = T I φ)
    (I : Fin (k + 1) → α) (φ : 𝓓(V, ℝ)) :
    alternatingDerivative (fun i => wirtingerDerivative (a i) (b i)) S I (extendTest hVU φ) =
      alternatingDerivative (fun i => wirtingerDerivative (a i) (b i)) T I φ := by
  let evalU : 𝓓'(U, ℂ) →+ ℂ :=
    { toFun := fun R => R (extendTest hVU φ), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let evalV : 𝓓'(V, ℂ) →+ ℂ :=
    { toFun := fun R => R φ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change evalU (alternatingDerivative _ S I) = evalV (alternatingDerivative _ T I)
  simp only [alternatingDerivative, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
    (wirtingerDerivative_extendTest hVU (h (i.removeNth I)) (a (I i)) (b (I i)) φ)

theorem coordinateRowDerivative_restrict (hVU : V ≤ U) (T : CoordinateDistributions U k l) :
    coordinateRowDerivative (restrictCoordinateMatrix T : CoordinateDistributions V k l) =
      restrictCoordinateMatrix (coordinateRowDerivative T) := by
  ext I J φ
  rw [restrictCoordinateMatrix_apply hVU]
  exact (alternatingDerivative_extendTest hVU coordinateVector (fun i => Complex.I • coordinateVector i)
    (fun I' => T I' J) (fun I' => restrictCoordinateMatrix T I' J)
    (fun I' ψ => (restrictCoordinateMatrix_apply hVU T I' J ψ).symm) I φ).symm

theorem coordinateColumnDerivative_restrict (hVU : V ≤ U) (T : CoordinateDistributions U k l) :
    coordinateColumnDerivative (restrictCoordinateMatrix T : CoordinateDistributions V k l) =
      restrictCoordinateMatrix (coordinateColumnDerivative T) := by
  ext I J φ
  rw [restrictCoordinateMatrix_apply hVU]
  exact (alternatingDerivative_extendTest hVU coordinateVector (fun j => -(Complex.I • coordinateVector j))
    (T I) (fun J' => restrictCoordinateMatrix T I J')
    (fun J' ψ => (restrictCoordinateMatrix_apply hVU T I J' ψ).symm) J φ).symm

end KEBall.BedfordTaylor
