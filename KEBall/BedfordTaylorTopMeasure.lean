import KEBall.BedfordTaylorMixedProduct
import KEBall.BedfordTaylorSmoothCompatibility

/-!
# The Bedford–Taylor measure of a locally bounded PSH potential

The standard top coefficient is a positive Radon measure. The
normalization is the one used by the paper's smooth measure.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ComplexOrder ContDiff Distributions ENNReal

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere hiding complexHessian

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

variable {n k : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

theorem positive_diagonalCoefficient {T : CoordinateDistributions Ω k k}
    (hT : IsPositiveMatrixDistribution T) (I : CoordinateTuple n k) :
    PositiveDistribution (Distribution.mapCLM Complex.reCLM (T I I)) := by
  intro φ hφ
  rw [Distribution.mapCLM_apply, Complex.reCLM_apply]
  have h : 0 ≤ T I I φ := (hT.2 φ hφ).diag_nonneg
  exact (Complex.nonneg_iff.mp h).1

/-- The positive Radon measure of a diagonal coefficient. -/
noncomputable def diagonalMeasure {T : CoordinateDistributions Ω k k}
    (hT : IsPositiveMatrixDistribution T) (I : CoordinateTuple n k) : Measure Ω :=
  (positive_diagonalCoefficient hT I).exists_regular_measure.choose

theorem diagonalMeasure_regular {T : CoordinateDistributions Ω k k}
    (hT : IsPositiveMatrixDistribution T) (I : CoordinateTuple n k) :
    (diagonalMeasure hT I).Regular :=
  (positive_diagonalCoefficient hT I).exists_regular_measure.choose_spec.1

theorem integral_diagonalMeasure {T : CoordinateDistributions Ω k k}
    (hT : IsPositiveMatrixDistribution T) (I : CoordinateTuple n k) (φ : 𝓓(Ω, ℝ)) :
    (∫ x : Ω, φ x ∂diagonalMeasure hT I) = (T I I φ).re :=
  (positive_diagonalCoefficient hT I).exists_regular_measure.choose_spec.2.2 φ

theorem diagonalMeasure_eq_quadraticMeasure {T : CoordinateDistributions Ω k k}
    (hT : IsPositiveMatrixDistribution T) (I : CoordinateTuple n k) :
    diagonalMeasure hT I = quadraticMeasure hT (Pi.single I 1) := by
  let : (diagonalMeasure hT I).Regular := diagonalMeasure_regular hT I
  let : (quadraticMeasure hT (Pi.single I 1)).Regular := quadraticMeasure_regular hT _
  apply measure_eq_of_smooth_test
  intro φ
  rw [integral_diagonalMeasure, integral_quadraticMeasure, quadraticDistribution_apply]
  simp only [Pi.star_single, star_one, Matrix.mulVec_single_one, single_dotProduct,
    one_mul, Matrix.col_apply, Matrix.of_apply]

/-- The normalized top-degree Bedford–Taylor measure, extended by zero
off the open domain. -/
noncomputable def topMeasure (hu : IsLocallyBoundedPshOn Ω u) :
    Measure (ComplexModel n) :=
  ENNReal.ofReal ((Real.pi ^ n)⁻¹) •
    (diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => hu)) id).map Subtype.val

theorem topMeasure_compl (hu : IsLocallyBoundedPshOn Ω u) :
    topMeasure hu (Ω : Set (ComplexModel n))ᶜ = 0 := by
  rw [topMeasure, Measure.smul_apply,
    Measure.map_apply measurable_subtype_coe Ω.isOpen.measurableSet.compl]
  have hempty : (Subtype.val : Ω → ComplexModel n) ⁻¹' (Ω : Set (ComplexModel n))ᶜ = ∅ := by
    ext z
    exact iff_false_intro (fun h => h z.property)
  rw [hempty, measure_empty, smul_eq_mul, mul_zero]

theorem topMeasure_finite_on_compact (hu : IsLocallyBoundedPshOn Ω u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    topMeasure hu K < ⊤ := by
  let ρ := diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => hu)) id
  let : ρ.Regular := diagonalMeasure_regular _ _
  have hc : IsCompact ((Subtype.val : Ω → ComplexModel n) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
      (fun z hz => ⟨⟨z, hKΩ hz⟩, rfl⟩)
  rw [topMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_subtype_coe hK.measurableSet]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hc.measure_lt_top (μ := ρ))

theorem integral_topMeasure_map (hu : IsLocallyBoundedPshOn Ω u) (f : ComplexModel n → ℝ) :
    (∫ x, f x ∂topMeasure hu) = (Real.pi ^ n)⁻¹ *
      ∫ x : Ω, f x ∂diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => hu)) id := by
  rw [topMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  exact (MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet).integral_map
    (μ := diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => hu)) id) f

theorem integral_topMeasure (hu : IsLocallyBoundedPshOn Ω u) (φ : 𝓓(Ω, ℝ)) :
    (∫ x, φ x ∂topMeasure hu) = (Real.pi ^ n)⁻¹ *
      (mixedProduct (k := n) (u := fun _ => u) (fun _ => hu) id id φ).re := by
  rw [integral_topMeasure_map, integral_diagonalMeasure]

theorem topMeasure_restrict (hu : IsLocallyBoundedPshOn Ω u)
    {V : Opens (ComplexModel n)} (hVΩ : V ≤ Ω) :
    (topMeasure hu).restrict (V : Set (ComplexModel n)) =
      topMeasure (IsLocallyBoundedPshOn.mono hu hVΩ) := by
  apply ambientMeasure_eq_of_smooth_test (U := V)
  · rw [Measure.restrict_apply V.isOpen.measurableSet.compl, compl_inter_self, measure_empty]
  · exact topMeasure_compl _
  · intro K hK hKV
    exact (Measure.restrict_le_self K).trans_lt (topMeasure_finite_on_compact hu hK (hKV.trans hVΩ))
  · intro K hK hKV
    exact topMeasure_finite_on_compact _ hK hKV
  · intro φ
    rw [← integral_indicator V.isOpen.measurableSet,
      indicator_eq_self.mpr ((subset_tsupport φ).trans φ.tsupport_subset)]
    change (∫ x, extendTest hVΩ φ x ∂topMeasure hu) = _
    rw [integral_topMeasure, integral_topMeasure,
      mixedProduct_restrict (u := fun _ => u) hVΩ (fun _ => hu), restrictCoordinateMatrix_apply hVΩ]

theorem topMeasure_congr {p : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p) (he : EqOn u p Ω) :
    topMeasure hu = topMeasure hp := by
  apply ambientMeasure_eq_of_smooth_test (topMeasure_compl hu) (topMeasure_compl hp)
    (fun _ => topMeasure_finite_on_compact hu) (fun _ => topMeasure_finite_on_compact hp)
  intro φ
  rw [integral_topMeasure, integral_topMeasure,
    mixedProduct_congr (u := fun _ => u) (w := fun _ => p) (fun _ => hu) (fun _ => hp) (fun _ => he)]

private theorem smoothMixedDensities_top_eq {x : ComplexModel n} (hu : ContDiffAt ℝ ∞ u x) :
    smoothMixedDensities n n (fun _ => u) id id x = (n.factorial : ℂ) * (modelHessian u x).det := by
  rw [smoothMixedDensities_eq_mixedMinor, mixedMinorMatrix_const]
  have hH : (Matrix.of fun i j =>
      classicalComplexHessianEntry u (coordinateVector i) (coordinateVector j) x) =
      modelHessian u x := by
    ext i j : 1
    exact classicalComplexHessianEntry_coordinate_eq hu i j
  rw [hH]
  rfl

theorem topMeasure_eq_smoothMeasure (hu : IsSmoothPshOn Ω u) :
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) = smoothMeasure Ω u hu := by
  apply ambientMeasure_eq_of_smooth_test (topMeasure_compl _) (smoothMeasure_compl hu)
    (fun _ => topMeasure_finite_on_compact _) (smoothMeasure_finite_on_compact hu)
  intro φ
  let g := smoothMixedDensities n n (fun _ => u)
  have hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω :=
    contDiffOn_smoothMixedDensities (fun _ => u) (fun _ => hu.1)
  have hI : Integrable (fun x => φ x • g id id x) :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_of_contDiffOn (hg id id))
  rw [integral_topMeasure, mixedProduct_eq_smooth (u := fun _ => u) (fun _ => hu)]
  simp only [matrixOfDensities, Matrix.of_apply, complexRegularDistribution_apply]
  change (Real.pi ^ n)⁻¹ * Complex.reCLM (∫ x, φ x • g id id x) = _
  rw [← Complex.reCLM.integral_comp_comm hI, ← integral_const_mul, smoothMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      ((continuousOn_smoothDensity hu.1).aemeasurable Ω.isOpen.measurableSet).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ,
    ← integral_indicator Ω.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · rw [indicator_of_mem hx, smoothMeasure_weight_toReal Ω u hu hx]
    change (Real.pi ^ n)⁻¹ * (φ x • g id id x).re = smoothDensity u x • φ x
    rw [show g id id x = (n.factorial : ℂ) * (modelHessian u x).det from
      smoothMixedDensities_top_eq (hu.1.contDiffAt (Ω.isOpen.mem_nhds hx))]
    simp [Complex.real_smul, Complex.mul_re, smoothDensity, div_eq_mul_inv]
    ring
  · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
    simp [hzero, hx]

theorem topMeasure_eq_map_d0TopMeasure_unitBall {q : E n → ℝ}
    (hq : IsSmoothPshOn (complexUnitBall n) (q ∘ (complexCoordinates n).symm)) :
    topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hq) =
      Measure.map (complexCoordinates n) ((d0TopMeasure q).restrict (unitBall n)) := by
  rw [topMeasure_eq_smoothMeasure hq]
  simpa only [preimage_complexUnitBall] using
    (map_d0TopMeasure_restrict_eq_smoothMeasure (complexUnitBall n) hq).symm

#print axioms topMeasure_eq_map_d0TopMeasure_unitBall

end KEBall.BedfordTaylor
