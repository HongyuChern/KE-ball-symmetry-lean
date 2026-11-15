import KEBall.BedfordTaylorMatrixExteriorDerivative
import KEBall.BedfordTaylorPositiveMatrixDistribution
import KEBall.BedfordTaylorSmoothCoefficients

/-!
# Smooth densities of coordinate matrices of distributions
-/

set_option autoImplicit false

open Filter Matrix MeasureTheory Set TopologicalSpace
open scoped ComplexOrder ContDiff Distributions

namespace KEBall.BedfordTaylor

open KEBallProbe
open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector IsSmoothPshOn IsLocallyBoundedPshOn)

variable {n k l : ℕ} {Ω : Opens (ComplexModel n)}

abbrev CoordinateDensities (n k l : ℕ) :=
  Matrix (CoordinateTuple n k) (CoordinateTuple n l) (ComplexModel n → ℂ)

/-- The regular distributions of smooth coefficient densities. -/
noncomputable def matrixOfDensities (g : CoordinateDensities n k l)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) : CoordinateDistributions Ω k l :=
  Matrix.of fun I J => complexRegularDistribution volume (g I J)
    (locallyIntegrableOn_of_contDiffOn (hg I J))

private theorem alternatingDensity_smooth {α : Type*}
    (a b : α → ComplexModel n) (v : Fin (k + 1) → α)
    (g : (Fin k → α) → ComplexModel n → ℂ) (hg : ∀ I, ContDiffOn ℝ ∞ (g I) Ω) :
    ContDiffOn ℝ ∞ (fun x => ∑ i : Fin (k + 1),
      (-1 : ℂ) ^ (i : ℕ) * dz (a (v i)) (b (v i)) (g (i.removeNth v)) x) Ω :=
  ContDiffOn.sum fun _ _ =>
    contDiffOn_const.mul (smoothOn_dz Ω.isOpen (hg _) _ _)

private theorem alternatingDerivative_of_density {α : Type*}
    (a b : α → ComplexModel n) (v : Fin (k + 1) → α)
    (g : (Fin k → α) → ComplexModel n → ℂ) (hg : ∀ I, ContDiffOn ℝ ∞ (g I) Ω) :
    alternatingDerivative (fun i => wirtingerDerivative (a i) (b i))
      (fun I => complexRegularDistribution volume (g I) (locallyIntegrableOn_of_contDiffOn (hg I))) v =
      complexRegularDistribution volume
        (fun x => ∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) *
          dz (a (v i)) (b (v i)) (g (i.removeNth v)) x)
        (locallyIntegrableOn_of_contDiffOn (alternatingDensity_smooth a b v g hg)) := by
  rw [alternatingDerivative, complexRegularDistribution_sum
    (fun i => contDiffOn_const.mul (smoothOn_dz Ω.isOpen (hg (i.removeNth v)) (a (v i)) (b (v i))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [wirtingerDerivative_complexRegularDistribution (hg (i.removeNth v)),
    complexRegularDistribution_const_mul (smoothOn_dz Ω.isOpen (hg (i.removeNth v)) _ _),
    ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

/-- The classical row exterior derivative of a coefficient matrix. -/
noncomputable def coordinateRowDensity (g : CoordinateDensities n k l) :
    CoordinateDensities n (k + 1) l :=
  Matrix.of fun I J x => ∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) *
    dz (coordinateVector (I i)) (Complex.I • coordinateVector (I i)) (g (i.removeNth I) J) x

/-- The classical column exterior derivative of a coefficient matrix. -/
noncomputable def coordinateColumnDensity (g : CoordinateDensities n k l) :
    CoordinateDensities n k (l + 1) :=
  Matrix.of fun I J x => ∑ j : Fin (l + 1), (-1 : ℂ) ^ (j : ℕ) *
    dz (coordinateVector (J j)) (-(Complex.I • coordinateVector (J j))) (g I (j.removeNth J)) x

theorem contDiffOn_coordinateRowDensity (g : CoordinateDensities n k l)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (I : CoordinateTuple n (k + 1))
    (J : CoordinateTuple n l) : ContDiffOn ℝ ∞ (coordinateRowDensity g I J) Ω :=
  alternatingDensity_smooth coordinateVector (fun i => Complex.I • coordinateVector i) I
    (fun I' => g I' J) (fun I' => hg I' J)

theorem contDiffOn_coordinateColumnDensity (g : CoordinateDensities n k l)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (I : CoordinateTuple n k)
    (J : CoordinateTuple n (l + 1)) : ContDiffOn ℝ ∞ (coordinateColumnDensity g I J) Ω :=
  alternatingDensity_smooth coordinateVector (fun j => -(Complex.I • coordinateVector j)) J
    (g I) (hg I)

theorem coordinateRowDerivative_of_densities (g : CoordinateDensities n k l)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) :
    coordinateRowDerivative (matrixOfDensities g hg) =
      matrixOfDensities (coordinateRowDensity g) (contDiffOn_coordinateRowDensity g hg) := by
  ext I J : 1
  exact alternatingDerivative_of_density coordinateVector (fun i => Complex.I • coordinateVector i) I
    (fun I' => g I' J) (fun I' => hg I' J)

theorem coordinateColumnDerivative_of_densities (g : CoordinateDensities n k l)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) :
    coordinateColumnDerivative (matrixOfDensities g hg) =
      matrixOfDensities (coordinateColumnDensity g) (contDiffOn_coordinateColumnDensity g hg) := by
  ext I J : 1
  exact alternatingDerivative_of_density coordinateVector (fun j => -(Complex.I • coordinateVector j))
    J (g I) (hg I)

theorem matrixOfDensities_eqOn_of_eq {g h : CoordinateDensities n k l}
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (hh : ∀ I J, ContDiffOn ℝ ∞ (h I J) Ω)
    (heq : matrixOfDensities g hg = matrixOfDensities h hh) :
    ∀ I J, EqOn (g I J) (h I J) Ω :=
  fun I J => eqOn_of_complexRegularDistribution_eq (hg I J) (hh I J)
    (congrArg (fun T : CoordinateDistributions Ω k l => T I J) heq)

theorem matrixOfDensities_zero :
    matrixOfDensities (0 : CoordinateDensities n k l)
      (fun _ _ => (contDiff_zero_fun : ContDiff ℝ ∞ (0 : ComplexModel n → ℂ)).contDiffOn) =
      (0 : CoordinateDistributions Ω k l) := by
  ext I J φ
  simp [matrixOfDensities, complexRegularDistribution_apply]

theorem matrixOfDensities_congr {g h : CoordinateDensities n k l}
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (hh : ∀ I J, ContDiffOn ℝ ∞ (h I J) Ω)
    (heq : ∀ I J, EqOn (g I J) (h I J) Ω) :
    matrixOfDensities g hg = matrixOfDensities h hh := by
  ext I J φ
  simp only [matrixOfDensities, Matrix.of_apply, complexRegularDistribution_apply]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · rw [heq I J hx]
  · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hx (φ.tsupport_subset hz))
    simp only [hzero, zero_smul]

private theorem weightMeasureDifference_apply_of_smooth {u : ComplexModel n → ℝ}
    (hu : IsSmoothPshOn Ω u) {T : 𝓓'(Ω, ℝ)} (hT : IsMeasureDifference T) (φ : 𝓓(Ω, ℝ)) :
    weightMeasureDifference (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hT φ =
      T (multiplySmoothTest φ hu.1) := by
  let μ := hT.choose
  let ν := hT.choose_spec.choose
  let : μ.Regular := hT.choose_spec.choose_spec.1
  let : ν.Regular := hT.choose_spec.choose_spec.2.1
  have hpair (ψ : 𝓓(Ω, ℝ)) : T ψ = (∫ x : Ω, ψ x ∂μ) - ∫ x : Ω, ψ x ∂ν :=
    hT.choose_spec.choose_spec.2.2 ψ
  rw [weightMeasureDifference_apply _ hT hpair, hpair]
  simp only [multiplySmoothTest_apply]

theorem weightPositiveMatrixDistribution_apply_of_smooth {u : ComplexModel n → ℝ}
    (hu : IsSmoothPshOn Ω u) {T : CoordinateDistributions Ω k k}
    (hT : IsPositiveMatrixDistribution T) (I J : CoordinateTuple n k) (φ : 𝓓(Ω, ℝ)) :
    weightPositiveMatrixDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hT I J φ =
      T I J (multiplySmoothTest φ hu.1) := by
  simp only [weightPositiveMatrixDistribution, Matrix.of_apply, _root_.add_apply, _root_.smul_apply,
    Distribution.mapCLM_apply, Complex.ofRealCLM_apply, weightMeasureDifference_apply_of_smooth hu,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im _

theorem weightPositiveMatrixDistribution_of_densities {u : ComplexModel n → ℝ}
    (hu : IsSmoothPshOn Ω u) (g : CoordinateDensities n k k)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω)
    (hPos : IsPositiveMatrixDistribution (matrixOfDensities g hg)) :
    weightPositiveMatrixDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hPos =
      matrixOfDensities (Matrix.of fun I J x => (u x : ℂ) * g I J x)
        (fun I J => (Complex.ofRealCLM.contDiff.comp_contDiffOn hu.1).mul (hg I J)) := by
  ext I J φ
  rw [weightPositiveMatrixDistribution_apply_of_smooth hu]
  simp only [matrixOfDensities, Matrix.of_apply, complexRegularDistribution_apply,
    multiplySmoothTest_apply, Complex.real_smul, Complex.ofReal_mul, mul_assoc]

private theorem quadraticDistribution_matrixOfDensities_apply (g : CoordinateDensities n k k)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω) (v : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) :
    quadraticDistribution (matrixOfDensities g hg) v φ =
      ∫ x, φ x • (star v ⬝ᵥ ((Matrix.of fun I J => g I J x) *ᵥ v)) := by
  let c := fun I J => star (v I) * v J
  let f := fun I J x => c I J * g I J x
  have hf (I J) : ContDiffOn ℝ ∞ (f I J) Ω := contDiffOn_const.mul (hg I J)
  have hi (I J) : Integrable (fun x => φ x • f I J x) volume :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_of_contDiffOn (hf I J))
  let eval : 𝓓'(Ω, ℂ) →+ ℂ :=
    { toFun := fun T => T φ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change eval (∑ I, ∑ J, c I J • matrixOfDensities g hg I J) = _
  simp only [map_sum]
  calc
    _ = ∑ I, ∑ J, ∫ x, φ x • f I J x := by
      refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
      change (c I J • complexRegularDistribution volume (g I J)
        (locallyIntegrableOn_of_contDiffOn (hg I J))) φ = _
      rw [← complexRegularDistribution_const_mul (hg I J), complexRegularDistribution_apply]
    _ = ∫ x, ∑ I, ∑ J, φ x • f I J x := by
      rw [integral_finsetSum Finset.univ (fun I _ => integrable_finsetSum Finset.univ (fun J _ => hi I J))]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [integral_finsetSum Finset.univ (fun J _ => hi I J)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
      simp only [f, c, Complex.real_smul]
      ring

theorem matrixOfDensities_isPositive (g : CoordinateDensities n k k)
    (hg : ∀ I J, ContDiffOn ℝ ∞ (g I J) Ω)
    (hPos : ∀ x ∈ Ω, (Matrix.of fun I J => g I J x).PosSemidef) :
    IsPositiveMatrixDistribution (matrixOfDensities g hg) := by
  have hh (φ : 𝓓(Ω, ℝ)) :
      (Matrix.of fun I J => matrixOfDensities g hg I J φ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro I J
    simp only [Matrix.of_apply, matrixOfDensities, complexRegularDistribution_apply]
    have hI : Integrable (fun x => φ x • g J I x) volume :=
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_of_contDiffOn (hg J I))
    change Complex.conjCLE.toContinuousLinearMap (∫ x, φ x • g J I x) = _
    rw [← Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hI]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω
    · have he : star (g J I x) = g I J x := (hPos x hx).isHermitian.apply I J
      rw [map_smul]
      exact congrArg (φ x • ·) he
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
      simp only [hz, zero_smul, map_zero]
  refine ⟨hh, fun φ hφ => Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hh φ) fun v => ?_⟩
  rw [← quadraticDistribution_apply, quadraticDistribution_matrixOfDensities_apply]
  apply integral_nonneg
  intro x
  by_cases hx : x ∈ Ω
  · exact smul_nonneg (hφ x) ((hPos x hx).dotProduct_mulVec_nonneg v)
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
    simp only [Pi.zero_apply, hz, zero_smul, le_refl]

end KEBall.BedfordTaylor
