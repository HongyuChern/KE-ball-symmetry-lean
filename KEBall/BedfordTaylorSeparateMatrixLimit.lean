import KEBall.BedfordTaylorMixedConvergence
import KEBall.BedfordTaylorSmoothMatrixProduct

/-!
# Separate weak continuity of the product step
-/

set_option autoImplicit false

open Filter MeasureTheory TopologicalSpace
open scoped ComplexOrder Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n k l : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
  {q : ℕ → ComplexModel n → ℝ}

/-- Weak convergence on smooth compactly supported tests for all
matrix coefficients. -/
def WeakMatrixLimit (T : ℕ → CoordinateDistributions Ω k l) (S : CoordinateDistributions Ω k l) :
    Prop :=
  ∀ I J (φ : 𝓓(Ω, ℝ)), Tendsto (fun j => T j I J φ) atTop (𝓝 (S I J φ))

private theorem tendsto_alternatingDerivative_test {α : Type*}
    (a b : α → ComplexModel n) {S : ℕ → (Fin k → α) → 𝓓'(Ω, ℂ)}
    {T : (Fin k → α) → 𝓓'(Ω, ℂ)}
    (h : ∀ I (φ : 𝓓(Ω, ℝ)), Tendsto (fun j => S j I φ) atTop (𝓝 (T I φ)))
    (I : Fin (k + 1) → α) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => alternatingDerivative (fun i => wirtingerDerivative (a i) (b i)) (S j) I φ)
      atTop (𝓝 (alternatingDerivative (fun i => wirtingerDerivative (a i) (b i)) T I φ)) := by
  let eval : 𝓓'(Ω, ℂ) →+ ℂ :=
    { toFun := fun R => R φ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change Tendsto (fun j => eval (alternatingDerivative _ (S j) I))
    atTop (𝓝 (eval (alternatingDerivative _ T I)))
  simp only [alternatingDerivative, map_sum, map_zsmul]
  apply tendsto_finsetSum
  intro i _
  exact (tendsto_wirtingerDerivative_test (h (i.removeNth I)) (a (I i)) (b (I i)) φ).const_smul
    ((-1 : ℤ) ^ (i : ℕ))

theorem WeakMatrixLimit.rowDerivative {T : ℕ → CoordinateDistributions Ω k l}
    {S : CoordinateDistributions Ω k l} (h : WeakMatrixLimit T S) :
    WeakMatrixLimit (fun j => coordinateRowDerivative (T j)) (coordinateRowDerivative S) :=
  fun I J φ => tendsto_alternatingDerivative_test coordinateVector
    (fun i => Complex.I • coordinateVector i) (fun I' => h I' J) I φ

theorem WeakMatrixLimit.columnDerivative {T : ℕ → CoordinateDistributions Ω k l}
    {S : CoordinateDistributions Ω k l} (h : WeakMatrixLimit T S) :
    WeakMatrixLimit (fun j => coordinateColumnDerivative (T j)) (coordinateColumnDerivative S) :=
  fun I J φ => tendsto_alternatingDerivative_test coordinateVector
    (fun j => -(Complex.I • coordinateVector j)) (h I) J φ

theorem WeakMatrixLimit.hermitian {T : ℕ → CoordinateDistributions Ω k k}
    {S : CoordinateDistributions Ω k k} (h : WeakMatrixLimit T S) (φ : 𝓓(Ω, ℝ))
    (hT : ∀ j, (Matrix.of fun I J => T j I J φ).IsHermitian) :
    (Matrix.of fun I J => S I J φ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro I J
  change star (S J I φ) = S I J φ
  apply tendsto_nhds_unique ((continuous_star.tendsto _).comp (h J I φ))
  apply (h I J φ).congr
  intro j
  exact ((hT j).apply I J).symm

theorem WeakMatrixLimit.quadratic {T : ℕ → CoordinateDistributions Ω k k}
    {S : CoordinateDistributions Ω k k} (h : WeakMatrixLimit T S)
    (v : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => quadraticDistribution (T j) v φ) atTop
      (𝓝 (quadraticDistribution S v φ)) := by
  simp only [quadraticDistribution_apply, dotProduct, Matrix.mulVec, Matrix.of_apply]
  exact tendsto_finsetSum _ fun I _ => tendsto_const_nhds.mul
    (tendsto_finsetSum _ fun J _ => (h I J φ).mul_const (v J))

theorem WeakMatrixLimit.posSemidef {T : ℕ → CoordinateDistributions Ω k k}
    {S : CoordinateDistributions Ω k k} (h : WeakMatrixLimit T S) (φ : 𝓓(Ω, ℝ))
    (hT : ∀ j, (Matrix.of fun I J => T j I J φ).PosSemidef) :
    (Matrix.of fun I J => S I J φ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (h.hermitian φ fun j => (hT j).isHermitian)
  intro v
  have hlim := h.quadratic v φ
  rw [← quadraticDistribution_apply, Complex.nonneg_iff]
  have hnonneg (j : ℕ) : 0 ≤ quadraticDistribution (T j) v φ := by
    rw [quadraticDistribution_apply]
    exact (hT j).dotProduct_mulVec_nonneg v
  refine ⟨ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
    (Eventually.of_forall fun j => (Complex.nonneg_iff.mp (hnonneg j)).1), ?_⟩
  symm
  apply tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hlim)
  exact tendsto_const_nhds.congr fun j => (Complex.nonneg_iff.mp (hnonneg j)).2

private theorem tendsto_weightMeasureDifference_test (hu : IsLocallyBoundedPshOn Ω u)
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    {T : 𝓓'(Ω, ℝ)} (hT : IsMeasureDifference T) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => weightMeasureDifference (hq j) hT φ) atTop
      (𝓝 (weightMeasureDifference hu hT φ)) := by
  let μ := hT.choose
  let ν := hT.choose_spec.choose
  let : μ.Regular := hT.choose_spec.choose_spec.1
  let : ν.Regular := hT.choose_spec.choose_spec.2.1
  have hpair (ψ : 𝓓(Ω, ℝ)) : T ψ = (∫ x : Ω, ψ x ∂μ) - ∫ x : Ω, ψ x ∂ν :=
    hT.choose_spec.choose_spec.2.2 ψ
  simp_rw [weightMeasureDifference_apply _ hT hpair]
  exact (tendsto_integral_psh_weight_of_antitone hu hq hanti hlim μ φ).sub
    (tendsto_integral_psh_weight_of_antitone hu hq hanti hlim ν φ)

theorem weakMatrixLimit_weight (hu : IsLocallyBoundedPshOn Ω u)
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    {T : CoordinateDistributions Ω k k} (hT : IsPositiveMatrixDistribution T) :
    WeakMatrixLimit (fun j => weightPositiveMatrixDistribution (hq j) hT)
      (weightPositiveMatrixDistribution hu hT) := by
  intro I J φ
  simp only [weightPositiveMatrixDistribution, Matrix.of_apply, add_apply, smul_apply,
    Distribution.mapCLM_apply, Complex.ofRealCLM_apply]
  have hRe := tendsto_weightMeasureDifference_test hu hq hanti hlim
    (matrixDistribution_realEntry_isMeasureDifference hT I J) φ
  have hIm := tendsto_weightMeasureDifference_test hu hq hanti hlim
    (matrixDistribution_imagEntry_isMeasureDifference hT I J) φ
  exact ((Complex.continuous_ofReal.tendsto _).comp hRe).add
    (((Complex.continuous_ofReal.tendsto _).comp hIm).const_smul Complex.I)

theorem WeakMatrixLimit.weightSmooth {T : ℕ → CoordinateDistributions Ω k k}
    {S : CoordinateDistributions Ω k k} (h : WeakMatrixLimit T S) (hu : IsSmoothPshOn Ω u)
    (hT : ∀ j, IsPositiveMatrixDistribution (T j)) (hS : IsPositiveMatrixDistribution S) :
    WeakMatrixLimit (fun j =>
      weightPositiveMatrixDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn hu) (hT j))
      (weightPositiveMatrixDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn hu) hS) := by
  intro I J φ
  simp_rw [weightPositiveMatrixDistribution_apply_of_smooth hu]
  exact h I J (multiplySmoothTest φ hu.1)

end KEBall.BedfordTaylor
