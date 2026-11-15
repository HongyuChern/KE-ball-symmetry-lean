import KEBall.BedfordTaylorMeasureDifference
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive matrices of distributions

Testing on a nonnegative function gives a positive semidefinite matrix.
Every quadratic contraction therefore defines a positive Radon measure.
Polarization recovers all the complex coefficient distributions.
-/

set_option autoImplicit false

open Matrix MeasureTheory Set TopologicalSpace
open scoped ComplexOrder Distributions ENNReal

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {ι : Type*} [Fintype ι]

/-- A positive Hermitian matrix of distributions on an open domain. -/
def IsPositiveMatrixDistribution (T : Matrix ι ι 𝓓'(Ω, ℂ)) : Prop :=
  (∀ φ : 𝓓(Ω, ℝ), (Matrix.of fun i j => T i j φ).IsHermitian) ∧
    ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → (Matrix.of fun i j => T i j φ).PosSemidef

/-- The distribution obtained by taking a constant-vector quadratic
contraction of the coefficient matrix. -/
noncomputable def quadraticDistribution (T : Matrix ι ι 𝓓'(Ω, ℂ)) (v : ι → ℂ) : 𝓓'(Ω, ℂ) :=
  ∑ i, ∑ j, (star (v i) * v j) • T i j

theorem quadraticDistribution_apply (T : Matrix ι ι 𝓓'(Ω, ℂ)) (v : ι → ℂ) (φ : 𝓓(Ω, ℝ)) :
    quadraticDistribution T v φ = star v ⬝ᵥ (Matrix.of (fun i j => T i j φ) *ᵥ v) := by
  let e : 𝓓'(Ω, ℂ) →+ ℂ :=
    { toFun := fun S => S φ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change e (∑ i, ∑ j, (star (v i) * v j) • T i j) = _
  simp only [map_sum, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change ((star (v i) * v j) • T i j) φ = _
  rw [_root_.smul_apply, smul_eq_mul]
  ring

theorem quadraticDistribution_re_nonnegative {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (v : ι → ℂ) :
    PositiveDistribution (Distribution.mapCLM Complex.reCLM (quadraticDistribution T v)) := by
  intro φ hφ
  rw [Distribution.mapCLM_apply, Complex.reCLM_apply, quadraticDistribution_apply]
  exact (Complex.nonneg_iff.mp ((hT.2 φ hφ).dotProduct_mulVec_nonneg v)).1

private theorem existsUnique_quadraticMeasure {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (v : ι → ℂ) :
    ∃! μ : Measure Ω, μ.Regular ∧
      ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂μ) = (quadraticDistribution T v φ).re := by
  obtain ⟨μ, hμ, _, hpair⟩ := (quadraticDistribution_re_nonnegative hT v).exists_regular_measure
  refine ⟨μ, ⟨hμ, hpair⟩, ?_⟩
  rintro ν ⟨hν, htest⟩
  let : μ.Regular := hμ
  let : ν.Regular := hν
  exact measure_eq_of_smooth_test fun φ => (htest φ).trans (hpair φ).symm

/-- The positive Radon measure of a quadratic contraction. -/
noncomputable def quadraticMeasure {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (v : ι → ℂ) : Measure Ω :=
  (existsUnique_quadraticMeasure hT v).exists.choose

theorem quadraticMeasure_regular {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (v : ι → ℂ) :
    (quadraticMeasure hT v).Regular :=
  (existsUnique_quadraticMeasure hT v).exists.choose_spec.1

theorem integral_quadraticMeasure {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (v : ι → ℂ) (φ : 𝓓(Ω, ℝ)) :
    (∫ x : Ω, φ x ∂quadraticMeasure hT v) = (quadraticDistribution T v φ).re :=
  (existsUnique_quadraticMeasure hT v).exists.choose_spec.2 φ

variable [DecidableEq ι]

private def basisVector (i : ι) : ι → ℂ := Pi.single i 1

private theorem quadratic_pair (M : Matrix ι ι ℂ) (i j : ι) (c : ℂ) :
    let w := basisVector i + c • basisVector j
    star w ⬝ᵥ (M *ᵥ w) =
      M i i + c * M i j + star c * M j i + star c * c * M j j := by
  have hs (k : ι) : star (basisVector k) = basisVector k := by
    funext l
    by_cases hl : l = k <;> simp [basisVector, hl]
  dsimp only
  simp only [star_add, star_smul, hs]
  simp only [basisVector, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_single_one,
    dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul, single_dotProduct,
    Matrix.col_apply, one_mul, smul_eq_mul]
  ring

private theorem entry_eq_quadratic_polarization (M : Matrix ι ι ℂ) (i j : ι) :
    let q := fun v : ι → ℂ => star v ⬝ᵥ (M *ᵥ v)
    let e := basisVector i
    let f := basisVector j
    M i j = (q (e + f) - q (e - f)) / 4 +
      Complex.I * (q (e - Complex.I • f) - q (e + Complex.I • f)) / 4 := by
  dsimp only
  have h₁ := quadratic_pair M i j (1 : ℂ)
  have h₂ := quadratic_pair M i j (-1 : ℂ)
  have h₃ := quadratic_pair M i j (-Complex.I)
  dsimp only at h₁ h₂ h₃
  rw [one_smul] at h₁
  rw [neg_one_smul, ← sub_eq_add_neg] at h₂
  rw [neg_smul, ← sub_eq_add_neg] at h₃
  rw [h₁, h₂, h₃, quadratic_pair M i j Complex.I]
  simp only [star_neg, star_one, Complex.star_def, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Every coefficient of a positive matrix of distributions is represented
by a linear combination of four positive measures. -/
theorem matrixDistribution_entry_apply {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (i j : ι) (φ : 𝓓(Ω, ℝ)) :
    let e := basisVector i
    let f := basisVector j
    T i j φ =
      ((∫ x : Ω, φ x ∂quadraticMeasure hT (e + f)) -
        (∫ x : Ω, φ x ∂quadraticMeasure hT (e - f)) : ℝ) / 4 +
      Complex.I * (((∫ x : Ω, φ x ∂quadraticMeasure hT (e - Complex.I • f)) -
        (∫ x : Ω, φ x ∂quadraticMeasure hT (e + Complex.I • f)) : ℝ) : ℂ) / 4 := by
  have hreal (v : ι → ℂ) :
      ((show ℝ from ∫ x : Ω, φ x ∂quadraticMeasure hT v) : ℂ) =
        star v ⬝ᵥ (Matrix.of (fun i j => T i j φ) *ᵥ v) := by
    rw [integral_quadraticMeasure, quadraticDistribution_apply]
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im, RCLike.im_eq_complex_im] using
        ((hT.1 φ).im_star_dotProduct_mulVec_self v).symm
  dsimp only
  simp only [Complex.ofReal_sub, hreal]
  exact entry_eq_quadratic_polarization (Matrix.of fun i j => T i j φ) i j

private theorem realEntry_pairing {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (i j : ι) (φ : 𝓓(Ω, ℝ)) :
    Distribution.mapCLM Complex.reCLM (T i j) φ =
      (∫ x : Ω, φ x ∂(ENNReal.ofReal (1 / 4) • quadraticMeasure hT (basisVector i + basisVector j))) -
       ∫ x : Ω, φ x ∂(ENNReal.ofReal (1 / 4) • quadraticMeasure hT (basisVector i - basisVector j)) := by
  rw [Distribution.mapCLM_apply, Complex.reCLM_apply, matrixDistribution_entry_apply hT i j φ]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_div, add_zero,
    integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  ring

private theorem imagEntry_pairing {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (i j : ι) (φ : 𝓓(Ω, ℝ)) :
    Distribution.mapCLM Complex.imCLM (T i j) φ =
      (∫ x : Ω, φ x ∂(ENNReal.ofReal (1 / 4) •
        quadraticMeasure hT (basisVector i - Complex.I • basisVector j))) -
       ∫ x : Ω, φ x ∂(ENNReal.ofReal (1 / 4) •
        quadraticMeasure hT (basisVector i + Complex.I • basisVector j)) := by
  rw [Distribution.mapCLM_apply, Complex.imCLM_apply, matrixDistribution_entry_apply hT i j φ]
  simp only [Complex.add_im, Complex.div_ofNat_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, zero_div,
    integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  ring

private theorem scaledQuadraticMeasure_regular {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (v : ι → ℂ) :
    (ENNReal.ofReal (1 / 4) • quadraticMeasure hT v).Regular := by
  let : (quadraticMeasure hT v).Regular := quadraticMeasure_regular hT v
  exact Measure.Regular.smul ENNReal.ofReal_ne_top

theorem matrixDistribution_realEntry_isMeasureDifference {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (i j : ι) :
    IsMeasureDifference (Distribution.mapCLM Complex.reCLM (T i j)) :=
  ⟨_, _, scaledQuadraticMeasure_regular hT _, scaledQuadraticMeasure_regular hT _,
    realEntry_pairing hT i j⟩

theorem matrixDistribution_imagEntry_isMeasureDifference {T : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (i j : ι) :
    IsMeasureDifference (Distribution.mapCLM Complex.imCLM (T i j)) :=
  ⟨_, _, scaledQuadraticMeasure_regular hT _, scaledQuadraticMeasure_regular hT _,
    imagEntry_pairing hT i j⟩

/-- Multiply each coefficient of a positive matrix distribution by a
locally bounded PSH function. The real and imaginary parts use well-defined
differences of locally finite Radon measures. -/
noncomputable def weightPositiveMatrixDistribution {u : ComplexModel n → ℝ}
    {T : Matrix ι ι 𝓓'(Ω, ℂ)} (hu : IsLocallyBoundedPshOn Ω u)
    (hT : IsPositiveMatrixDistribution T) : Matrix ι ι 𝓓'(Ω, ℂ) :=
  Matrix.of fun i j =>
    Distribution.mapCLM Complex.ofRealCLM
        (weightMeasureDifference hu (matrixDistribution_realEntry_isMeasureDifference hT i j)) +
      Complex.I • Distribution.mapCLM Complex.ofRealCLM
        (weightMeasureDifference hu (matrixDistribution_imagEntry_isMeasureDifference hT i j))

theorem weightPositiveMatrixDistribution_entry_apply {u : ComplexModel n → ℝ}
    {T : Matrix ι ι 𝓓'(Ω, ℂ)} (hu : IsLocallyBoundedPshOn Ω u)
    (hT : IsPositiveMatrixDistribution T) (i j : ι) (φ : 𝓓(Ω, ℝ)) :
    let e := basisVector i
    let f := basisVector j
    let eval := fun v => ∫ x : Ω, φ x * u x ∂quadraticMeasure hT v
    weightPositiveMatrixDistribution hu hT i j φ =
      ((eval (e + f) - eval (e - f) : ℝ) : ℂ) / 4 +
        Complex.I * ((eval (e - Complex.I • f) - eval (e + Complex.I • f) : ℝ) : ℂ) / 4 := by
  haveI (v : ι → ℂ) : (ENNReal.ofReal (1 / 4) • quadraticMeasure hT v).Regular :=
    scaledQuadraticMeasure_regular hT v
  simp only [weightPositiveMatrixDistribution, Matrix.of_apply, _root_.add_apply, _root_.smul_apply,
    Distribution.mapCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [weightMeasureDifference_apply hu _ (realEntry_pairing hT i j),
    weightMeasureDifference_apply hu _ (imagEntry_pairing hT i j)]
  simp only [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  push_cast
  ring

theorem weightPositiveMatrixDistribution_congr {u p : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p) (heq : EqOn u p Ω)
    {T S : Matrix ι ι 𝓓'(Ω, ℂ)} (hT : IsPositiveMatrixDistribution T)
    (hS : IsPositiveMatrixDistribution S) (hEq : T = S) :
    weightPositiveMatrixDistribution hu hT = weightPositiveMatrixDistribution hp hS := by
  subst S
  ext i j φ
  simp only [weightPositiveMatrixDistribution, Matrix.of_apply,
    weightMeasureDifference_congr hu hp heq]

theorem quadraticMeasure_congr {T S : Matrix ι ι 𝓓'(Ω, ℂ)}
    (hT : IsPositiveMatrixDistribution T) (hS : IsPositiveMatrixDistribution S)
    (heq : T = S) (v : ι → ℂ) :
    quadraticMeasure hT v = quadraticMeasure hS v := by
  subst S
  rfl

end KEBall.BedfordTaylor
