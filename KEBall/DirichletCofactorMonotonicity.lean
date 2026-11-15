import KEBall.DirichletUniformEllipticity
import Mathlib.Analysis.Complex.Order

/-! Quantitative monotonicity of inversion on positive Hermitian matrices. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

namespace KEBall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_mul_re_nonneg_of_posSemidef {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  change A = Cᴴ * C at hC
  rw [hC, ← Matrix.trace_mul_cycle]
  exact (RCLike.nonneg_iff.mp (hB.mul_mul_conjTranspose_same C).trace_nonneg).1

private theorem trace_hermitian_mul_ge_of_smul_one_le {A B D : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hD : D.IsHermitian) {a : ℝ}
    (hB : (a : ℂ) • (1 : Matrix ι ι ℂ) ≤ B) :
    a * (A * (D * D)).trace.re ≤ (A * (D * B * D)).trace.re := by
  have h := (Matrix.le_iff.mp hB).conjTranspose_mul_mul_same D
  rw [hD.eq] at h
  have ht := trace_mul_re_nonneg_of_posSemidef hA h
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at ht
  exact sub_nonneg.mp ht

omit [DecidableEq ι] in
private theorem trace_hermitian_square_re {D : Matrix ι ι ℂ} (hD : D.IsHermitian) :
    (D * D).trace.re = ∑ i, ∑ j, ‖D i j‖ ^ 2 := by
  have he : Dᴴ * D = D * D := congrArg (· * D) hD.eq
  rw [← he]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.sq_norm]
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]

/-- A lower bound on the two inverse matrices controls the squared
entrywise distance by the pairing of the inverse and matrix differences. -/
theorem posDef_inverse_difference_trace_ge {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {a : ℝ} (ha : 0 ≤ a)
    (hAi : (a : ℂ) • (1 : Matrix ι ι ℂ) ≤ A⁻¹)
    (hBi : (a : ℂ) • (1 : Matrix ι ι ℂ) ≤ B⁻¹) :
    a ^ 2 * (∑ i, ∑ j, ‖(B - A) i j‖ ^ 2) ≤ ((A⁻¹ - B⁻¹) * (B - A)).trace.re := by
  let D := B - A
  have hD : D.IsHermitian := hB.isHermitian.sub hA.isHermitian
  have hD₂ : (D * D).PosSemidef := by
    simpa only [hD.eq] using Matrix.posSemidef_conjTranspose_mul_self D
  have ht := trace_hermitian_mul_ge_of_smul_one_le hA.inv.posSemidef hD hBi
  have ht' := trace_mul_re_nonneg_of_posSemidef (Matrix.le_iff.mp hAi) hD₂
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at ht'
  have hLow := (mul_le_mul_of_nonneg_left (sub_nonneg.mp ht') ha).trans ht
  rw [← mul_assoc, ← pow_two, trace_hermitian_square_re hD] at hLow
  have hiA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hiB : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hInv : A⁻¹ * D * B⁻¹ = A⁻¹ - B⁻¹ := by
    rw [show D = B - A from rfl, Matrix.mul_sub, Matrix.sub_mul, mul_assoc A⁻¹,
      Matrix.mul_nonsing_inv _ hiB, Matrix.nonsing_inv_mul _ hiA, mul_one, one_mul]
  rwa [← mul_assoc A⁻¹, ← mul_assoc A⁻¹, hInv] at hLow


/-- An upper spectral bound for a positive matrix gives a scalar lower
bound for its inverse. -/
theorem smul_one_le_inverse_of_eigenvalues_le {A : Matrix ι ι ℂ}
    (hA : A.PosDef) {b : ℝ} (hb : 0 < b)
    (hEig : ∀ i, hA.isHermitian.eigenvalues i ≤ b) :
    (b⁻¹ : ℝ) • (1 : Matrix ι ι ℂ) ≤ A⁻¹ := by
  let U := hA.isHermitian.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ _ U
  let d : ι → ℂ := fun i => hA.isHermitian.eigenvalues i
  let di : ι → ℂ := fun i => ((hA.isHermitian.eigenvalues i)⁻¹ : ℝ)
  have hA' : A = e (diagonal d) := hA.isHermitian.spectral_theorem
  have hAi : A⁻¹ = e (diagonal di) := by
    apply Matrix.inv_eq_right_inv
    rw [hA', ← map_mul, Matrix.diagonal_mul_diagonal]
    have hd : d * di = 1 := by
      funext i
      change (hA.isHermitian.eigenvalues i : ℂ) * ((hA.isHermitian.eigenvalues i)⁻¹ : ℝ) = 1
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast (hA.eigenvalues_pos i).ne')]
    change e (diagonal (d * di)) = 1
    rw [hd]
    change e (diagonal fun _ => (1 : ℂ)) = 1
    rw [Matrix.diagonal_one, map_one]
  have he : A⁻¹ - (b⁻¹ : ℝ) • (1 : Matrix ι ι ℂ) =
      e (diagonal (fun i => ((hA.isHermitian.eigenvalues i)⁻¹ - b⁻¹ : ℝ) : ι → ℂ)) := by
    rw [hAi, show (b⁻¹ : ℝ) • (1 : Matrix ι ι ℂ) =
      e ((b⁻¹ : ℂ) • (1 : Matrix ι ι ℂ)) by
        rw [map_smul, map_one]
        ext i j
        simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv], ← map_sub]
    apply congrArg e
    ext i j
    by_cases h : i = j
    · subst j
      simp [di, Matrix.smul_apply, smul_eq_mul]
    · simp [h, di]
  rw [Matrix.le_iff, he, Unitary.conjStarAlgAut_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have h : 0 ≤ (hA.isHermitian.eigenvalues i)⁻¹ - b⁻¹ :=
    sub_nonneg.mpr ((inv_le_inv₀ hb (hA.eigenvalues_pos i)).mpr (hEig i))
  exact (Complex.zero_le_real).mpr h

/-- With a common positive lower bound on the inverse Hessians, the
cofactor difference controls the squared matrix distance up to a density
difference term. -/
theorem posDef_cofactor_difference_trace_ge {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {a : ℝ} (ha : 0 ≤ a)
    (hAi : (a : ℂ) • (1 : Matrix ι ι ℂ) ≤ A⁻¹)
    (hBi : (a : ℂ) • (1 : Matrix ι ι ℂ) ≤ B⁻¹) :
    A.det.re * a ^ 2 * (∑ i, ∑ j, ‖(B - A) i j‖ ^ 2) ≤
      ((A.adjugate - B.adjugate) * (B - A)).trace.re +
        (B.det.re - A.det.re) * (B⁻¹ * (B - A)).trace.re := by
  have h := mul_le_mul_of_nonneg_left (posDef_inverse_difference_trace_ge hA hB ha hAi hBi)
    (posDef_det_re_pos hA).le
  rw [← mul_assoc] at h
  refine h.trans_eq ?_
  have hAdj {C : Matrix ι ι ℂ} (hC : C.PosDef) : C.adjugate = (C.det.re : ℂ) • C⁻¹ := by
    rw [← posDef_det_eq_ofReal_re hC]
    have hu := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
    rw [Matrix.nonsing_inv_apply C hu, smul_smul, hu.mul_val_inv, one_smul]
  rw [hAdj hA, hAdj hB]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

end KEBall
