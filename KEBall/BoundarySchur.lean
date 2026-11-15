import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import KEBall.Domain

/-!
# A coordinate-free scalar horizontal block and its normal adjugate

The two low-rank updates are evaluated by the actual matrix determinant
lemma. This is the normal Schur calculation without assuming a chosen
unitary frame. No determinant or adjugate formula is a hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators

namespace KEBall

noncomputable def borderedScalarMatrix {n : ℕ} (t a : ℂ)
    (c d b e : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  t • 1 + vecMulVec b d + vecMulVec c e + (a - t) • vecMulVec c d

theorem borderedScalarMatrix_det {n : ℕ} (hn : 1 ≤ n) {t a : ℂ}
    (ht : t ≠ 0) {c d b e : Fin n → ℂ}
    (hdc : d ⬝ᵥ c = 1) (hdb : d ⬝ᵥ b = 0) (hec : e ⬝ᵥ c = 0) :
    (borderedScalarMatrix t a c d b e).det =
      t ^ (n - 1) * (a - (e ⬝ᵥ b) / t) := by
  let U : Matrix (Fin n) (Fin 2) ℂ := fun i k =>
    if k = 0 then t⁻¹ * b i else t⁻¹ * c i
  let V : Matrix (Fin 2) (Fin n) ℂ := fun k j =>
    if k = 0 then d j else e j + (a - t) * d j
  have hfact : borderedScalarMatrix t a c d b e = t • (1 + U * V) := by
    ext i j
    simp only [borderedScalarMatrix, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, vecMulVec_apply, Matrix.mul_apply, Fin.sum_univ_two,
      U, V, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    field_simp
    ring
  have h00 : (V * U) 0 0 = 0 := by
    change (∑ k : Fin n, d k * (t⁻¹ * b k)) = 0
    calc
      _ = t⁻¹ * (d ⬝ᵥ b) := by simp only [dotProduct, Finset.mul_sum]; congr 1; funext k; ring
      _ = 0 := by rw [hdb, mul_zero]
  have h01 : (V * U) 0 1 = t⁻¹ := by
    change (∑ k : Fin n, d k * (t⁻¹ * c k)) = t⁻¹
    calc
      _ = t⁻¹ * (d ⬝ᵥ c) := by simp only [dotProduct, Finset.mul_sum]; congr 1; funext k; ring
      _ = _ := by rw [hdc, mul_one]
  have h10 : (V * U) 1 0 = t⁻¹ * (e ⬝ᵥ b) := by
    change (∑ k : Fin n, (e k + (a - t) * d k) * (t⁻¹ * b k)) = _
    calc
      _ = t⁻¹ * (e ⬝ᵥ b) + ((a - t) * t⁻¹) * (d ⬝ᵥ b) := by
        simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hdb, mul_zero, add_zero]
  have h11 : (V * U) 1 1 = (a - t) / t := by
    change (∑ k : Fin n, (e k + (a - t) * d k) * (t⁻¹ * c k)) = _
    calc
      _ = t⁻¹ * (e ⬝ᵥ c) + ((a - t) * t⁻¹) * (d ⬝ᵥ c) := by
        simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hec, hdc, mul_zero, zero_add, mul_one]; rfl
  rw [hfact, Matrix.det_smul, Matrix.det_one_add_mul_comm, Matrix.det_fin_two]
  simp only [Fintype.card_fin, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), h00, h01, h10, h11,
    add_zero, zero_add, one_mul]
  have hpow : t ^ n = t ^ (n - 1) * t := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  field_simp
  ring

theorem borderedScalarMatrix_mulVec_normal {n : ℕ} {t a : ℂ} (ht : t ≠ 0)
    {c d b e : Fin n → ℂ} (hdc : d ⬝ᵥ c = 1)
    (hdb : d ⬝ᵥ b = 0) (hec : e ⬝ᵥ c = 0) :
    (borderedScalarMatrix t a c d b e).mulVec (c - t⁻¹ • b) =
      (a - (e ⬝ᵥ b) / t) • c := by
  have hdn : d ⬝ᵥ (c - t⁻¹ • b) = 1 := by
    rw [dotProduct_sub, dotProduct_smul, hdc, hdb, smul_eq_mul, mul_zero, sub_zero]
  have hen : e ⬝ᵥ (c - t⁻¹ • b) = -t⁻¹ * (e ⬝ᵥ b) := by
    rw [dotProduct_sub, dotProduct_smul, hec, smul_eq_mul]
    ring
  unfold borderedScalarMatrix
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, hdn, hen, op_smul_eq_smul,
    one_smul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem borderedScalarMatrix_adjugate_normal {n : ℕ} (hn : 1 ≤ n) {t a : ℂ}
    (ht : t ≠ 0) {c d b e : Fin n → ℂ}
    (hdc : d ⬝ᵥ c = 1) (hdb : d ⬝ᵥ b = 0) (hec : e ⬝ᵥ c = 0)
    (hdet : (borderedScalarMatrix t a c d b e).det ≠ 0) :
    (borderedScalarMatrix t a c d b e).adjugate.mulVec c =
      t ^ (n - 1) • (c - t⁻¹ • b) := by
  apply Matrix.mulVec_injective_of_det_ne_zero hdet
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_smul,
    borderedScalarMatrix_mulVec_normal ht hdc hdb hec,
    borderedScalarMatrix_det hn ht hdc hdb hec, smul_smul]

#print axioms borderedScalarMatrix_det
#print axioms borderedScalarMatrix_mulVec_normal
#print axioms borderedScalarMatrix_adjugate_normal

end KEBall
