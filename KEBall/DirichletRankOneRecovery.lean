import KEBall.DirichletUniformEllipticity
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Recovering the missing normal Hessian coefficient from the determinant. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

private theorem det_one_add_vecMulVec {n : ℕ} (z w : Fin n → ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + Matrix.vecMulVec z w).det = 1 + w ⬝ᵥ z := by
  rw [show Matrix.vecMulVec z w =
      Matrix.replicateCol (Fin 1) z * Matrix.replicateRow (Fin 1) w by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mul_apply]]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow z w

/-- A real rank-one update of a positive Hermitian matrix changes its real
determinant affinely, with strictly positive slope for a nonzero direction. -/
theorem det_re_hermitian_rankOne_update {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (z : Fin n → ℂ) (t : ℝ) :
    (A + (t : ℂ) • Matrix.vecMulVec z (star z)).det.re =
      A.det.re * (1 + t * (star z ⬝ᵥ (A⁻¹ *ᵥ z)).re) := by
  have hU : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  let w := (t : ℂ) • (A⁻¹ *ᵥ z)
  have hFact : A + (t : ℂ) • Matrix.vecMulVec z (star z) =
      A * (1 + Matrix.vecMulVec w (star z)) := by
    have hAw : A *ᵥ w = (t : ℂ) • z := by
      rw [show w = (t : ℂ) • (A⁻¹ *ᵥ z) from rfl, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, hAw]
    congr 1
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc]
  rw [hFact, Matrix.det_mul, det_one_add_vecMulVec, posDef_det_eq_ofReal_re hA]
  simp [w, dotProduct_smul, Complex.mul_re]

/-- When the remainder of the Hermitian Hessian is obtained by removing
a rank-one normal contribution, the determinant recovers the coefficient
of that contribution exactly. -/
theorem real_rankOne_coefficient_eq_of_det {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {z : Fin n → ℂ} (hz : z ≠ 0) {t : ℝ}
    (hB : B = A + (t : ℂ) • Matrix.vecMulVec z (star z)) :
    t = (B.det.re - A.det.re) / (A.det.re * (star z ⬝ᵥ (A⁻¹ *ᵥ z)).re) := by
  have hQ : 0 < (star z ⬝ᵥ (A⁻¹ *ᵥ z)).re :=
    (RCLike.pos_iff.mp (hA.inv.dotProduct_mulVec_pos hz)).1
  have hD := posDef_det_re_pos hA
  rw [eq_div_iff (mul_pos hD hQ).ne', hB, det_re_hermitian_rankOne_update hA]
  ring

/-- The slope of a rank-one determinant update, written polynomially in
the matrix entries using the adjugate. -/
noncomputable def hermitianRankOneDetSlope {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) : ℝ :=
  (star z ⬝ᵥ (A.adjugate *ᵥ z)).re

theorem hermitianRankOneDetSlope_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (z : Fin n → ℂ) :
    hermitianRankOneDetSlope A z = A.det.re * (star z ⬝ᵥ (A⁻¹ *ᵥ z)).re := by
  have hU : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hAdj : A.adjugate = A.det • A⁻¹ := by
    have hMul : A.det * (↑hU.unit⁻¹ : ℂ) = 1 :=
      calc
        A.det * (↑hU.unit⁻¹ : ℂ) = (↑hU.unit : ℂ) * (↑hU.unit⁻¹ : ℂ) :=
          congrArg (· * (↑hU.unit⁻¹ : ℂ)) hU.unit_spec.symm
        _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.nonsing_inv_apply _ hU, smul_smul, hMul, one_smul]
  rw [hermitianRankOneDetSlope, hAdj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    posDef_det_eq_ofReal_re hA]
  simp [Complex.mul_re]

theorem hermitianRankOneDetSlope_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {z : Fin n → ℂ} (hz : z ≠ 0) :
    0 < hermitianRankOneDetSlope A z := by
  rw [hermitianRankOneDetSlope_eq hA]
  exact mul_pos (posDef_det_re_pos hA)
    (RCLike.pos_iff.mp (hA.inv.dotProduct_mulVec_pos hz)).1

/-- The determinant has the common regularity of the matrix entries. -/
theorem contDiffOn_det_of_contDiffOn_entries {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} {r : ℕ∞ω} {S : Set X}
    {A : X → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) S) :
    ContDiffOn ℝ r (fun x => (A x).det) S := by
  classical
  simp only [Matrix.det_apply]
  exact ContDiffOn.sum fun σ _ => (contDiffOn_prod fun i _ => hA (σ i) i).const_smul _

theorem contDiffOn_adjugate_of_contDiffOn_entries {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} {r : ℕ∞ω} {S : Set X}
    {A : X → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) S) (i j : Fin n) :
    ContDiffOn ℝ r (fun x => (A x).adjugate i j) S := by
  classical
  simp only [Matrix.adjugate_apply]
  apply contDiffOn_det_of_contDiffOn_entries
  intro a b
  by_cases h : a = j
  · subst a
    let row : Fin n → ℂ := Pi.single i 1
    change ContDiffOn ℝ r (fun x => ((A x).updateRow j row) j b) S
    exact (contDiffOn_const (c := row b)).congr fun x _ => by rw [Matrix.updateRow_self]
  · simpa only [Matrix.updateRow_ne h] using hA a b

theorem contDiffOn_hermitianRankOneDetSlope {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} {r : ℕ∞ω} {S : Set X}
    {A : X → Matrix (Fin n) (Fin n) ℂ} {z : X → Fin n → ℂ}
    (hA : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) S)
    (hz : ∀ i, ContDiffOn ℝ r (fun x => z x i) S) :
    ContDiffOn ℝ r (fun x => hermitianRankOneDetSlope (A x) (z x)) S := by
  apply Complex.reCLM.contDiff.comp_contDiffOn
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  exact ContDiffOn.sum fun i _ => (Complex.conjCLE.contDiff.comp_contDiffOn (hz i)).mul
    (ContDiffOn.sum fun j _ => (contDiffOn_adjugate_of_contDiffOn_entries hA i j).mul (hz j))

/-- A positive Hermitian reference field determines the regularity of the
missing real rank-one coefficient from the given determinant. -/
theorem contDiffOn_of_hermitianRankOne_det {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} {r : ℕ∞ω} {S : Set X}
    {A : X → Matrix (Fin n) (Fin n) ℂ} {z : X → Fin n → ℂ} {t f : X → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) S)
    (hz : ∀ i, ContDiffOn ℝ r (fun x => z x i) S)
    (hP : ∀ x ∈ S, (A x).PosDef) (hZ : ∀ x ∈ S, z x ≠ 0)
    (hf : ContDiffOn ℝ r f S)
    (hEq : ∀ x ∈ S, (A x + (t x : ℂ) • Matrix.vecMulVec (z x) (star (z x))).det.re = f x) :
    ContDiffOn ℝ r t S := by
  have hD : ContDiffOn ℝ r (fun x => (A x).det.re) S :=
    Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_det_of_contDiffOn_entries hA)
  refine ((hf.sub hD).div (contDiffOn_hermitianRankOneDetSlope hA hz)
    (fun x hx => (hermitianRankOneDetSlope_pos (hP x hx) (hZ x hx)).ne')).congr ?_
  intro x hx
  change t x = (f x - (A x).det.re) / hermitianRankOneDetSlope (A x) (z x)
  rw [hermitianRankOneDetSlope_eq (hP x hx), ← hEq x hx]
  exact real_rankOne_coefficient_eq_of_det (hP x hx) (hZ x hx) rfl

end KEBall
