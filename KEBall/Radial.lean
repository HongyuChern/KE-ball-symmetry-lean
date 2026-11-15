import KEBall.RadialCoordinates
import KEBall.CofactorDivergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The actual radial potential and its complex Hessian

The computations start with the real Frechet derivative of the concrete
Euclidean norm and use the fixed interleaved-coordinate Wirtinger operators.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise

namespace KEBall
open KEBallProbe

noncomputable def radialProfile (n : ℕ) (b t : ℝ) : ℝ :=
  (n + 1 : ℝ) * Real.log ((1 + b * t) / (1 + b))

noncomputable def radialSlopeProfile (n : ℕ) (b t : ℝ) : ℝ :=
  (n + 1 : ℝ) * b / (1 + b * t)

lemma radial_denominator_pos {b : ℝ} (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    0 < 1 + b * t := by positivity

lemma hasDerivAt_radialProfile (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    HasDerivAt (radialProfile n b) (radialSlopeProfile n b t) t := by
  have hb1 : 0 < 1 + b := by positivity
  have hd : 0 < 1 + b * t := radial_denominator_pos hb ht
  have hbase : HasDerivAt (fun s : ℝ => (1 + b * s) / (1 + b))
      (b / (1 + b)) t :=
    by simpa only [id_eq, mul_one] using
      (((hasDerivAt_id t).const_mul b).const_add 1).div_const (1 + b)
  have h := (hbase.log (ne_of_gt (div_pos hd hb1))).const_mul (n + 1 : ℝ)
  convert h using 1 <;> try rfl
  dsimp [radialSlopeProfile]
  field_simp

lemma hasDerivAt_radialSlopeProfile (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    HasDerivAt (radialSlopeProfile n b) (-(n + 1 : ℝ) * b ^ 2 / (1 + b * t) ^ 2) t := by
  have hd : 0 < 1 + b * t := radial_denominator_pos hb ht
  have h := (hasDerivAt_const t ((n + 1 : ℝ) * b)).div
    (((hasDerivAt_id t).const_mul b).const_add 1) (ne_of_gt hd)
  convert h using 1 <;> try rfl
  dsimp
  ring

theorem smooth_radialPotential (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (radialPotential n b) := by
  have hbase : ContDiff ℝ ∞ (fun x : E n => (1 + b * ‖x‖ ^ 2) / (1 + b)) :=
    (contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))).div_const (1 + b)
  exact contDiff_const.mul (hbase.log fun x => ne_of_gt
    (div_pos (radial_denominator_pos hb (sq_nonneg ‖x‖)) (by positivity)))

lemma smooth_radialSlope (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (fun x : E n => radialSlopeProfile n b (‖x‖ ^ 2)) := by
  exact contDiff_const.div (contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ)))
    (fun x => ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖)))

theorem partialBar_radialPotential (n : ℕ) {b : ℝ} (hb : 0 < b)
    (j : Fin n) (x : E n) :
    partialBar j (fun y => (radialPotential n b y : ℂ)) x =
      (radialSlopeProfile n b (‖x‖ ^ 2) : ℂ) * complexCoord x j := by
  exact partialBar_ofReal_comp_norm_sq (hasDerivAt_radialProfile n hb (sq_nonneg ‖x‖)) j

theorem partialZ_radialSlope (n : ℕ) {b : ℝ} (hb : 0 < b)
    (i : Fin n) (x : E n) :
    partialZ i (fun y => (radialSlopeProfile n b (‖y‖ ^ 2) : ℂ)) x =
      (-(n + 1 : ℝ) * b ^ 2 / (1 + b * ‖x‖ ^ 2) ^ 2 : ℂ) * star (complexCoord x i) := by
  simpa using partialZ_ofReal_comp_norm_sq
    (hasDerivAt_radialSlopeProfile n hb (sq_nonneg ‖x‖)) i

theorem radial_complexHessian_entry (n : ℕ) {b : ℝ} (hb : 0 < b)
    (x : E n) (i j : Fin n) :
    complexHessian (radialPotential n b) x i j =
      ((n + 1 : ℝ) * b / (1 + b * ‖x‖ ^ 2) : ℂ) * (if i = j then 1 else 0) -
        ((n + 1 : ℝ) * b ^ 2 / (1 + b * ‖x‖ ^ 2) ^ 2 : ℂ) *
          star (complexCoord x i) * complexCoord x j := by
  have hfirst : partialBar j (fun y => (radialPotential n b y : ℂ)) =
      fun y => (radialSlopeProfile n b (‖y‖ ^ 2) : ℂ) * complexCoord y j :=
    funext (partialBar_radialPotential n hb j)
  have hcoeff : DifferentiableAt ℝ
      (fun y : E n => (radialSlopeProfile n b (‖y‖ ^ 2) : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (smooth_radialSlope n hb)).differentiable (by simp) x
  change partialZ i (partialBar j (fun y => (radialPotential n b y : ℂ))) x = _
  rw [hfirst]
  change dz (realDirection i) (imagDirection i)
    (fun y => (radialSlopeProfile n b (‖y‖ ^ 2) : ℂ) * complexCoord y j) x = _
  rw [dz_mul_differentiableAt hcoeff ((smooth_complexCoord j).differentiable (by simp) x)]
  change partialZ i (fun y => (radialSlopeProfile n b (‖y‖ ^ 2) : ℂ)) x * complexCoord x j +
    (radialSlopeProfile n b (‖x‖ ^ 2) : ℂ) * partialZ i (fun y => complexCoord y j) x = _
  rw [partialZ_radialSlope n hb, partialZ_complexCoord]
  unfold radialSlopeProfile
  push_cast
  ring

theorem radial_complexHessian (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    complexHessian (radialPotential n b) x =
      ((n + 1 : ℝ) * b / (1 + b * ‖x‖ ^ 2) : ℂ) •
        (1 - (b / (1 + b * ‖x‖ ^ 2) : ℂ) •
          Matrix.vecMulVec (star (complexCoord x)) (complexCoord x)) := by
  ext i j
  rw [radial_complexHessian_entry n hb]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  push_cast
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

theorem radial_boundary_zero (n : ℕ) {b : ℝ} (hb : 0 < b)
    {x : E n} (hx : x ∈ unitSphere n) : radialPotential n b x = 0 := by
  have hxnorm : ‖x‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  have hb1 : 1 + b ≠ 0 := ne_of_gt (by positivity : 0 < 1 + b)
  simp [radialPotential, hxnorm, hb1]

lemma dot_complexCoord_star {n : ℕ} (x : E n) :
    complexCoord x ⬝ᵥ star (complexCoord x) = (‖x‖ ^ 2 : ℝ) := by
  simpa only [dotProduct, Pi.star_apply, mul_comm] using sum_star_complexCoord_mul x

lemma radial_rank_one_square {n : ℕ} (x : E n) :
    Matrix.vecMulVec (star (complexCoord x)) (complexCoord x) *
        Matrix.vecMulVec (star (complexCoord x)) (complexCoord x) =
      (‖x‖ ^ 2 : ℂ) • Matrix.vecMulVec (star (complexCoord x)) (complexCoord x) := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, dot_complexCoord_star]
  norm_cast

lemma radial_gram_inverse (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    (1 + (b : ℂ) • Matrix.vecMulVec (star (complexCoord x)) (complexCoord x))⁻¹ =
      1 - (b / (1 + b * ‖x‖ ^ 2) : ℂ) •
        Matrix.vecMulVec (star (complexCoord x)) (complexCoord x) := by
  apply Matrix.inv_eq_right_inv
  simp only [add_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, radial_rank_one_square, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hd : (1 + (b : ℂ) * (‖x‖ : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖))
  field_simp
  ring

theorem radial_complexHessian_posDef (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    (complexHessian (radialPotential n b) x).PosDef := by
  have hbC : (0 : ℂ) < (b : ℂ) := by exact_mod_cast hb
  have hgram :
      (1 + (b : ℂ) • Matrix.vecMulVec (star (complexCoord x)) (complexCoord x)).PosDef :=
    Matrix.PosDef.one.add_posSemidef
      ((Matrix.posSemidef_vecMulVec_star_self (complexCoord x)).smul hbC.le)
  have hinv := hgram.inv
  rw [radial_gram_inverse n hb] at hinv
  rw [radial_complexHessian n hb]
  apply hinv.smul
  have hn : (0 : ℝ) < n + 1 := by positivity
  exact_mod_cast div_pos (mul_pos hn hb) (radial_denominator_pos hb (sq_nonneg ‖x‖))

lemma det_one_add_smul_outer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (v w : ι → ℂ) :
    (1 + c • Matrix.vecMulVec v w).det = 1 + c * (w ⬝ᵥ v) := by
  rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]

theorem radial_complexHessian_det (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    (complexHessian (radialPotential n b) x).det =
      ((n + 1 : ℝ) ^ n * b ^ n / (1 + b * ‖x‖ ^ 2) ^ (n + 1) : ℂ) := by
  have hd : (1 + (b : ℂ) * (‖x‖ : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖))
  have hdet :
      (1 - (b / (1 + b * ‖x‖ ^ 2) : ℂ) •
        Matrix.vecMulVec (star (complexCoord x)) (complexCoord x)).det =
        (1 + (b : ℂ) * (‖x‖ : ℂ) ^ 2)⁻¹ := by
    rw [sub_eq_add_neg, ← neg_smul, det_one_add_smul_outer, dot_complexCoord_star]
    push_cast
    field_simp
    ring
  rw [radial_complexHessian n hb, Matrix.det_smul, Fintype.card_fin, hdet]
  push_cast
  simp only [div_eq_mul_inv, mul_pow, ← inv_pow]
  rw [pow_succ]
  ring

theorem radial_exp_neg (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    Real.exp (-radialPotential n b x) =
      ((1 + b) / (1 + b * ‖x‖ ^ 2)) ^ (n + 1) := by
  have hp : 0 < (1 + b * ‖x‖ ^ 2) / (1 + b) :=
    div_pos (radial_denominator_pos hb (sq_nonneg ‖x‖)) (by positivity)
  have he : Real.exp ((n + 1 : ℝ) * Real.log ((1 + b * ‖x‖ ^ 2) / (1 + b))) =
      ((1 + b * ‖x‖ ^ 2) / (1 + b)) ^ (n + 1) := by
    have h := Real.exp_nat_mul (Real.log ((1 + b * ‖x‖ ^ 2) / (1 + b))) (n + 1)
    simpa only [Nat.cast_add, Nat.cast_one, Real.exp_log hp] using h
  rw [radialPotential, Real.exp_neg, he, ← inv_pow, inv_div]

theorem radial_equation (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    (complexHessian (radialPotential n b) x).det =
      (radialCoefficient n b * Real.exp (-radialPotential n b x) : ℂ) := by
  rw [radial_complexHessian_det n hb, radial_exp_neg n hb]
  have hb1 : 1 + b ≠ 0 := ne_of_gt (by positivity : 0 < 1 + b)
  have hd : 1 + b * ‖x‖ ^ 2 ≠ 0 :=
    ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖))
  have hreal : (n + 1 : ℝ) ^ n * b ^ n / (1 + b * ‖x‖ ^ 2) ^ (n + 1) =
      radialCoefficient n b * ((1 + b) / (1 + b * ‖x‖ ^ 2)) ^ (n + 1) := by
    unfold radialCoefficient
    rw [div_pow]
    field_simp
  exact_mod_cast hreal

/-- The full reverse construction, with no assumed Hessian formula. -/
theorem radial_isSolution (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IsSolution n (radialCoefficient n b) (radialPotential n b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold radialCoefficient
    positivity
  · exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, (smooth_radialPotential n hb).contDiffOn⟩
  · intro x _
    exact radial_complexHessian_posDef n hb x
  · intro x _
    exact radial_equation n hb x
  · intro x hx
    exact radial_boundary_zero n hb hx

#print axioms radial_complexHessian
#print axioms radial_boundary_zero
#print axioms radial_complexHessian_posDef
#print axioms radial_complexHessian_det
#print axioms radial_isSolution

end KEBall
