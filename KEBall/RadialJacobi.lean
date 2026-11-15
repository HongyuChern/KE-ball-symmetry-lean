import KEBall.Radial
import KEBall.Specification

/-!
# The actual positive Jacobi function on the stable radial branch

The radial linearized operator is derived from the Frechet/Wirtinger
Hessian and the proved matrix inverse.  No radial Laplacian identity is
assumed as an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise

namespace KEBall
open KEBallProbe

theorem radial_complexHessian_inverse (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    (complexHessian (radialPotential n b) x)⁻¹ =
      ((1 + b * ‖x‖ ^ 2) / ((n + 1 : ℝ) * b) : ℂ) •
        (1 + (b : ℂ) • Matrix.vecMulVec (star (complexCoord x)) (complexCoord x)) := by
  apply Matrix.inv_eq_right_inv
  rw [radial_complexHessian n hb]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_add, sub_mul,
    Matrix.one_mul, Matrix.mul_one, radial_rank_one_square]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hkC : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (n + 1 : ℝ) ≠ 0)
  have hd : (1 + (b : ℂ) * (‖x‖ : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖))
  push_cast
  field_simp
  ring

theorem complexHessian_radial_profile_entry {n : ℕ} {ρ ρ₁ : ℝ → ℝ} {ρ₂ : ℝ}
    (hρ : ∀ t : ℝ, 0 ≤ t → HasDerivAt ρ (ρ₁ t) t) {x : E n}
    (hρ₁ : HasDerivAt ρ₁ ρ₂ (‖x‖ ^ 2)) (i j : Fin n) :
    complexHessian (fun y : E n => ρ (‖y‖ ^ 2)) x i j =
      (ρ₁ (‖x‖ ^ 2) : ℂ) * (if i = j then 1 else 0) +
        (ρ₂ : ℂ) * star (complexCoord x i) * complexCoord x j := by
  have hfirst : partialBar j (fun y : E n => (ρ (‖y‖ ^ 2) : ℂ)) =
      fun y => (ρ₁ (‖y‖ ^ 2) : ℂ) * complexCoord y j := by
    funext y
    exact partialBar_ofReal_comp_norm_sq (hρ _ (sq_nonneg ‖y‖)) j
  have hcoeff : DifferentiableAt ℝ (fun y : E n => (ρ₁ (‖y‖ ^ 2) : ℂ)) x :=
    (Complex.ofRealCLM.hasFDerivAt.comp x
      (hρ₁.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt)).differentiableAt
  change partialZ i (partialBar j (fun y : E n => (ρ (‖y‖ ^ 2) : ℂ))) x = _
  rw [hfirst]
  change dz (realDirection i) (imagDirection i)
    (fun y : E n => (ρ₁ (‖y‖ ^ 2) : ℂ) * complexCoord y j) x = _
  rw [dz_mul_differentiableAt hcoeff ((smooth_complexCoord j).differentiable (by simp) x)]
  change partialZ i (fun y : E n => (ρ₁ (‖y‖ ^ 2) : ℂ)) x * complexCoord x j +
    (ρ₁ (‖x‖ ^ 2) : ℂ) * partialZ i (fun y => complexCoord y j) x = _
  rw [partialZ_ofReal_comp_norm_sq hρ₁, partialZ_complexCoord]
  ring

theorem complexHessian_radial_profile {n : ℕ} {ρ ρ₁ : ℝ → ℝ} {ρ₂ : ℝ}
    (hρ : ∀ t : ℝ, 0 ≤ t → HasDerivAt ρ (ρ₁ t) t) {x : E n}
    (hρ₁ : HasDerivAt ρ₁ ρ₂ (‖x‖ ^ 2)) :
    complexHessian (fun y : E n => ρ (‖y‖ ^ 2)) x =
      (ρ₁ (‖x‖ ^ 2) : ℂ) • 1 +
        (ρ₂ : ℂ) • Matrix.vecMulVec (star (complexCoord x)) (complexCoord x) := by
  ext i j
  rw [complexHessian_radial_profile_entry hρ hρ₁]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  ring

theorem complexLaplacian_eq_trace {n : ℕ} (u h : E n → ℝ) (x : E n) :
    complexLaplacian u h x =
      ((complexHessian u x)⁻¹ * complexHessian h x).trace.re := by
  unfold complexLaplacian inverseCoefficient
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_comm

theorem radial_outer_trace {n : ℕ} (x : E n) :
    (Matrix.vecMulVec (star (complexCoord x)) (complexCoord x)).trace =
      (‖x‖ ^ 2 : ℝ) := by
  rw [Matrix.trace_vecMulVec]
  exact sum_star_complexCoord_mul x

theorem complexLaplacian_radial_profile {n : ℕ} {b : ℝ} (hb : 0 < b)
    {ρ ρ₁ : ℝ → ℝ} {ρ₂ : ℝ}
    (hρ : ∀ t : ℝ, 0 ≤ t → HasDerivAt ρ (ρ₁ t) t) {x : E n}
    (hρ₁ : HasDerivAt ρ₁ ρ₂ (‖x‖ ^ 2)) :
    complexLaplacian (radialPotential n b) (fun y : E n => ρ (‖y‖ ^ 2)) x =
      (1 + b * ‖x‖ ^ 2) / ((n + 1 : ℝ) * b) *
        (((n : ℝ) + b * ‖x‖ ^ 2) * ρ₁ (‖x‖ ^ 2) +
          ‖x‖ ^ 2 * (1 + b * ‖x‖ ^ 2) * ρ₂) := by
  have htrace :
      ((complexHessian (radialPotential n b) x)⁻¹ *
        complexHessian (fun y : E n => ρ (‖y‖ ^ 2)) x).trace =
      ((1 + b * ‖x‖ ^ 2) / ((n + 1 : ℝ) * b) *
        (((n : ℝ) + b * ‖x‖ ^ 2) * ρ₁ (‖x‖ ^ 2) +
          ‖x‖ ^ 2 * (1 + b * ‖x‖ ^ 2) * ρ₂) : ℝ) := by
    rw [radial_complexHessian_inverse n hb, complexHessian_radial_profile hρ hρ₁]
    simp only [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, add_mul,
      Matrix.one_mul, Matrix.mul_one, radial_rank_one_square, Matrix.trace_smul,
      Matrix.trace_add, Matrix.trace_one, radial_outer_trace, smul_smul,
      Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  rw [complexLaplacian_eq_trace, htrace]
  rfl

noncomputable def radialJacobiProfile (n : ℕ) (b t : ℝ) : ℝ :=
  2 * ((n : ℝ) - b * t) / (1 + b * t)

noncomputable def radialJacobiSlopeProfile (n : ℕ) (b t : ℝ) : ℝ :=
  -2 * (n + 1 : ℝ) * b / (1 + b * t) ^ 2

noncomputable def radialJacobi (n : ℕ) (b : ℝ) (x : E n) : ℝ :=
  radialJacobiProfile n b (‖x‖ ^ 2)

theorem hasDerivAt_radialJacobiProfile (n : ℕ) {b t : ℝ}
    (hb : 0 < b) (ht : 0 ≤ t) :
    HasDerivAt (radialJacobiProfile n b) (radialJacobiSlopeProfile n b t) t := by
  have hd : 1 + b * t ≠ 0 := ne_of_gt (radial_denominator_pos hb ht)
  have hnum : HasDerivAt (fun s : ℝ => 2 * ((n : ℝ) - b * s)) (-2 * b) t := by
    convert ((hasDerivAt_const t (n : ℝ)).sub ((hasDerivAt_id t).const_mul b)).const_mul 2
      using 1 <;> try rfl
    ring
  have hden : HasDerivAt (fun s : ℝ => 1 + b * s) b t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul b).const_add 1
  convert hnum.div hden hd using 1 <;> try rfl
  dsimp [radialJacobiSlopeProfile]
  field_simp
  ring

theorem hasDerivAt_radialJacobiSlopeProfile (n : ℕ) {b t : ℝ}
    (hb : 0 < b) (ht : 0 ≤ t) :
    HasDerivAt (radialJacobiSlopeProfile n b)
      (4 * (n + 1 : ℝ) * b ^ 2 / (1 + b * t) ^ 3) t := by
  have hd : 1 + b * t ≠ 0 := ne_of_gt (radial_denominator_pos hb ht)
  have hden : HasDerivAt (fun s : ℝ => 1 + b * s) b t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul b).const_add 1
  have h := (hasDerivAt_const t (-2 * (n + 1 : ℝ) * b)).div
    (hden.pow 2) (pow_ne_zero 2 hd)
  convert h using 1 <;> try rfl
  dsimp
  field_simp
  ring

theorem smooth_radialJacobi (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (radialJacobi n b) := by
  exact (contDiff_const.mul
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))).div
      (contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ)))
      (fun x => ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖)))

theorem radialJacobi_pos {n : ℕ} {b : ℝ} (hb : 0 < b) (hbn : b < (n : ℝ))
    {x : E n} (hx : x ∈ closedUnitBall n) : 0 < radialJacobi n b x := by
  have hxnorm : ‖x‖ ≤ 1 := by simpa [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hx
  have hxnormsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hnum : 0 < (n : ℝ) - b * ‖x‖ ^ 2 := by nlinarith
  exact div_pos (mul_pos (by norm_num) hnum) (radial_denominator_pos hb (sq_nonneg ‖x‖))

theorem radialJacobi_equation (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    complexLaplacian (radialPotential n b) (radialJacobi n b) x + radialJacobi n b x = 0 := by
  change complexLaplacian (radialPotential n b)
    (fun y : E n => radialJacobiProfile n b (‖y‖ ^ 2)) x +
      radialJacobiProfile n b (‖x‖ ^ 2) = 0
  rw [complexLaplacian_radial_profile hb (fun t ht => hasDerivAt_radialJacobiProfile n hb ht)
    (hasDerivAt_radialJacobiSlopeProfile n hb (sq_nonneg ‖x‖))]
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hd : 1 + b * ‖x‖ ^ 2 ≠ 0 :=
    ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖))
  dsimp [radialJacobiProfile, radialJacobiSlopeProfile]
  field_simp
  ring

/-- The positive test function needed for comparison on the stable branch. -/
theorem stable_radialJacobi {n : ℕ} {b : ℝ} (hb : 0 < b) (hbn : b < (n : ℝ)) :
    SmoothNear (closedUnitBall n) (radialJacobi n b) ∧
      (∀ x ∈ closedUnitBall n, 0 < radialJacobi n b x) ∧
      (∀ x ∈ unitBall n,
        complexLaplacian (radialPotential n b) (radialJacobi n b) x + radialJacobi n b x = 0) := by
  exact ⟨⟨Set.univ, isOpen_univ, Set.subset_univ _, (smooth_radialJacobi n hb).contDiffOn⟩,
    fun _ hx => radialJacobi_pos hb hbn hx, fun x _ => radialJacobi_equation n hb x⟩

theorem partialZ_radialPotential (n : ℕ) {b : ℝ} (hb : 0 < b)
    (i : Fin n) (x : E n) :
    partialZ i (fun y => (radialPotential n b y : ℂ)) x =
      (radialSlopeProfile n b (‖x‖ ^ 2) : ℂ) * star (complexCoord x i) := by
  exact partialZ_ofReal_comp_norm_sq (hasDerivAt_radialProfile n hb (sq_nonneg ‖x‖)) i

lemma scalar_outer_contraction {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (a : ℂ) (z : ι → ℂ) :
    (∑ i : ι, ∑ j : ι, A j i * (a * star (z i)) * (a * z j)) =
      a ^ 2 * (A * Matrix.vecMulVec (star z) z).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem radial_gradientNormSq (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    gradientNormSq (radialPotential n b) x = (n + 1 : ℝ) * b * ‖x‖ ^ 2 := by
  have hq : gradientNormSq (radialPotential n b) x =
      ((radialSlopeProfile n b (‖x‖ ^ 2) : ℂ) ^ 2 *
        ((complexHessian (radialPotential n b) x)⁻¹ *
          Matrix.vecMulVec (star (complexCoord x)) (complexCoord x)).trace).re := by
    unfold gradientNormSq inverseCoefficient
    simp_rw [partialZ_radialPotential n hb, partialBar_radialPotential n hb]
    rw [scalar_outer_contraction]
  have htrace :
      ((complexHessian (radialPotential n b) x)⁻¹ *
        Matrix.vecMulVec (star (complexCoord x)) (complexCoord x)).trace =
        ((1 + b * ‖x‖ ^ 2) / ((n + 1 : ℝ) * b) *
          ‖x‖ ^ 2 * (1 + b * ‖x‖ ^ 2) : ℝ) := by
    rw [radial_complexHessian_inverse n hb]
    simp only [Matrix.smul_mul, add_mul, Matrix.one_mul, radial_rank_one_square,
      Matrix.trace_smul, Matrix.trace_add, radial_outer_trace, smul_smul, smul_eq_mul]
    push_cast
    ring
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hd : 1 + b * ‖x‖ ^ 2 ≠ 0 :=
    ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖))
  have hreal : (radialSlopeProfile n b (‖x‖ ^ 2)) ^ 2 *
      ((1 + b * ‖x‖ ^ 2) / ((n + 1 : ℝ) * b) * ‖x‖ ^ 2 * (1 + b * ‖x‖ ^ 2)) =
      (n + 1 : ℝ) * b * ‖x‖ ^ 2 := by
    dsimp [radialSlopeProfile]
    field_simp
  rw [hq, htrace]
  have hc : (radialSlopeProfile n b (‖x‖ ^ 2) : ℂ) ^ 2 *
      ((1 + b * ‖x‖ ^ 2) / ((n + 1 : ℝ) * b) * ‖x‖ ^ 2 * (1 + b * ‖x‖ ^ 2) : ℝ) =
      ((n + 1 : ℝ) * b * ‖x‖ ^ 2 : ℝ) := by exact_mod_cast hreal
  rw [hc]
  rfl

theorem radial_expWeight (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    expWeight (radialPotential n b) x = (1 + b) / (1 + b * ‖x‖ ^ 2) := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hp : 0 < (1 + b * ‖x‖ ^ 2) / (1 + b) :=
    div_pos (radial_denominator_pos hb (sq_nonneg ‖x‖)) (by positivity)
  have harg : -((n + 1 : ℝ) * Real.log ((1 + b * ‖x‖ ^ 2) / (1 + b))) / (n + 1 : ℝ) =
      -Real.log ((1 + b * ‖x‖ ^ 2) / (1 + b)) := by
    field_simp
  rw [expWeight, radialPotential, harg, Real.exp_neg, Real.exp_log hp, inv_div]

theorem radial_auxiliaryP (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    auxiliaryP (radialPotential n b) x = 1 + b := by
  rw [auxiliaryP, radial_expWeight n hb, radial_gradientNormSq n hb]
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hd : 1 + b * ‖x‖ ^ 2 ≠ 0 :=
    ne_of_gt (radial_denominator_pos hb (sq_nonneg ‖x‖))
  field_simp

theorem radial_auxiliaryW (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    auxiliaryW (radialPotential n b) x = Real.log b := by
  simp [auxiliaryW, radial_auxiliaryP n hb]

end KEBall
