import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A holomorphic involution interchanging the origin and a point of a ball

The formula is smooth in the center parameter even at the origin.
-/

set_option autoImplicit false

open Metric Set
open scoped ComplexConjugate ContDiff InnerProductSpace

namespace KEBall

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private noncomputable def ballInvolutionScale (a : H) : ℝ :=
  Real.sqrt (1 - ‖a‖ ^ 2)

omit [InnerProductSpace ℂ H] in
private theorem ballInvolutionScale_pos {a : H} (ha : ‖a‖ < 1) :
    0 < ballInvolutionScale a :=
  Real.sqrt_pos.mpr (sub_pos.mpr (by nlinarith only [ha, norm_nonneg a]))

omit [InnerProductSpace ℂ H] in
private theorem ballInvolutionScale_sq {a : H} (ha : ‖a‖ < 1) :
    ballInvolutionScale a ^ 2 = 1 - ‖a‖ ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr (by nlinarith only [ha, norm_nonneg a]))

/-- The standard map of the complex unit ball interchanging the origin and
its center parameter. -/
noncomputable def complexBallInvolution (a z : H) : H :=
  let s := ballInvolutionScale a
  let b := ((1 + s : ℝ) : ℂ)
  let t := ⟪a, z⟫_ℂ
  (b * (1 - t))⁻¹ • ((b - t) • a - ((s : ℂ) * b) • z)

private theorem one_sub_inner_ne_zero {a z : H} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    (1 : ℂ) - ⟪a, z⟫_ℂ ≠ 0 := by
  have ht := (norm_inner_le_norm (𝕜 := ℂ) a z).trans
    (mul_le_of_le_one_right (norm_nonneg a) hz)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at ht
  exact (not_le_of_gt ha) ht

private theorem normSq_ballInvolutionNumerator {a z : H} (ha : ‖a‖ < 1) :
    let s := ballInvolutionScale a
    let b := ((1 + s : ℝ) : ℂ)
    let t := ⟪a, z⟫_ℂ
    ‖(b - t) • a - ((s : ℂ) * b) • z‖ ^ 2 =
      (1 + s) ^ 2 * (‖(1 : ℂ) - t‖ ^ 2 - s ^ 2 * (1 - ‖z‖ ^ 2)) := by
  let s := ballInvolutionScale a
  let b := ((1 + s : ℝ) : ℂ)
  let t := ⟪a, z⟫_ℂ
  change ‖(b - t) • a - ((s : ℂ) * b) • z‖ ^ 2 =
    (1 + s) ^ 2 * (‖(1 : ℂ) - t‖ ^ 2 - s ^ 2 * (1 - ‖z‖ ^ 2))
  have hs : ‖a‖ ^ 2 = 1 - s ^ 2 := by linarith only [ballInvolutionScale_sq ha]
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right]
  change ‖(b - t) • a‖ ^ 2 -
    2 * (conj (b - t) * (((s : ℂ) * b) * t)).re +
    ‖((s : ℂ) * b) • z‖ ^ 2 = _
  simp only [norm_smul, mul_pow, Complex.sq_norm, Complex.normSq_apply,
    b, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  rw [hs]
  ring

/-- The exact norm identity of the ball involution. -/
theorem one_sub_normSq_complexBallInvolution {a z : H}
    (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - ‖complexBallInvolution a z‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖(1 : ℂ) - ⟪a, z⟫_ℂ‖ ^ 2 := by
  let s := ballInvolutionScale a
  have hb : 0 < 1 + s := by linarith only [ballInvolutionScale_pos ha]
  have hd : ‖(1 : ℂ) - ⟪a, z⟫_ℂ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (one_sub_inner_ne_zero ha hz)
  unfold complexBallInvolution
  rw [norm_smul, mul_pow, norm_inv, normSq_ballInvolutionNumerator ha, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, ← ballInvolutionScale_sq ha]
  change 1 - ((1 + s) * ‖(1 : ℂ) - ⟪a, z⟫_ℂ‖)⁻¹ ^ 2 * _ = _
  field_simp [hb.ne', hd]
  ring

theorem complexBallInvolution_mapsTo_unitBall {a : H} (ha : ‖a‖ < 1) :
    MapsTo (complexBallInvolution a) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz ⊢
  have h := one_sub_normSq_complexBallInvolution ha hz.le
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖(1 : ℂ) - ⟪a, z⟫_ℂ‖ ^ 2 := by
    rw [← ballInvolutionScale_sq ha, ← ballInvolutionScale_sq hz]
    exact div_pos (mul_pos (pow_pos (ballInvolutionScale_pos ha) _) (pow_pos (ballInvolutionScale_pos hz) _))
      (pow_pos (norm_pos_iff.mpr (one_sub_inner_ne_zero ha hz.le)) _)
  nlinarith only [h, hpos, norm_nonneg (complexBallInvolution a z)]

theorem complexBallInvolution_mapsTo_closedUnitBall {a : H} (ha : ‖a‖ < 1) :
    MapsTo (complexBallInvolution a) (closedBall 0 1) (closedBall 0 1) := by
  intro z hz
  rw [mem_closedBall, dist_zero_right] at hz ⊢
  have h := one_sub_normSq_complexBallInvolution ha hz
  have hnonneg : 0 ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖(1 : ℂ) - ⟪a, z⟫_ℂ‖ ^ 2 :=
    div_nonneg (mul_nonneg (by nlinarith only [ha, norm_nonneg a])
      (by nlinarith only [hz, norm_nonneg z])) (sq_nonneg _)
  nlinarith only [h, hnonneg, norm_nonneg (complexBallInvolution a z)]

theorem complexBallInvolution_zero {a : H} (ha : ‖a‖ < 1) :
    complexBallInvolution a 0 = a := by
  have hb : ((1 + ballInvolutionScale a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 + ballInvolutionScale a : ℝ) ≠ 0 from by
      linarith only [ballInvolutionScale_pos ha])
  simp only [complexBallInvolution, inner_zero_right, sub_zero, mul_one, smul_zero,
    smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem complexBallInvolution_center {a : H} (ha : ‖a‖ < 1) :
    complexBallInvolution a a = 0 := by
  let s := ballInvolutionScale a
  have h : (‖a‖ : ℂ) ^ 2 = 1 - (s : ℂ) ^ 2 := by
    exact_mod_cast (show ‖a‖ ^ 2 = 1 - s ^ 2 by linarith only [ballInvolutionScale_sq ha])
  simp only [complexBallInvolution, inner_self_eq_norm_sq_to_K, ← sub_smul,
    Complex.ofReal_add, Complex.ofReal_one]
  change (((1 + (s : ℂ)) * (1 - (‖a‖ : ℂ) ^ 2))⁻¹) •
    (((1 + (s : ℂ)) - (‖a‖ : ℂ) ^ 2 - (s : ℂ) * (1 + (s : ℂ))) • a) = 0
  rw [h, show (1 + (s : ℂ) - (1 - (s : ℂ) ^ 2) - (s : ℂ) * (1 + (s : ℂ))) = 0 by ring,
    zero_smul, smul_zero]

/-- Applying the ball involution twice recovers the original point,
including on the unit sphere. -/
theorem complexBallInvolution_involutive {a z : H} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    complexBallInvolution a (complexBallInvolution a z) = z := by
  let s := ballInvolutionScale a
  let b := ((1 + s : ℝ) : ℂ)
  let t := ⟪a, z⟫_ℂ
  let k := (b * (1 - t))⁻¹
  let w := complexBallInvolution a z
  let t' := ⟪a, w⟫_ℂ
  have hb : b = 1 + (s : ℂ) := by simp [b]
  have hb₀ : b ≠ 0 := by
    change ((1 + s : ℝ) : ℂ) ≠ 0
    exact_mod_cast (show (1 + s : ℝ) ≠ 0 from by linarith only [ballInvolutionScale_pos ha])
  have hs₀ : (s : ℂ) ≠ 0 := by exact_mod_cast (ballInvolutionScale_pos ha).ne'
  have hd : 1 - t ≠ 0 := one_sub_inner_ne_zero ha hz
  have hA : (‖a‖ : ℂ) ^ 2 = 1 - (s : ℂ) ^ 2 := by
    exact_mod_cast (show ‖a‖ ^ 2 = 1 - s ^ 2 by linarith only [ballInvolutionScale_sq ha])
  have hw : w = k • ((b - t) • a - ((s : ℂ) * b) • z) := rfl
  have ht' : t' = ((‖a‖ : ℂ) ^ 2 - t) / (1 - t) := by
    change ⟪a, w⟫_ℂ = _
    rw [hw, inner_smul_right, inner_sub_right, inner_smul_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    change k * ((b - t) * (‖a‖ : ℂ) ^ 2 - (s : ℂ) * b * t) = _
    dsimp only [k]
    rw [hA, hb]
    field_simp [hd, hb ▸ hb₀]
    ring
  have hD : 1 - t' = (s : ℂ) ^ 2 / (1 - t) := by
    rw [ht', hA]
    field_simp [hd]
    ring
  have hN : b - t' = (s : ℂ) * (b - t) / (1 - t) := by
    rw [ht', hA, hb]
    field_simp [hd]
    ring
  have hmul : ((s : ℂ) * b) * k = (s : ℂ) / (1 - t) := by
    dsimp only [k]
    field_simp [hb₀, hd]
  have hcoeff : (s : ℂ) / (1 - t) * (b - t) = (s : ℂ) * (b - t) / (1 - t) := by ring
  have hres : (s : ℂ) / (1 - t) * ((s : ℂ) * b) = b * ((s : ℂ) ^ 2 / (1 - t)) := by ring
  have hW : ((s : ℂ) * b) • w =
      ((s : ℂ) * (b - t) / (1 - t)) • a - (b * ((s : ℂ) ^ 2 / (1 - t))) • z := by
    rw [hw, smul_smul, hmul, smul_sub, smul_smul, smul_smul, hcoeff, hres]
  change (b * (1 - t'))⁻¹ • ((b - t') • a - ((s : ℂ) * b) • w) = z
  rw [hD, hN, hW,
    sub_sub_cancel, smul_smul, inv_mul_cancel₀ (mul_ne_zero hb₀ (div_ne_zero (pow_ne_zero _ hs₀) hd)),
    one_smul]

theorem differentiableAt_complexBallInvolution {a z : H} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    DifferentiableAt ℂ (complexBallInvolution a) z := by
  let s := ballInvolutionScale a
  let b := ((1 + s : ℝ) : ℂ)
  have hb : b ≠ 0 := by
    change ((1 + s : ℝ) : ℂ) ≠ 0
    exact_mod_cast (show (1 + s : ℝ) ≠ 0 from by linarith only [ballInvolutionScale_pos ha])
  have ht : DifferentiableAt ℂ (fun y => ⟪a, y⟫_ℂ) z := (innerSL ℂ a).differentiableAt
  have hD := (differentiableAt_const (c := b)).mul ((differentiableAt_const (c := (1 : ℂ))).sub ht)
  have hD' := hD.inv (mul_ne_zero hb (one_sub_inner_ne_zero ha hz))
  have hN := (((differentiableAt_const (c := b)).sub ht).smul
    (differentiableAt_const (c := a))).sub (differentiableAt_id.const_smul ((s : ℂ) * b))
  exact hD'.smul hN

theorem differentiableOn_complexBallInvolution {a : H} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (complexBallInvolution a) (ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := (show ‖z‖ < 1 by simpa only [mem_ball, dist_zero_right] using hz).le
  exact (differentiableAt_complexBallInvolution ha hz').differentiableWithinAt

/-- The ball involution depends smoothly on both variables on a neighborhood
of every pair with center parameter inside the ball and argument in its closure. -/
theorem contDiffAt_complexBallInvolution [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    {a z : H} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ContDiffAt ℝ ∞ (fun p : H × H => complexBallInvolution p.1 p.2) (a, z) := by
  let s (p : H × H) := ballInvolutionScale p.1
  let b (p : H × H) := ((1 + s p : ℝ) : ℂ)
  let t (p : H × H) := ⟪p.1, p.2⟫_ℂ
  have hs : ContDiffAt ℝ ∞ s (a, z) := by
    have h : ContDiff ℝ ∞ (fun p : H × H => 1 - ‖p.1‖ ^ 2) :=
      contDiff_const.sub ((contDiff_norm_sq ℂ).comp contDiff_fst)
    exact h.contDiffAt.sqrt (by
      change 1 - ‖a‖ ^ 2 ≠ 0
      linarith only [ballInvolutionScale_sq ha, pow_pos (ballInvolutionScale_pos ha) 2])
  have hsC : ContDiffAt ℝ ∞ (fun p : H × H => (s p : ℂ)) (a, z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (a, z) hs
  have hb : ContDiffAt ℝ ∞ b (a, z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (a, z) (contDiffAt_const.add hs)
  have hb₀ : b (a, z) ≠ 0 := by
    change ((1 + ballInvolutionScale a : ℝ) : ℂ) ≠ 0
    exact_mod_cast (show (1 + ballInvolutionScale a : ℝ) ≠ 0 from by
      linarith only [ballInvolutionScale_pos ha])
  have ht : ContDiffAt ℝ ∞ t (a, z) := contDiffAt_inner
  have hD := hb.mul ((contDiffAt_const (c := (1 : ℂ))).sub ht)
  have hD' := hD.inv (mul_ne_zero hb₀ (one_sub_inner_ne_zero ha hz))
  have hN := ((hb.sub ht).smul contDiff_fst.contDiffAt).sub
    ((hsC.mul hb).smul contDiff_snd.contDiffAt)
  exact hD'.smul hN

end KEBall
