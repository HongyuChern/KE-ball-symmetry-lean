import KEBall.DirichletNormalRecovery

/-!
# Uniqueness of a boundary Hessian from its tangent entries

For symmetric real forms the missing entry is a single radial rank-one
coefficient.  The positive complex Hessian makes the determinant strictly
increasing in that coefficient, with the project's factor of 1/4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped ComplexOrder Matrix

namespace KEBall

theorem dirichlet_bilinear_difference_eq_radial_rankOne {n : ℕ}
    {B C : E n →L[ℝ] E n →L[ℝ] ℝ} {p : E n}
    (hp : p ∈ unitSphere n)
    (hB : ∀ v w, B v w = B w v) (hC : ∀ v w, C v w = C w v)
    (hTan : ∀ v, inner ℝ p v = 0 → B v = C v) :
    B = C + (B p p - C p p) • (innerSL ℝ p).smulRight (innerSL ℝ p) := by
  have hpp : inner ℝ p p = 1 := by
    rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp hp, one_pow]
  have hOrth (v : E n) : inner ℝ p (v - inner ℝ p v • p) = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hpp, mul_one, sub_self]
  have hEval (v w : E n) : B v w - C v w = inner ℝ p v * (B p w - C p w) := by
    have h := congrArg (fun D : E n →L[ℝ] ℝ => D w) (hTan _ (hOrth v))
    simp only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply, smul_eq_mul] at h
    nlinarith only [h]
  ext v w
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul]
  have h₁ := hEval v w
  have h₂ := hEval w p
  rw [hB w p, hC w p] at h₂
  rw [h₂] at h₁
  nlinarith only [h₁]

theorem dirichlet_symmetric_bilinear_eq_of_tangent_det {n : ℕ}
    {B C : E n →L[ℝ] E n →L[ℝ] ℝ} {p : E n}
    (hp : p ∈ unitSphere n)
    (hB : ∀ v w, B v w = B w v) (hC : ∀ v w, C v w = C w v)
    (hTan : ∀ v, inner ℝ p v = 0 → B v = C v)
    (hPos : (complexHessianOfRealBilinear C).PosDef)
    (hDet : (complexHessianOfRealBilinear B).det.re =
      (complexHessianOfRealBilinear C).det.re) : B = C := by
  have hSplit := dirichlet_bilinear_difference_eq_radial_rankOne hp hB hC hTan
  have hp0 : p ≠ 0 := by
    intro he
    have h := mem_sphere_zero_iff_norm.mp hp
    simp [he] at h
  have hz : star (complexCoord p) ≠ 0 := by
    intro he
    apply hp0
    apply complexCoord_eq_zero_iff.mp
    have h := congrArg star he
    simpa only [star_star, star_zero] using h
  have hMatrix : complexHessianOfRealBilinear B = complexHessianOfRealBilinear C +
      (((B p p - C p p) / 4 : ℝ) : ℂ) •
        Matrix.vecMulVec (star (complexCoord p)) (star (star (complexCoord p))) := by
    calc
      complexHessianOfRealBilinear B = complexHessianOfRealBilinear
          (C + (B p p - C p p) • (innerSL ℝ p).smulRight (innerSL ℝ p)) :=
        congrArg complexHessianOfRealBilinear hSplit
      _ = _ := by
        simpa only [star_star] using
          complexHessianOfRealBilinear_add_rankOne C p (B p p - C p p)
  have hCoeff := real_rankOne_coefficient_eq_of_det hPos hz hMatrix
  rw [hDet, sub_self, zero_div] at hCoeff
  have he : B p p - C p p = 0 := by linarith only [hCoeff]
  rw [hSplit, he, zero_smul, add_zero]

theorem dirichlet_bilinear_tangent_eq_of_unit_tangent_eq {n : ℕ}
    {B C : E n →L[ℝ] E n →L[ℝ] ℝ} {p : E n}
    (hTan : ∀ v, ‖v‖ = 1 → inner ℝ p v = 0 → B v = C v) :
    ∀ v, inner ℝ p v = 0 → B v = C v := by
  intro v hv
  by_cases he : v = 0
  · simp [he]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr he
  let z : E n := ‖v‖⁻¹ • v
  have hz : ‖z‖ = 1 := by
    simp only [z, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ hn
  have hzOrth : inner ℝ p z = 0 := by simp [z, real_inner_smul_right, hv]
  have h := hTan z hz hzOrth
  have hvz : v = ‖v‖ • z := by simp [z, smul_smul, hn]
  calc
    B v = B (‖v‖ • z) := congrArg B hvz
    _ = ‖v‖ • B z := B.map_smul ‖v‖ z
    _ = ‖v‖ • C z := congrArg (fun D : E n →L[ℝ] ℝ => ‖v‖ • D) h
    _ = C (‖v‖ • z) := (C.map_smul ‖v‖ z).symm
    _ = C v := congrArg C hvz.symm

end KEBall
