import KEBall.DirichletInteriorMaximum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Explicit radial barriers for the actual elliptic contraction

The Hessian and its contraction are calculated with the project's real
Fréchet derivative and orthonormal basis.  These identities are used for
local boundary comparison; no boundary regularity is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Metric Set
open scoped BigOperators ContDiff Topology

noncomputable section

namespace KEBall

def dirichletRadialExponential {n : ℕ} (κ : ℝ) (z x : E n) : ℝ :=
  Real.exp (-κ * ‖x - z‖ ^ 2)

theorem contDiff_dirichletRadialExponential {n : ℕ} (κ : ℝ) (z : E n) :
    ContDiff ℝ ∞ (dirichletRadialExponential κ z) :=
  (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ))).exp

theorem hasFDerivAt_dirichletRadialExponential {n : ℕ} (κ : ℝ) (z x : E n) :
    HasFDerivAt (dirichletRadialExponential κ z)
      ((-2 * κ * dirichletRadialExponential κ z x) • innerSL ℝ (x - z)) x := by
  have hN : HasFDerivAt (fun y : E n => ‖y - z‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ (x - z)) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq, two_smul] using!
      (hasStrictFDerivAt_norm_sq (x - z)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const z)
  have h := (hN.const_mul (-κ)).exp
  change HasFDerivAt (dirichletRadialExponential κ z)
    (dirichletRadialExponential κ z x • (-κ • ((2 : ℝ) • innerSL ℝ (x - z)))) x at h
  have he : dirichletRadialExponential κ z x • (-κ • ((2 : ℝ) • innerSL ℝ (x - z))) =
      (-2 * κ * dirichletRadialExponential κ z x) • innerSL ℝ (x - z) := by
    rw [smul_smul, smul_smul]
    congr 1
    ring
  rwa [he] at h

theorem realHessian_dirichletRadialExponential {n : ℕ}
    (κ : ℝ) (z x v w : E n) :
    realHessian (dirichletRadialExponential κ z) x v w =
      dirichletRadialExponential κ z x *
        (4 * κ ^ 2 * inner ℝ (x - z) v * inner ℝ (x - z) w -
          2 * κ * inner ℝ v w) := by
  have hE : fderiv ℝ (dirichletRadialExponential κ z) =
      fun y => (-2 * κ * dirichletRadialExponential κ z y) • innerSL ℝ (y - z) := by
    funext y
    exact (hasFDerivAt_dirichletRadialExponential κ z y).fderiv
  have hC := (hasFDerivAt_dirichletRadialExponential κ z x).const_mul (-2 * κ)
  have hZ : HasFDerivAt (fun y : E n => innerSL ℝ (y - z)) (innerSL ℝ) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using!
      (innerSL ℝ (E := E n)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
  have h := hC.smul hZ
  change HasFDerivAt
    (fun y => (-2 * κ * dirichletRadialExponential κ z y) • innerSL ℝ (y - z)) _ x at h
  rw [← hE] at h
  rw [realHessian, h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul]
  change (-2 * κ * dirichletRadialExponential κ z x) * inner ℝ v w +
    ((-2 * κ) * ((-2 * κ * dirichletRadialExponential κ z x) * inner ℝ (x - z) v)) *
      inner ℝ (x - z) w = _
  ring

theorem dirichletBilinearContraction_radialExponential {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (A : E n →L[ℝ] E n) (κ : ℝ) (z x : E n) :
    dirichletBilinearContraction b A (realHessian (dirichletRadialExponential κ z) x) =
      dirichletRadialExponential κ z x *
        (4 * κ ^ 2 * inner ℝ (A (x - z)) (x - z) -
          2 * κ * ∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i)) := by
  have hPair : (∑ i : Fin (2 * n), inner ℝ (x - z) (A (b i)) *
      inner ℝ (x - z) (b i)) = inner ℝ (A (x - z)) (x - z) := by
    have h := congrArg (fun q : E n => inner ℝ (A q) (x - z)) (b.sum_repr' (x - z))
    simp only [map_sum, map_smul, sum_inner, real_inner_smul_left] at h
    simpa only [real_inner_comm (x - z), mul_comm] using h
  unfold dirichletBilinearContraction
  simp only [realHessian_dirichletRadialExponential]
  rw [← hPair]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]

end KEBall
