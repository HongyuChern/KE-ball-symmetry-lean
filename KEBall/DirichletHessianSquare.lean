import KEBall.DirichletBilinearContraction
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The positive quadratic term in the real cofactor operator applied to
the square of an actual directional derivative. -/

set_option autoImplicit false
set_option maxHeartbeats 600000

open InnerProductSpace
open scoped BigOperators ContDiff

noncomputable section

namespace KEBall

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι]

theorem fderiv_fderiv_square_of_contDiff {q : V → ℝ}
    (hq : ContDiff ℝ ∞ q) (x : V) :
    fderiv ℝ (fderiv ℝ (fun y => q y * q y)) x =
      (2 * q x) • fderiv ℝ (fderiv ℝ q) x +
        (2 : ℝ) • (fderiv ℝ q x).smulRight (fderiv ℝ q x) := by
  have hq1 := hq.fderiv_right (m := ∞) (by simp)
  have hfirst : fderiv ℝ (fun y => q y * q y) =
      fun y => q y • fderiv ℝ q y + (fderiv ℝ q y).smulRight (q y) := by
    funext y
    exact ((hq.differentiable (by simp) y).hasFDerivAt.smul
      (hq.differentiable (by simp) y).hasFDerivAt).fderiv
  have hleft := (hq.differentiable (by simp) x).hasFDerivAt.smul
    (hq1.differentiable (by simp) x).hasFDerivAt
  have hright := (ContinuousLinearMap.smulRightL ℝ V ℝ).hasFDerivAt_of_bilinear
    (hq1.differentiable (by simp) x).hasFDerivAt
    (hq.differentiable (by simp) x).hasFDerivAt
  have hsecond := hleft.add hright
  have hfun : (q • fderiv ℝ q + fun y =>
      (ContinuousLinearMap.smulRightL ℝ V ℝ) (fderiv ℝ q y) (q y)) =
      (fun y => q y • fderiv ℝ q y + (fderiv ℝ q y).smulRight (q y)) := by
    funext y
    rfl
  rw [hfun] at hsecond
  rw [hfirst, hsecond.fderiv]
  ext v w
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.precompR, ContinuousLinearMap.precompL,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRightL_apply_apply,
    smul_eq_mul]
  ring

theorem dirichletBilinearContraction_dualSquare
    (b : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V) (L : V →L[ℝ] ℝ) :
    dirichletBilinearContraction b A (L.smulRight L) =
      inner ℝ (A ((toDual ℝ V).symm L)) ((toDual ℝ V).symm L) := by
  let g := (toDual ℝ V).symm L
  have hL (v : V) : L v = inner ℝ g v := toDual_symm_apply.symm
  unfold dirichletBilinearContraction
  simp only [ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  calc
    (∑ i : ι, L (A (b i)) * L (b i)) = L (A (∑ i : ι, inner ℝ (b i) g • b i)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [hL (b i), real_inner_comm (b i) g]
      ring
    _ = inner ℝ (A g) g := by rw [b.sum_repr', hL, real_inner_comm]

theorem dirichletBilinearContraction_dualSquare_ge
    (b : OrthonormalBasis ι ℝ V) {A : V →L[ℝ] V} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ z : V, c * ‖z‖ ^ 2 ≤ inner ℝ (A z) z)
    (L : V →L[ℝ] ℝ) {v : V} (hv : ‖v‖ = 1) :
    c * (L v) ^ 2 ≤ dirichletBilinearContraction b A (L.smulRight L) := by
  rw [dirichletBilinearContraction_dualSquare]
  let g := (toDual ℝ V).symm L
  have hLV : |L v| ≤ ‖g‖ := by
    rw [← toDual_symm_apply]
    exact (abs_real_inner_le_norm g v).trans_eq (by rw [hv, mul_one])
  have hSq : (L v) ^ 2 ≤ ‖g‖ ^ 2 := by
    nlinarith [sq_abs (L v), abs_nonneg (L v), norm_nonneg g]
  exact (mul_le_mul_of_nonneg_left hSq hc).trans (hA g)

theorem dirichletBilinearContraction_square
    (b : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V)
    {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (x : V) :
    dirichletBilinearContraction b A
      (fderiv ℝ (fderiv ℝ (fun y => q y * q y)) x) =
        2 * q x * dirichletBilinearContraction b A (fderiv ℝ (fderiv ℝ q) x) +
        2 * dirichletBilinearContraction b A ((fderiv ℝ q x).smulRight (fderiv ℝ q x)) := by
  rw [fderiv_fderiv_square_of_contDiff hq]
  simp only [dirichletBilinearContraction, add_apply, smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

end KEBall
