import KEBall.RealHessian
import KEBall.ComplexFlux
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Algebra.Order.Chebyshev

/-! The Euclidean Laplacian and the trace of the complex Hessian. -/

set_option autoImplicit false

open MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Laplacian

namespace KEBall

theorem euclideanLaplacian_eq_four_complexHessian_trace_re {n : ℕ}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x) :
    Δ u x = 4 * (complexHessian u x).trace.re := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)]
  dsimp only
  rw [← (interleavedEquiv n).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, interleavedEquiv_zero,
    interleavedEquiv_one, EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.trace, Matrix.diag, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change realHessian u x (realDirection i) (realDirection i) +
    realHessian u x (imagDirection i) (imagDirection i) = 4 * (complexHessian u x i i).re
  rw [complexHessian_real_entry hu, realHessian_symm hu (realDirection i) (imagDirection i), sub_self]
  simp [Complex.mul_re, Complex.inv_re]

private theorem sq_trace_re_le {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    H.trace.re ^ 2 ≤ (n : ℝ) * ∑ i, ∑ j, ‖H i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  calc
    _ ≤ (n : ℝ) * ∑ i, (H i i).re ^ 2 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => (H i i).re))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      have hRe : (H i i).re ^ 2 ≤ ‖H i i‖ ^ 2 := by
        rw [← sq_abs ((H i i).re)]
        exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
      exact hRe.trans (Finset.single_le_sum (f := fun j => ‖H i j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- The real Laplacian difference is controlled in (L²) by the complex Hessian
difference, with the same volume normalization. -/
theorem integral_sq_euclideanLaplacian_sub_le {n : ℕ} (hn : 0 < n)
    {u v : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hv : SmoothNear (closedUnitBall n) v) :
    (∫ x in unitBall n, (Δ v x - Δ u x) ^ 2 ∂volume0 n) ≤
      (16 * n : ℝ) * ∫ x in unitBall n, ∑ i, ∑ j,
        ‖(complexHessian v x - complexHessian u x) i j‖ ^ 2 ∂volume0 n := by
  let μ := (volume0 n).restrict (unitBall n)
  let H (x : E n) := complexHessian v x - complexHessian u x
  let q (x : E n) : ℝ := ∑ i, ∑ j, ‖H x i j‖ ^ 2
  let p (x : E n) : ℝ := (Δ v x - Δ u x) ^ 2
  have huC (i j : Fin n) : ContinuousOn (fun x => complexHessian u x i j) (closedUnitBall n) := by
    obtain ⟨U, hU, hSub, huU⟩ := hu
    exact (complexHessian_contDiffOn hU huU i j).continuousOn.mono hSub
  have hvC (i j : Fin n) : ContinuousOn (fun x => complexHessian v x i j) (closedUnitBall n) := by
    obtain ⟨U, hU, hSub, hvU⟩ := hv
    exact (complexHessian_contDiffOn hU hvU i j).continuousOn.mono hSub
  have hI {w : E n → ℝ} (hw : ContinuousOn w (closedUnitBall n)) : Integrable w μ :=
    hw.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hQ : ContinuousOn q (closedUnitBall n) :=
    continuousOn_finsetSum Finset.univ fun i _ => continuousOn_finsetSum Finset.univ fun j _ =>
      (((hvC i j).sub (huC i j)).norm).pow 2
  have he (x : E n) (hx : x ∈ closedUnitBall n) : Δ v x - Δ u x = 4 * (H x).trace.re := by
    rw [euclideanLaplacian_eq_four_complexHessian_trace_re (hv.contDiffAt hx),
      euclideanLaplacian_eq_four_complexHessian_trace_re (hu.contDiffAt hx)]
    simp only [H, Matrix.trace_sub, Complex.sub_re, mul_sub]
  have hP : ContinuousOn p (closedUnitBall n) := by
    have hC : ContinuousOn (fun x => (H x).trace.re) (closedUnitBall n) := by
      apply Complex.continuous_re.comp_continuousOn
      simp only [Matrix.trace, Matrix.diag]
      exact continuousOn_finsetSum Finset.univ fun i _ => (hvC i i).sub (huC i i)
    exact ((continuousOn_const (c := (4 : ℝ))).mul hC |>.pow 2).congr
      fun x hx => congrArg (fun a : ℝ => a ^ 2) (he x hx)
  have hPoint : p ≤ᵐ[μ] fun x => (16 * n : ℝ) * q x := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    change (Δ v x - Δ u x) ^ 2 ≤ _
    rw [he x (ball_subset_closedBall hx), mul_pow]
    have h := mul_le_mul_of_nonneg_left (sq_trace_re_le (H x)) (show (0 : ℝ) ≤ 4 ^ 2 by norm_num)
    exact h.trans_eq (by dsimp [q]; ring)
  have h := integral_mono_ae (hI hP) ((hI hQ).const_mul (16 * n : ℝ)) hPoint
  rw [integral_const_mul] at h
  exact h

end KEBall
