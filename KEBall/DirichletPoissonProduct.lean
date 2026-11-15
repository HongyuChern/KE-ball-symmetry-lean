import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The product identity for the actual Euclidean Laplacian. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped ContDiff Laplacian

noncomputable section

namespace KEBall

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem euclideanLaplacian_mul_of_contDiff
    {c u : V → ℝ} (hc : ContDiff ℝ ∞ c) (hu : ContDiff ℝ ∞ u) (x : V) :
    Δ (fun y => c y * u y) x = c x * Δ u x + u x * Δ c x +
      2 * ∑ i : Fin (Module.finrank ℝ V),
        fderiv ℝ c x ((stdOrthonormalBasis ℝ V) i) *
          fderiv ℝ u x ((stdOrthonormalBasis ℝ V) i) := by
  have hc1 := hc.fderiv_right (m := ∞) (by simp)
  have hu1 := hu.fderiv_right (m := ∞) (by simp)
  have hfirst : fderiv ℝ (fun y => c y * u y) =
      fun y => c y • fderiv ℝ u y + (fderiv ℝ c y).smulRight (u y) := by
    funext y
    exact ((hc.differentiable (by simp) y).hasFDerivAt.smul
      (hu.differentiable (by simp) y).hasFDerivAt).fderiv
  have hleft := (hc.differentiable (by simp) x).hasFDerivAt.smul
    (hu1.differentiable (by simp) x).hasFDerivAt
  have hright := (ContinuousLinearMap.smulRightL ℝ V ℝ).hasFDerivAt_of_bilinear
    (hc1.differentiable (by simp) x).hasFDerivAt
    (hu.differentiable (by simp) x).hasFDerivAt
  have hsecond := hleft.add hright
  have hfun : (c • fderiv ℝ u + fun y =>
      (ContinuousLinearMap.smulRightL ℝ V ℝ) (fderiv ℝ c y) (u y)) =
      (fun y => c y • fderiv ℝ u y + (fderiv ℝ c y).smulRight (u y)) := by
    funext y
    rfl
  rw [hfun] at hsecond
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hfirst, hsecond.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.precompR, ContinuousLinearMap.precompL,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRightL_apply_apply,
    smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem norm_euclideanLaplacian_mul_le
    {c u : V → ℝ} (hc : ContDiff ℝ ∞ c) (hu : ContDiff ℝ ∞ u) (x : V) :
    ‖Δ (fun y => c y * u y) x‖ ≤
      ‖c x‖ * ‖Δ u x‖ + ‖u x‖ * ‖Δ c x‖ +
        2 * (Module.finrank ℝ V : ℝ) * ‖fderiv ℝ c x‖ * ‖fderiv ℝ u x‖ := by
  have hsum : ‖∑ i : Fin (Module.finrank ℝ V),
      fderiv ℝ c x ((stdOrthonormalBasis ℝ V) i) *
        fderiv ℝ u x ((stdOrthonormalBasis ℝ V) i)‖ ≤
      (Module.finrank ℝ V : ℝ) * ‖fderiv ℝ c x‖ * ‖fderiv ℝ u x‖ := by
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ V), ‖fderiv ℝ c x‖ * ‖fderiv ℝ u x‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul]
        have hcB := (fderiv ℝ c x).le_opNorm ((stdOrthonormalBasis ℝ V) i)
        have huB := (fderiv ℝ u x).le_opNorm ((stdOrthonormalBasis ℝ V) i)
        rw [(stdOrthonormalBasis ℝ V).orthonormal.norm_eq_one i, mul_one] at hcB huB
        exact mul_le_mul hcB huB (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  rw [euclideanLaplacian_mul_of_contDiff hc hu]
  calc
    _ ≤ ‖c x * Δ u x‖ + ‖u x * Δ c x‖ +
        ‖2 * ∑ i : Fin (Module.finrank ℝ V),
          fderiv ℝ c x ((stdOrthonormalBasis ℝ V) i) *
            fderiv ℝ u x ((stdOrthonormalBasis ℝ V) i)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_mul, Real.norm_ofNat]
      nlinarith only [hsum]

end KEBall
