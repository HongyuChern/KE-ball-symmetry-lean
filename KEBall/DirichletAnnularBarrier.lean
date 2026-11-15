import KEBall.DirichletRadialBarrierEstimate

/-!
# Quantitative size and source correction of the annular barrier

The positive exponential barrier vanishes on the outer sphere.  A quadratic
term corrects a bounded nonzero source, with the real dimension retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped BigOperators ContDiff

noncomputable section

namespace KEBall

def dirichletAnnularBarrier {n : ℕ} (κ R : ℝ) (z x : E n) : ℝ :=
  dirichletRadialExponential κ z x - Real.exp (-κ * R ^ 2)

theorem dirichletAnnularBarrier_zero_on_sphere {n : ℕ} (κ R : ℝ) (z : E n)
    {x : E n} (hx : x ∈ sphere z R) : dirichletAnnularBarrier κ R z x = 0 := by
  simp only [dirichletAnnularBarrier, dirichletRadialExponential,
    ← dist_eq_norm, mem_sphere.mp hx, sub_self]

theorem dirichletAnnularBarrier_le_one {n : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (R : ℝ) (z x : E n) : dirichletAnnularBarrier κ R z x ≤ 1 := by
  have hExp : dirichletRadialExponential κ z x ≤ 1 := by
    unfold dirichletRadialExponential
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) (sq_nonneg _))
  have hPos := Real.exp_pos (-κ * R ^ 2)
  unfold dirichletAnnularBarrier
  linarith

theorem dirichletAnnularBarrier_lower_quadratic {n : ℕ} (κ R : ℝ) (z x : E n) :
    κ * Real.exp (-κ * R ^ 2) * (R ^ 2 - ‖x - z‖ ^ 2) ≤
      dirichletAnnularBarrier κ R z x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (κ * (R ^ 2 - ‖x - z‖ ^ 2)))
    (Real.exp_pos (-κ * R ^ 2)).le
  have he : dirichletRadialExponential κ z x =
      Real.exp (-κ * R ^ 2) * Real.exp (κ * (R ^ 2 - ‖x - z‖ ^ 2)) := by
    unfold dirichletRadialExponential
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he] at h
  unfold dirichletAnnularBarrier
  nlinarith only [h]

/-- The barrier dominates distance to the outer sphere at an explicit scale. -/
theorem dirichletAnnularBarrier_lower_distance {n : ℕ} {κ R : ℝ}
    (hκ : 0 ≤ κ) (z x : E n) (hx : ‖x - z‖ ≤ R) :
    κ * R * Real.exp (-κ * R ^ 2) * (R - ‖x - z‖) ≤
      dirichletAnnularBarrier κ R z x := by
  have hq : R * (R - ‖x - z‖) ≤ R ^ 2 - ‖x - z‖ ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg (x - z)) (sub_nonneg.mpr hx)]
  have h := mul_le_mul_of_nonneg_left hq
    (mul_nonneg hκ (Real.exp_pos (-κ * R ^ 2)).le)
  calc
    κ * R * Real.exp (-κ * R ^ 2) * (R - ‖x - z‖) =
        κ * Real.exp (-κ * R ^ 2) * (R * (R - ‖x - z‖)) := by ring
    _ ≤ κ * Real.exp (-κ * R ^ 2) * (R ^ 2 - ‖x - z‖ ^ 2) := h
    _ ≤ dirichletAnnularBarrier κ R z x := dirichletAnnularBarrier_lower_quadratic κ R z x

def dirichletQuadraticBarrier {n : ℕ} (R : ℝ) (z x : E n) : ℝ :=
  ‖x - z‖ ^ 2 - R ^ 2

theorem contDiff_dirichletQuadraticBarrier {n : ℕ} (R : ℝ) (z : E n) :
    ContDiff ℝ ∞ (dirichletQuadraticBarrier R z) :=
  ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).sub contDiff_const

theorem hasFDerivAt_dirichletQuadraticBarrier {n : ℕ} (R : ℝ) (z x : E n) :
    HasFDerivAt (dirichletQuadraticBarrier R z) ((2 : ℝ) • innerSL ℝ (x - z)) x := by
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq, two_smul] using!
    ((hasStrictFDerivAt_norm_sq (x - z)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const z)).sub_const (R ^ 2)

theorem realHessian_dirichletQuadraticBarrier {n : ℕ} (R : ℝ) (z x : E n) :
    realHessian (dirichletQuadraticBarrier R z) x = (2 : ℝ) • innerSL ℝ := by
  have he : fderiv ℝ (dirichletQuadraticBarrier R z) =
      fun y => (2 : ℝ) • innerSL ℝ (y - z) := by
    funext y
    exact (hasFDerivAt_dirichletQuadraticBarrier R z y).fderiv
  have hZ : HasFDerivAt (fun y : E n => innerSL ℝ (y - z)) (innerSL ℝ) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using!
      (innerSL ℝ (E := E n)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
  rw [realHessian, he]
  exact (hZ.const_smul (2 : ℝ)).fderiv

theorem dirichletBilinearContraction_quadraticBarrier {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (A : E n →L[ℝ] E n) (R : ℝ) (z x : E n) :
    dirichletBilinearContraction b A (realHessian (dirichletQuadraticBarrier R z) x) =
      2 * ∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i) := by
  rw [realHessian_dirichletQuadraticBarrier]
  simp only [dirichletBilinearContraction, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  rfl

theorem dirichlet_coefficient_trace_lower_bound {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n →L[ℝ] E n} {ell : ℝ}
    (hCoer : ∀ v : E n, ell * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    (2 * n : ℝ) * ell ≤ ∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i) := by
  calc
    (2 * n : ℝ) * ell = ∑ _i : Fin (2 * n), ell := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [b.orthonormal.norm_eq_one i, one_pow, mul_one] using hCoer (b i)

end KEBall
