import KEBall.DirichletHessianUniformBounds
import KEBall.DirichletUniformEllipticity
import KEBall.DirichletWeakDeterminantLimit

/-!
# Uniform actual coefficients and first jets on the prescribed density path

The bounds are extracted from the already verified a priori estimates.
They are chosen before the path parameter and the smooth solution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff NNReal Matrix.Norms.Elementwise

namespace KEBall

theorem exists_uniform_logDensityPath_cofactor_bounds {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ {u : E n → ℝ},
        SmoothNear (closedUnitBall n) u → (∀ x ∈ unitSphere n, u x = 0) →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, (complexHessian u x).det.re = Real.exp (t * g x)) →
        ∀ x ∈ unitBall n, ‖dirichletCofactorOperator u x‖ ≤ K ∧
          ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v := by
  obtain ⟨D, hD⟩ := exists_norm_complexHessian_le_of_logDensityPath hn hg
  obtain ⟨K, hK, hKNorm⟩ := exists_norm_dirichletCofactorOperator_bound (n := n) D
  obtain ⟨a, b, Kg, M, ha, hb, hKg, hM, hData⟩ := exists_logDensityPath_bounds hn hg
  obtain ⟨l, U, hl, hU, hEll⟩ := exists_uniform_ellipticity_of_dirichlet_density_bounds hn ha hb hKg hM
  refine ⟨a ^ n * l, K, mul_pos (pow_pos ha _) hl, hK, ?_⟩
  intro t ht u hu hu0 huP hEq x hx
  refine ⟨hKNorm u x (hD t ht hu hu0 huP hEq x hx), ?_⟩
  intro v
  let f : E n → ℝ := fun y => Real.exp (t * g y)
  have hf : SmoothNear (closedUnitBall n) f := by
    obtain ⟨V, hV, hSubV, hgV⟩ := hg
    exact ⟨V, hV, hSubV, (contDiffOn_const.mul hgV).exp⟩
  have hDensity (y : E n) (hy : y ∈ unitBall n) : a ^ n ≤ f y ∧ f y ≤ b ^ n :=
    (hData t ht).1 y (ball_subset_closedBall hy)
  have he := (hEll hu hf hu0 huP hEq hDensity
    (fun y hy => (hData t ht).2.1 y (ball_subset_closedBall hy))
    (fun y hy => (hData t ht).2.2 y (ball_subset_closedBall hy))
    x (ball_subset_closedBall hx) v).1
  rw [dirichletCofactorOperator_inner_self (huP x hx), hEq x hx]
  change (a ^ n * l) * ‖v‖ ^ 2 ≤ f x * _
  calc
    (a ^ n * l) * ‖v‖ ^ 2 = a ^ n * (l * ‖v‖ ^ 2) := by ring
    _ ≤ f x * (l * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (hDensity x hx).1 (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left he (Real.exp_pos _).le

theorem exists_uniform_logDensityPath_firstJet_bounds {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ (L : ℝ≥0) (A : ℝ), 0 ≤ A ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ {u : E n → ℝ},
        SmoothNear (closedUnitBall n) u → (∀ x ∈ unitSphere n, u x = 0) →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, (complexHessian u x).det.re = Real.exp (t * g x)) →
        LipschitzOnWith L (fderiv ℝ u) (closedUnitBall n) ∧ ‖fderiv ℝ u 0‖ ≤ A := by
  obtain ⟨a, b, K, M, ha, hb, hK, hM, hData⟩ := exists_logDensityPath_bounds hn hg
  let d := (3 * K + 1) / (n : ℝ)
  let C := 2 * b + 4 * b * d +
    (2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * d) ^ 2 / (4 * a)))
  let L : ℝ≥0 := ⟨C + ((M + 1) / (n : ℝ)) * b, by dsimp [C, d]; positivity⟩
  let A : ℝ := 2 * b + ((K + 1) / (n : ℝ)) * b
  refine ⟨L, A, by dsimp [A]; positivity, ?_⟩
  intro t ht u hu hu0 huP hEq
  let f : E n → ℝ := fun x => Real.exp (t * g x)
  have hf : SmoothNear (closedUnitBall n) f := by
    obtain ⟨V, hV, hSub, hgV⟩ := hg
    exact ⟨V, hV, hSub, (contDiffOn_const.mul hgV).exp⟩
  have hDensity (x : E n) (hx : x ∈ unitBall n) : a ^ n ≤ f x ∧ f x ≤ b ^ n :=
    (hData t ht).1 x (ball_subset_closedBall hx)
  have hLog (x : E n) (hx : x ∈ unitBall n) : ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K :=
    (hData t ht).2.1 x (ball_subset_closedBall hx)
  have hHess (x : E n) (hx : x ∈ closedUnitBall n) (v : E n) (hv : ‖v‖ = 1) :
      |realHessian u x v v| ≤ L :=
    abs_realHessian_self_le_of_dirichlet_det hn hu hf hu0 huP hEq ha hb hM hDensity
      (fun y hy z hz => abs_realHessian_self_le_on_sphere_of_dirichlet_det hn hu hf hu0 huP hEq
        ha hb hK hDensity hLog hy hz)
      (fun y hy => (hData t ht).2.2 y (ball_subset_closedBall hy)) x hx v hv
  refine ⟨lipschitzOnWith_fderiv_of_unit_hessian_bound hu hHess, ?_⟩
  exact norm_fderiv_le_of_dirichlet_det hn hu hf hu0 huP hEq ha hb hK hDensity hLog
    0 (by simp [closedUnitBall])

end KEBall
