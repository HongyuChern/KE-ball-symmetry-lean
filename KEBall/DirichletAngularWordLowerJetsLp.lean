import KEBall.DirichletAllMixedAngularHessianLp

/-! The original angular words and their actual first derivatives in finite Lp. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open Filter MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem contDiffOn_dirichletAngularDerivative_interior {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) (S : E n →L[ℝ] E n) :
    ContDiffOn ℝ ∞ (dirichletAngularDerivative S u) (unitBall n) := by
  refine ((hu.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply
    S.contDiff.contDiffOn).congr ?_
  intro x hx
  exact dirichletAngularDerivative_eq_fderiv_on_ball S u hx

theorem contDiffOn_dirichletAngularWord_interior {n m : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) (R : Fin m → DirichletUnitaryField n) :
    ContDiffOn ℝ ∞ (dirichletAngularWord R u) (unitBall n) := by
  induction m with
  | zero => exact hu
  | succ m ih =>
    exact contDiffOn_dirichletAngularDerivative_interior (ih (Fin.tail R)) (R 0).val

theorem fderiv_dirichletAngularDerivative_on_ball {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) (S : E n →L[ℝ] E n)
    {x : E n} (hx : x ∈ unitBall n) :
    fderiv ℝ (dirichletAngularDerivative S u) x =
      (fderiv ℝ u x).comp S + (realHessian u x).flip (S x) := by
  have he : dirichletAngularDerivative S u =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y (S y)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact dirichletAngularDerivative_eq_fderiv_on_ball S u hy
  rw [he.fderiv_eq, fderiv_clm_apply
    (((hu.contDiffAt (isOpen_ball.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    S.differentiableAt, S.fderiv]
  rfl

theorem memLp_dirichletAngularDerivative_and_fderiv {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) (S : E n →L[ℝ] E n) (p : ℝ≥0∞)
    (hD : MemLp (fderiv ℝ u) p ((volume0 n).restrict (unitBall n)))
    (hH : MemLp (realHessian u) p ((volume0 n).restrict (unitBall n))) :
    MemLp (dirichletAngularDerivative S u) p ((volume0 n).restrict (unitBall n)) ∧
    MemLp (fderiv ℝ (dirichletAngularDerivative S u)) p ((volume0 n).restrict (unitBall n)) := by
  have hC := contDiffOn_dirichletAngularDerivative_interior hu S
  have hSM := hC.continuousOn.aestronglyMeasurable (μ := volume0 n) measurableSet_ball
  have hDSM := (hC.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).continuousOn.aestronglyMeasurable
    (μ := volume0 n) measurableSet_ball
  have hSx (x : E n) (hx : x ∈ unitBall n) : ‖S x‖ ≤ ‖S‖ :=
    (S.le_opNorm x).trans ((mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le (norm_nonneg S)).trans_eq (mul_one _))
  constructor
  · refine (hD.norm.const_mul ‖S‖).mono' hSM ?_
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    rw [dirichletAngularDerivative_eq_fderiv_on_ball S u hx]
    exact ((fderiv ℝ u x).le_opNorm (S x)).trans
      ((mul_le_mul_of_nonneg_left (hSx x hx) (norm_nonneg _)).trans_eq (mul_comm _ _))
  · refine ((hD.norm.add hH.norm).const_mul ‖S‖).mono' hDSM ?_
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    rw [fderiv_dirichletAngularDerivative_on_ball hu S hx]
    calc
      _ ≤ ‖(fderiv ℝ u x).comp S‖ + ‖(realHessian u x).flip (S x)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ u x‖*‖S‖ + ‖realHessian u x‖*‖S‖ := add_le_add
        (ContinuousLinearMap.opNorm_comp_le _ _)
        (by
          have h := ((realHessian u x).flip.le_opNorm (S x)).trans
            (mul_le_mul_of_nonneg_left (hSx x hx) (norm_nonneg _))
          simpa only [ContinuousLinearMap.opNorm_flip] using h)
      _ = ‖S‖ * (‖fderiv ℝ u x‖ + ‖realHessian u x‖) := by ring

theorem memLp_angularWord_lower_jets_of_C2_solution_finite {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (dirichletAngularWord R u) p ((volume0 n).restrict (unitBall n)) ∧
    MemLp (fderiv ℝ (dirichletAngularWord R u)) p ((volume0 n).restrict (unitBall n)) := by
  have hH {j : ℕ} (Q : Fin j → DirichletUnitaryField n) :
      MemLp (realHessian (dirichletAngularWord Q u)) p ((volume0 n).restrict (unitBall n)) := by
    refine MemLp.ae_eq ?_ (memLp_withinHessian_angularWord_of_C2_solution_finite
      hn hu huS hu0 hPos hf hEq Q p hp)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact dirichletWithinRealHessian_eq_on_ball _ hx
  induction m with
  | zero =>
    refine ⟨dirichlet_memLp_of_continuousOn hn hu.continuousOn p, ?_⟩
    have hB : UniqueDiffOn ℝ (closedUnitBall n) :=
      uniqueDiffOn_convex (convex_closedBall (0 : E n) 1) (by
        rw [closedUnitBall, interior_closedBall _ (by norm_num)]
        exact nonempty_ball.mpr (by norm_num))
    have hC := (hu.fderivWithin (m := 1) hB (by norm_num)).continuousOn
    refine MemLp.ae_eq ?_ (dirichlet_memLp_of_continuousOn hn hC p)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact fderivWithin_of_mem_nhds (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  | succ m ih =>
    exact memLp_dirichletAngularDerivative_and_fderiv
      (contDiffOn_dirichletAngularWord_interior huS (Fin.tail R)) (R 0).val p
      (ih (Fin.tail R)).2 (hH (Fin.tail R))

end KEBall
