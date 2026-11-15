import KEBall.DirichletSmoothAngularWordEquation
import KEBall.DirichletAngularWithinL2

/-! The exact angular determinant equation needs only interior smoothness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ContDiff Topology
namespace KEBall

theorem exists_dirichlet_local_smooth_extension {n : ℕ} {u : E n → ℝ}
    {U : Set (E n)} (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    {x : E n} (hx : x ∈ U) :
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ v =ᶠ[𝓝 x] u := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := ε/4, rOut := ε/2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let v (y : E n) := χ y * u y
  have hχU : tsupport (χ : E n → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [χ]; linarith)).trans hεU
  refine ⟨v, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact χ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hy))
    · have hn : y ∉ tsupport (χ : E n → ℝ) := fun h => hy (hχU h)
      have he : v =ᶠ[𝓝 y] (0 : E n → ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with z hz
        simp only [v,hz,zero_mul,Pi.zero_apply]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · filter_upwards [χ.eventuallyEq_one_of_mem_ball (mem_ball_self χ.rIn_pos)] with y hy
    simp only [v,hy,Pi.one_apply,one_mul]

theorem dirichletAngularWord_eventuallyEq {n m : ℕ} {u v : E n → ℝ}
    {x : E n} (hx : x ∈ unitBall n) (he : u =ᶠ[𝓝 x] v)
    (R : Fin m → DirichletUnitaryField n) :
    dirichletAngularWord R u =ᶠ[𝓝 x] dirichletAngularWord R v := by
  induction m with
  | zero => exact he
  | succ m ih =>
    have hD : fderiv ℝ (dirichletAngularWord (Fin.tail R) u) =ᶠ[𝓝 x]
        fderiv ℝ (dirichletAngularWord (Fin.tail R) v) := (ih (Fin.tail R)).fderiv
    filter_upwards [hD,isOpen_ball.mem_nhds hx] with y hy hyB
    change dirichletAngularDerivative (R 0).val _ y = dirichletAngularDerivative (R 0).val _ y
    rw [dirichletAngularDerivative_eq_fderiv_on_ball _ _ hyB,
      dirichletAngularDerivative_eq_fderiv_on_ball _ _ hyB,hy]

theorem dirichletWithinComplexHessian_eq_of_eventuallyEq_on_ball {n : ℕ}
    {u v : E n → ℝ} {x : E n} (hx : x ∈ unitBall n) (he : u =ᶠ[𝓝 x] v) :
    dirichletWithinComplexHessian u x = dirichletWithinComplexHessian v x := by
  change complexHessianOfRealBilinear (dirichletWithinRealHessian u x) =
    complexHessianOfRealBilinear (dirichletWithinRealHessian v x)
  rw [dirichletWithinRealHessian_eq_on_ball _ hx,dirichletWithinRealHessian_eq_on_ball _ hx]
  exact congrArg complexHessianOfRealBilinear he.fderiv.fderiv_eq

theorem interior_angularWord_eq_linearized_det {n m : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (R : Fin (m+1) → DirichletUnitaryField n) {x : E n} (hx : x ∈ unitBall n) :
    ((dirichletWithinComplexHessian u x).adjugate *
      dirichletWithinComplexHessian (dirichletAngularWord R u) x).trace.re +
      dirichletAngularDetLowerTerms R dirichletWithinComplexHessian u x =
      dirichletAngularWord R f x := by
  obtain ⟨v,hv,he⟩ := exists_dirichlet_local_smooth_extension isOpen_ball hu hx
  have h := closedBall_angularWord_eq_linearized_det_of_contDiff hn hv R x (ball_subset_closedBall hx)
  have hH := dirichletWithinComplexHessian_eq_of_eventuallyEq_on_ball hx he
  have hHW {j : ℕ} (Q : Fin j → DirichletUnitaryField n) :=
    dirichletWithinComplexHessian_eq_of_eventuallyEq_on_ball hx
      (dirichletAngularWord_eventuallyEq hx he Q)
  have hLow : dirichletAngularDetLowerTerms R dirichletWithinComplexHessian v x =
      dirichletAngularDetLowerTerms R dirichletWithinComplexHessian u x := by
    unfold dirichletAngularDetLowerTerms
    apply Finset.sum_congr rfl
    intro c hc
    rw [hH]
    congr 1
    funext j
    exact hHW _
  have hF : (fun y => (complexHessian v y).det.re) =ᶠ[𝓝 x] f := by
    have hNear := he.eventually_nhds
    filter_upwards [hNear,isOpen_ball.mem_nhds hx] with y hy hyB
    rw [complexHessian_congr_of_eventuallyEq hy]
    exact hEq y hyB
  rw [hH,hHW R,hLow,(dirichletAngularWord_eventuallyEq hx hF R).self_of_nhds] at h
  exact h

end KEBall
