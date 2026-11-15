import KEBall.DirichletClosedBallHessianCoercivity

/-! The global estimate for a fixed positive closed-ball potential and a smooth reference. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_dirichlet_closedBall_cofactor_hessian_estimate {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef) :
    ∃ C ≥ (0 : ℝ), ∀ {q : E n → ℝ},
      ContDiffOn ℝ 2 q (closedUnitBall n) → ContDiffOn ℝ ∞ q (unitBall n) →
      (∀ x ∈ unitSphere n, q x = 0) →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian q x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * ∫ x in unitBall n,
          (dirichletContractionCLM n
            (dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x))
            (dirichletWithinRealHessian q x)) ^ 2 ∂volume0 n := by
  let f (x : E n) := (dirichletWithinComplexHessian u x).det.re
  have hFC : ContinuousOn f (closedUnitBall n) :=
    (Complex.continuous_re.comp continuous_id.matrix_det).comp_continuousOn
      (continuousOn_dirichletWithinComplexHessian_of_C2 hu)
  have hK : IsCompact (closedUnitBall n) := isCompact_closedBall _ _
  obtain ⟨p, hp, hMin⟩ := hK.exists_isMinOn
    ⟨0, mem_closedBall_self zero_le_one⟩ hFC
  have hfPos : 0 < f p := posDef_det_re_pos (hPos p hp)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hFC
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (continuousOn_dirichletWithinRealHessian hu)
  let a := min 1 (f p)
  let b := max 1 B
  let M := max 1 D
  have ha : 0 < a := lt_min zero_lt_one hfPos
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hPow : a ^ n ≤ a := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hk, pow_succ]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (pow_le_one₀ ha.le (min_le_left 1 (f p))) ha.le
  have hDen (x : E n) (hx : x ∈ closedUnitBall n) : a ^ n ≤ f x ∧ f x ≤ b ^ n := by
    constructor
    · exact hPow.trans ((min_le_right _ _).trans (hMin hx))
    · have hAbs : |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x hx
      exact (le_abs_self (f x)).trans (hAbs.trans
        ((le_max_right _ _).trans (le_self_pow₀ (le_max_left 1 B) hn.ne')))
  obtain ⟨C, hC, hEst⟩ := exists_integral_sq_withinRealHessian_le_withinLinearizedDet hn ha hb hM
  refine ⟨C, hC, ?_⟩
  intro q hq hqS hq0
  exact hEst hu huS hq hqS hu0 hq0 hPos hDen
    (fun x hx => (hD x hx).trans (le_max_right _ _))

theorem exists_dirichlet_smooth_zeroBoundary_reference_close_hessian {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ closedUnitBall n, ‖dirichletWithinRealHessian u x - realHessian v x‖ < ε) ∧
      ∀ x ∈ unitBall n, ‖realHessian (u - v) x‖ < ε := by
  obtain ⟨v, hV, _, _, hH⟩ := exists_dirichlet_zeroBoundary_smooth_C2_approximation hu huS hu0
  obtain ⟨j, hj⟩ := (Metric.tendstoUniformlyOn_iff.mp hH ε hε).exists
  have hBound (x : E n) (hx : x ∈ closedUnitBall n) :
      ‖dirichletWithinRealHessian u x - realHessian (v j) x‖ < ε := by
    simpa only [dist_eq_norm, dirichletWithinRealHessian] using hj x hx
  refine ⟨v j, (hV j).1, (hV j).2, hBound, ?_⟩
  intro x hx
  rw [dirichlet_realHessian_sub_C2
    ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx))
    (((hV j).1.contDiffAt (ball_subset_closedBall hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    ← dirichletWithinRealHessian_eq_on_ball u hx]
  exact hBound x (ball_subset_closedBall hx)

end KEBall
