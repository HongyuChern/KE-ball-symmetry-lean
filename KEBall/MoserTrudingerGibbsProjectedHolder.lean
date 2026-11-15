import KEBall.MoserTrudingerGibbsProjectedHarnack
import KEBall.DirichletScalarOscillationHolder
import KEBall.DirichletDirectionalLogDet
import KEBall.DirichletFinitePositiveFrame

/-! Uniform interior Holder bounds for the projected Hessians of the
actual Gibbs iterates.  All constants precede the iteration index. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000

open InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff NNReal

namespace KEBall.MoserTrudinger

theorem exists_uniform_projected_holder_of_smoothGibbs_bounds
    {n : ℕ} (hn : 2 ≤ n) {γ B D G : ℝ} (hγ : 0 ≤ γ) (hD : 0 < D) (hG : 0 ≤ G)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0)
    (hTrace : ∀ j x, x ∈ closedUnitBall n → (complexHessian (u (j + 1)) x).trace.re ≤ D)
    (hGrad : ∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ G) :
    ∃ α K : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ K ∧
      ∀ j (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖complexProjectedHessian (u (j + 2)) x - complexProjectedHessian (u (j + 2)) y‖ ≤
            (K * (8 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
  have hn0 : 0 < n := by omega
  letI : NeZero n := ⟨hn0.ne'⟩
  letI : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨a, b, ha, hb, hDensity⟩ := exists_power_density_bounds_of_bounded_family hn0 hγ
    (fun j => (hu j).continuous.continuousOn) huB
  obtain ⟨c₀, K₀, hc₀, hK₀, hCoeff⟩ := exists_uniform_cofactor_bounds_of_smoothGibbs_trace
    hn0 hγ hD hu huP hEq huB hTrace
  obtain ⟨m, v, l, U, hl, hU, hBasis, hPairs, hRep⟩ :=
    exists_dirichlet_uniform_positive_frame (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (B := K₀) hc₀
  obtain ⟨c, H, S, hc, hH, hS, hHarnack⟩ :=
    exists_uniform_projected_defect_harnack_of_smoothGibbs_trace hn hγ hD hu huP hEq huB hTrace
  let q : ℕ → Fin m → E n → ℝ := fun j i x =>
    complexProjectedHessian (u (j + 2)) x (v i) (v i)
  have hq (j : ℕ) (i : Fin m) : ContinuousOn (q j i) (closedUnitBall n) :=
    ((((complexProjectedHessian_contDiff (hu (j + 2))).clm_apply contDiff_const).clm_apply
      contDiff_const).continuous).continuousOn
  have hLip (j : ℕ) : LipschitzOnWith (⟨G, hG⟩ : ℝ≥0) (u j) (closedUnitBall n) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall (0 : E n) 1)
    · intro x _
      exact (hu j).differentiable (by simp) x
    · intro x hx
      exact_mod_cast hGrad j x hx
  let E₀ : ℝ := b ^ n * (γ * G)
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have hPair : ∀ j x, x ∈ unitBall n → ∀ y, y ∈ unitBall n →
      ∃ β : Fin m → ℝ, (∀ i, l ≤ β i ∧ β i ≤ U) ∧
        (∑ i : Fin m, β i * (q j i x - q j i y)) ≤ E₀ * dist x y := by
    intro j x hx y hy
    have hCoeffX := hCoeff (j + 1) x (ball_subset_closedBall hx)
    have hSym : (dirichletCofactorOperator (u (j + 2)) x).toLinearMap.IsSymmetric := by
      intro w z
      change inner ℝ (dirichletCofactorOperator (u (j + 2)) x w) z =
        inner ℝ w (dirichletCofactorOperator (u (j + 2)) x z)
      rw [← real_inner_comm w (dirichletCofactorOperator (u (j + 2)) x z)]
      simpa only [dirichletCofactorOfMatrix_complexHessian] using
        (dirichletCofactorOfMatrix_symmetric (huP (j + 2) x hx).isHermitian w z)
    obtain ⟨β, hβ, hFrame⟩ := hRep (dirichletCofactorOperator (u (j + 2)) x)
      ⟨hSym, hCoeffX.2, hCoeffX.1⟩
    have hxP : (complexHessianOfRealBilinear (complexProjectedHessian (u (j + 2)) x)).PosDef := by
      rw [complexHessianOfRealBilinear_projected (hu (j + 2)).contDiffAt]
      exact huP (j + 2) x hx
    have hyP : (complexHessianOfRealBilinear (complexProjectedHessian (u (j + 2)) y)).PosDef := by
      rw [complexHessianOfRealBilinear_projected (hu (j + 2)).contDiffAt]
      exact huP (j + 2) y hy
    have hFrame' : dirichletCofactorOfMatrix
        (complexHessianOfRealBilinear (complexProjectedHessian (u (j + 2)) x)) =
          ∑ i : Fin m, β i • rankOne ℝ (v i) (v i) := by
      rw [complexHessianOfRealBilinear_projected (hu (j + 2)).contDiffAt,
        dirichletCofactorOfMatrix_complexHessian]
      exact hFrame
    have hLinear := dirichlet_directional_logdet_comparison
      (complexProjectedHessian (u (j + 2)) x) (complexProjectedHessian (u (j + 2)) y)
      hxP hyP v β hFrame'
    simp only [complexHessianOfRealBilinear_projected (hu (j + 2)).contDiffAt,
      hEq (j + 1) x hx, hEq (j + 1) y hy] at hLinear
    have hDiff : |Real.log (gibbsDensity γ (u (j + 1)) x) -
        Real.log (gibbsDensity γ (u (j + 1)) y)| ≤ (γ * G) * dist x y := by
      rw [log_gibbsDensity_eq hn0 γ (hu (j + 1)).continuous.continuousOn,
        log_gibbsDensity_eq hn0 γ (hu (j + 1)).continuous.continuousOn]
      have he : (-γ) * u (j + 1) x - Real.log (normalizingIntegral γ (u (j + 1))) -
          ((-γ) * u (j + 1) y - Real.log (normalizingIntegral γ (u (j + 1)))) =
            (-γ) * (u (j + 1) x - u (j + 1) y) := by ring
      rw [he, abs_mul, abs_neg, abs_of_nonneg hγ]
      have hL := (hLip (j + 1)).dist_le_mul x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
      have hL' : |u (j + 1) x - u (j + 1) y| ≤ G * dist x y := by
        simpa only [Real.dist_eq, NNReal.coe_mk] using! hL
      exact (mul_le_mul_of_nonneg_left hL' hγ).trans_eq (mul_assoc _ _ _).symm
    have hPos : 0 ≤ gibbsDensity γ (u (j + 1)) x :=
      (pow_pos ha n).le.trans (hDensity (j + 1) x (ball_subset_closedBall hx)).1
    refine ⟨β, hβ, hLinear.trans ?_⟩
    calc
      _ ≤ gibbsDensity γ (u (j + 1)) x *
          |Real.log (gibbsDensity γ (u (j + 1)) x) - Real.log (gibbsDensity γ (u (j + 1)) y)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hPos
      _ ≤ b ^ n * ((γ * G) * dist x y) := mul_le_mul
        (hDensity (j + 1) x (ball_subset_closedBall hx)).2 hDiff (abs_nonneg _) (pow_pos hb n).le
      _ = _ := by dsimp [E₀]; ring
  let A : ℝ := ∑ i : Fin m, (S * ‖v i‖ ^ 2) / (4 * n * c)
  have hAi (i : Fin m) : 0 ≤ (S * ‖v i‖ ^ 2) / (4 * n * c) := by positivity
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hAi i
  have hAiA (i : Fin m) : (S * ‖v i‖ ^ 2) / (4 * n * c) ≤ A :=
    Finset.single_le_sum (fun k _ => hAi k) (Finset.mem_univ i)
  have hH' : 0 < H := zero_lt_one.trans_le hH
  have hAvg : ∀ j i (M : ℝ) (x₀ : E n) (R : ℝ),
      0 < R → closedBall x₀ R ⊆ unitBall n →
      (∀ x ∈ ball x₀ R, q j i x ≤ M) →
      ∀ y ∈ ball x₀ (R / 4),
        (∫ x, M - q j i x ∂dirichletBallProbability x₀ (R / 4)) ≤
          H * (M - q j i y + A * R ^ 2) := by
    intro j i M x₀ R hR hBall hM y hy
    have h := hHarnack j (v i) M x₀ R hR hBall hM y hy
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hAiA i) (sq_nonneg R))) hH'.le)
  obtain ⟨θ, C, hθ0, hθ1, hC, hStep⟩ :=
    exists_uniform_dirichlet_scalar_oscillation_step q hq hl hU.le hE₀ hH' hA hPair hAvg
  let Bv : Fin m → ℝ := fun i => (2 * D) * ‖v i‖ ^ 2
  have hBv (i : Fin m) : 0 ≤ Bv i := by dsimp [Bv]; positivity
  have hBound (j : ℕ) (i : Fin m) (x : E n) (hx : x ∈ unitBall n) : |q j i x| ≤ Bv i := by
    have h := complexProjectedHessian_self_bounds_of_trace (huP (j + 2) x hx)
      (hTrace (j + 1) x (ball_subset_closedBall hx)) (v i)
    rw [abs_of_nonneg h.1]
    exact h.2
  obtain ⟨α, D₁, hα0, hα1, hD₁, hPower⟩ :=
    exists_uniform_dirichlet_scalar_oscillation_power q hq Bv hBv hBound hθ0 hθ1 hC hStep
  refine ⟨α, (2 * n : ℝ) ^ 2 * (3 / 2 * D₁), hα0, hα1, by positivity, ?_⟩
  intro j x₀ R hR hR1 hBall x hx y hy
  exact dirichlet_bilinear_holder_of_directional_oscillation_power
    (complexProjectedHessian_contDiff (hu (j + 2))).continuous.continuousOn
    (fun z hz => hermitianRealification_symm (huP (j + 2) z hz).isHermitian)
    v hBasis hPairs hα0.le hD₁ (hPower j) hR hR1 hBall hx hy

theorem exists_uniform_projected_holder_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ α K : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ K ∧
      ∀ j (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖complexProjectedHessian (u (j + 2)) x - complexProjectedHessian (u (j + 2)) y‖ ≤
            (K * (8 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration
      (by omega : 0 < n) hγ hu hu0 huP hEq hM huB
  exact exists_uniform_projected_holder_of_smoothGibbs_bounds
    hn hγ hD hG.le hu huP hEq huB hTrace hGrad

end KEBall.MoserTrudinger
