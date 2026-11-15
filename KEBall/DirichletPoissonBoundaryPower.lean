import KEBall.DirichletBoundaryQuotientPower
import KEBall.DirichletBoundaryQuotientBound
import KEBall.DirichletTraceCofactorBounds
import KEBall.DirichletRotationCofactorEquation
import KEBall.DirichletLaplacianTrace
import KEBall.RadialJacobi

/-! Boundary quotient decay for the actual Poisson equation, using a fixed
quadratic background in the cofactor Harnack theorem.  Uncompiled draft. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open InnerProductSpace Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff Laplacian NNReal

noncomputable section
namespace KEBall

theorem exists_uniform_poisson_boundary_quotient_power {n : ℕ} (hn : 2 ≤ n)
    {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) :
    ∃ α D : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ D ∧
      ∀ (q : E n → ℝ), ContDiff ℝ ∞ q →
        (∀ x ∈ unitSphere n, q x = 0) →
        (∀ x ∈ closedUnitBall n, ‖fderiv ℝ q x‖ ≤ G) →
        (∀ x ∈ unitBall n, |Δ q x| ≤ L) →
        ∀ p ∈ unitSphere n, ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 →
          ∀ r : ℝ, 0 < r → r ≤ R₀ →
            dirichletBoundaryOscillation
              (fun x => q x / dirichletBoundaryDistanceProxy x) p r ≤
                (D * (256 / R₀ : ℝ) ^ α) * r ^ α := by
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  let b : E n → ℝ := fun x => ‖x‖ ^ 2
  have hb : ContDiff ℝ ∞ b := contDiff_norm_sq ℝ
  have hbNear : SmoothNear (closedUnitBall n) b :=
    ⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩
  have hOneNear : SmoothNear (closedUnitBall n) (fun _ : E n => (1 : ℝ)) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hH (x : E n) : complexHessian b x = 1 := by
    have hρ (t : ℝ) (_ : 0 ≤ t) : HasDerivAt (fun s : ℝ => s) 1 t :=
      hasDerivAt_id' t
    have hρ₁ : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 (‖x‖ ^ 2) := hasDerivAt_const _ _
    simpa [b] using
      complexHessian_radial_profile hρ (x := x) hρ₁
  have hbP (x : E n) (_ : x ∈ unitBall n) : (complexHessian b x).PosDef := by
    rw [hH]
    exact Matrix.PosDef.one
  have hbEq (x : E n) (_ : x ∈ unitBall n) :
      (complexHessian b x).det.re = (1 : ℝ) := by simp [hH]
  have hbTrace (x : E n) (_ : x ∈ closedUnitBall n) :
      (complexHessian b x).trace.re ≤ (n : ℝ) := by simp [hH]
  let c : ℝ := (n : ℝ)⁻¹ / 4
  let K : ℝ := (1 / (n : ℝ) ^ (n - 1))⁻¹ / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCoeff (x : E n) (hx : x ∈ unitBall n) :
      ‖dirichletCofactorOperator b x‖ ≤ K ∧
        ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator b x v) v := by
    simpa only [one_pow, one_mul] using
      dirichletCofactorOperator_bounds_of_det_trace hbNear hOneNear hbP hbEq
        (a := 1) (b := 1) zero_lt_one zero_lt_one hnR
        (fun _ _ => by simp) hbTrace (ball_subset_closedBall hx)
  obtain ⟨α, D, hα0, hα1, hD, hPower⟩ :=
    exists_uniform_dirichlet_boundary_quotient_power_decay hn hc hK
      (show 0 ≤ L / 4 by positivity) (show 0 ≤ 2 * G by positivity)
  refine ⟨α, D, hα0, hα1, hD, ?_⟩
  intro q hq hq0 hGrad hLap
  have hqNear : SmoothNear (closedUnitBall n) q :=
    ⟨univ, isOpen_univ, subset_univ _, hq.contDiffOn⟩
  have hLip : LipschitzOnWith (⟨G, hG⟩ : ℝ≥0) q (closedUnitBall n) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _
      (convex_closedBall (0 : E n) 1)
    · intro x _
      exact hq.differentiable (by simp) x
    · intro x hx
      exact_mod_cast hGrad x hx
  apply hPower b hbNear hbP (fun x hx => (hCoeff x hx).1)
    (fun x hx => (hCoeff x hx).2) q hqNear hq0
    (fun x hx => abs_dirichlet_boundary_quotient_le_of_lipschitz hn0 hLip hq0 hx)
  intro x hx
  have hContraction : dirichletBilinearContraction
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletCofactorOperator b x) (realHessian q x) = Δ q x / 4 := by
    rw [← dirichletCofactorOfMatrix_complexHessian,
      dirichletBilinearContraction_cofactor_eq b q
        (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    unfold MoserTrudinger.cofactorContraction
    rw [hH, Matrix.adjugate_one,
      euclideanLaplacian_eq_four_complexHessian_trace_re hq.contDiffAt]
    simp [Matrix.one_apply, Matrix.trace, Matrix.diag]
  rw [hContraction, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact div_le_div_of_nonneg_right (hLap x hx) (by norm_num)

end KEBall
