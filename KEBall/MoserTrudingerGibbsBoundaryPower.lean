import KEBall.DirichletSourceBoundaryQuotient
import KEBall.DirichletBoundaryQuotientPower
import KEBall.DirichletRotationCofactorEquation
import KEBall.MoserTrudingerGibbsCofactorUniform

/-! Uniform boundary power decay for actual Gibbs rotation derivatives.
The initial quotient bound comes from the actual linearized equation and
its quadratic barrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall.MoserTrudinger

theorem exists_uniform_rotation_boundary_power_of_smoothGibbs_bounds
    {n : ℕ} (hn : 2 ≤ n) {γ B D G N : ℝ}
    (hγ : 0 ≤ γ) (hD : 0 < D) (hG : 0 ≤ G) (hN : 0 ≤ N)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0)
    (hTrace : ∀ j x, x ∈ closedUnitBall n → (complexHessian (u (j + 1)) x).trace.re ≤ D)
    (hGrad : ∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ G) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
      ∀ (j : ℕ) (T : E n →L[ℝ] E n), (∀ y, T (J y) = J (T y)) →
        ∀ (M : Matrix (Fin n) (Fin n) ℂ), (∀ y, complexCoord (T y) = M *ᵥ complexCoord y) →
          Mᴴᵀ = -Mᵀ → (∀ x ∈ unitSphere n, inner ℝ x (T x) = 0) → ‖T‖ ≤ N →
          ∀ p ∈ unitSphere n, ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 →
            ∀ r : ℝ, 0 < r → r ≤ R₀ →
              dirichletBoundaryOscillation
                (fun x => fderiv ℝ (u (j + 1)) x (T x) / dirichletBoundaryDistanceProxy x) p r ≤
                (C * (256 / R₀ : ℝ) ^ α) * r ^ α := by
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  obtain ⟨a, b, ha, hb, hDensity⟩ := exists_power_density_bounds_of_bounded_family hn0 hγ
    (fun j => (hu j).continuous.continuousOn) huB
  obtain ⟨c, K, hc, hK, hCoeff⟩ := exists_uniform_cofactor_bounds_of_smoothGibbs_trace
    hn0 hγ hD hu huP hEq huB hTrace
  let S : ℝ := b ^ n * (γ * G) * N
  let Q : ℝ := S / (2 * n * c)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨α, C, hα0, hα1, hC, hPower⟩ :=
    exists_uniform_dirichlet_boundary_quotient_power_decay hn hc hK.le hS hQ
  refine ⟨α, C, hα0, hα1, hC, ?_⟩
  intro j T hTJ M hTM hM hTan hTN
  let q : E n → ℝ := fun x => fderiv ℝ (u (j + 1)) x (T x)
  have huN : SmoothNear (closedUnitBall n) (u (j + 1)) :=
    ⟨univ, isOpen_univ, subset_univ _, (hu (j + 1)).contDiffOn⟩
  have hfN : SmoothNear (closedUnitBall n) (gibbsDensity γ (u j)) :=
    ⟨univ, isOpen_univ, subset_univ _,
      (((contDiff_const.mul (hu j)).exp).div_const _).contDiffOn⟩
  have hq : SmoothNear (closedUnitBall n) q := smoothNear_dirichlet_linearFieldDerivative huN T
  have hq0 (x : E n) (hx : x ∈ unitSphere n) : q x = 0 :=
    dirichlet_linearFieldDerivative_zero_on_sphere huN (hu0 (j + 1)) T hTan hx
  have hLog (x : E n) (hx : x ∈ unitBall n) :
      ‖fderiv ℝ (fun y => Real.log (gibbsDensity γ (u j) y)) x‖ ≤ γ * G := by
    rw [fderiv_log_gibbsDensity hn0 γ (hu j), norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left (hGrad j x (ball_subset_closedBall hx)) hγ
  have hSource (x : E n) (hx : x ∈ unitBall n) :
      |dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
        (dirichletCofactorOperator (u (j + 1)) x) (realHessian q x)| ≤ S := by
    rw [← dirichletCofactorOfMatrix_complexHessian]
    have h := abs_dirichlet_rotation_cofactor_source_le huN hfN (huP (j + 1)) (hEq j)
      T hTJ M hTM hM (pow_pos hb n).le (mul_nonneg hγ hG)
      (fun y hy => (hDensity j y (ball_subset_closedBall hy)).2) hLog hx
    exact h.trans (mul_le_mul_of_nonneg_left hTN (by positivity))
  have hSym (x : E n) (hx : x ∈ unitBall n) :
      (dirichletCofactorOperator (u (j + 1)) x).toLinearMap.IsSymmetric := by
    intro v w
    change inner ℝ (dirichletCofactorOperator (u (j + 1)) x v) w =
      inner ℝ v (dirichletCofactorOperator (u (j + 1)) x w)
    rw [← real_inner_comm v (dirichletCofactorOperator (u (j + 1)) x w)]
    simpa only [dirichletCofactorOfMatrix_complexHessian] using
      (dirichletCofactorOfMatrix_symmetric (huP (j + 1) x hx).isHermitian v w)
  have hEll (x : E n) (hx : x ∈ unitBall n) :=
    (hCoeff j x (ball_subset_closedBall hx)).2
  have hBound : ∀ x ∈ unitBall n, |q x / dirichletBoundaryDistanceProxy x| ≤ Q :=
    abs_dirichlet_boundary_quotient_le_of_source hn0 hc hS hSym hEll hq hq0 hSource
  exact hPower (u (j + 1)) huN (huP (j + 1))
    (fun x hx => (hCoeff j x (ball_subset_closedBall hx)).1) hEll q hq hq0 hBound hSource

theorem exists_uniform_rotation_boundary_power_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 2 ≤ n) {γ M B N : ℝ} (hγ : 0 ≤ γ) (hN : 0 ≤ N)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
      ∀ (j : ℕ) (T : E n →L[ℝ] E n), (∀ y, T (J y) = J (T y)) →
        ∀ (A : Matrix (Fin n) (Fin n) ℂ), (∀ y, complexCoord (T y) = A *ᵥ complexCoord y) →
          Aᴴᵀ = -Aᵀ → (∀ x ∈ unitSphere n, inner ℝ x (T x) = 0) → ‖T‖ ≤ N →
          ∀ p ∈ unitSphere n, ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 →
            ∀ r : ℝ, 0 < r → r ≤ R₀ →
              dirichletBoundaryOscillation
                (fun x => fderiv ℝ (u (j + 1)) x (T x) / dirichletBoundaryDistanceProxy x) p r ≤
                (C * (256 / R₀ : ℝ) ^ α) * r ^ α := by
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration
      (by omega : 0 < n) hγ hu hu0 huP hEq hM huB
  exact exists_uniform_rotation_boundary_power_of_smoothGibbs_bounds
    hn hγ hD hG.le hN hu hu0 huP hEq huB hTrace hGrad

end KEBall.MoserTrudinger
