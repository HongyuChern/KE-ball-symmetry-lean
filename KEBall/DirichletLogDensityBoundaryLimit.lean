import KEBall.DirichletLogDensityBoundaryPower
import KEBall.DirichletBoundaryOscillationLimit

/-!
# Boundary rotation quotient decay for a specified first-jet limit

Uniform convergence of the actual derivatives identifies every quotient
pointwise inside the ball.  The boundary estimates pass to that same G.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff Matrix NNReal Topology

namespace KEBall

theorem exists_logDensityPath_firstJet_limit_boundary_power {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {N : ℝ} (hN : 0 ≤ N)
    {t : ℕ → ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x))
    {G : E n → E n →L[ℝ] ℝ}
    (hGrad : TendstoUniformlyOn (fun m => fderiv ℝ (u m)) G atTop (closedUnitBall n)) :
    ∃ α D : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ D ∧
      ∀ (T : E n →L[ℝ] E n), (∀ y, T (J y) = J (T y)) →
        ∀ (M : Matrix (Fin n) (Fin n) ℂ), (∀ y, complexCoord (T y) = M *ᵥ complexCoord y) →
          Mᴴᵀ = -Mᵀ → (∀ x ∈ unitSphere n, inner ℝ x (T x) = 0) → ‖T‖ ≤ N →
          ∀ p ∈ unitSphere n, ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 →
            ∀ r : ℝ, 0 < r → r ≤ R₀ →
              dirichletBoundaryOscillation
                (fun x => G x (T x) / dirichletBoundaryDistanceProxy x) p r ≤
                (D * (256 / R₀ : ℝ) ^ α) * r ^ α := by
  have hn0 : 0 < n := by omega
  obtain ⟨α, D, hα0, hα1, hD, hPower⟩ :=
    exists_uniform_logDensityPath_rotation_quotient_power_decay hn hg hN
  obtain ⟨L, A, hA, hJet⟩ := exists_uniform_logDensityPath_firstJet_bounds hn0 hg
  refine ⟨α, D, hα0, hα1, hD, ?_⟩
  intro T hTJ M hTM hM hTangent hTN p hp R₀ hR₀ hR₀1 r hr hrR₀
  let B : ℝ := 2 * (2 * (L : ℝ) + A) * N
  have hBound (m : ℕ) (x : E n) (hx : x ∈ unitBall n) :
      |fderiv ℝ (u m) x (T x) / dirichletBoundaryDistanceProxy x| ≤ B := by
    obtain ⟨hLip, hAt0⟩ := hJet (t m) (ht m) (hu m) (hu0 m) (huP m) (hEq m)
    have hDu (y : E n) (hy : y ∈ closedUnitBall n) :
        HasFDerivWithinAt (u m) (fderiv ℝ (u m) y) (closedUnitBall n) y :=
      (((hu m).contDiffAt hy).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
    have h := abs_dirichlet_rotation_firstJet_quotient_le hn0 hLip hDu (hu0 m) T hTangent hx
    have hFirst : 2 * (2 * (L : ℝ) + ‖fderiv ℝ (u m) 0‖) ≤
        2 * (2 * (L : ℝ) + A) := by linarith only [hAt0]
    exact h.trans (mul_le_mul hFirst hTN (norm_nonneg T) (by positivity))
  have hLim (x : E n) (hx : x ∈ unitBall n) :
      Tendsto (fun m => fderiv ℝ (u m) x (T x) / dirichletBoundaryDistanceProxy x)
        atTop (𝓝 (G x (T x) / dirichletBoundaryDistanceProxy x)) := by
    exact (((ContinuousLinearMap.apply ℝ ℝ (T x)).continuous.tendsto (G x)).comp
      (hGrad.tendsto_at (ball_subset_closedBall hx))).div_const _
  apply dirichletBoundaryOscillation_le_of_pointwise_limit hBound hLim hp hr
  intro m
  exact hPower (t m) (ht m) (hu m) (hu0 m) (huP m) (hEq m)
    T hTJ M hTM hM hTangent hTN p hp R₀ hR₀ hR₀1 r hr hrR₀

end KEBall
