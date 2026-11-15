import KEBall.DirichletBoundaryQuotientPower
import KEBall.DirichletRotationQuotientBound
import KEBall.DirichletRotationCofactorEquation
import KEBall.DirichletLogDensityBoundaryBounds

/-!
# Uniform boundary power decay of actual log-density path rotation quotients

All PDE, source, weak Harnack and starting quotient hypotheses are supplied
by the verified estimates for the same smooth potential.  The exponent and
constant are chosen before the path parameter, solution and bounded rotation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix NNReal

namespace KEBall

theorem exists_uniform_logDensityPath_rotation_quotient_power_decay {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) {N : ℝ} (hN : 0 ≤ N) :
    ∃ α D : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ D ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ {u : E n → ℝ},
        SmoothNear (closedUnitBall n) u → (∀ x ∈ unitSphere n, u x = 0) →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, (complexHessian u x).det.re = Real.exp (t * g x)) →
        ∀ (T : E n →L[ℝ] E n), (∀ y, T (J y) = J (T y)) →
          ∀ (M : Matrix (Fin n) (Fin n) ℂ), (∀ y, complexCoord (T y) = M *ᵥ complexCoord y) →
            Mᴴᵀ = -Mᵀ → (∀ x ∈ unitSphere n, inner ℝ x (T x) = 0) → ‖T‖ ≤ N →
            ∀ p ∈ unitSphere n, ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 →
              ∀ r : ℝ, 0 < r → r ≤ R₀ →
                dirichletBoundaryOscillation
                  (fun x => fderiv ℝ u x (T x) / dirichletBoundaryDistanceProxy x) p r ≤
                  (D * (256 / R₀ : ℝ) ^ α) * r ^ α := by
  have hn0 : 0 < n := by omega
  obtain ⟨c, Kc, hc, hKc, hCoeff⟩ := exists_uniform_logDensityPath_cofactor_bounds hn0 hg
  obtain ⟨L, A, hA, hJet⟩ := exists_uniform_logDensityPath_firstJet_bounds hn0 hg
  obtain ⟨a, b, Kg, M₂, ha, hb, hKg, hM₂, hData⟩ := exists_logDensityPath_bounds hn0 hg
  let S : ℝ := b ^ n * Kg * N
  let B : ℝ := 2 * (2 * (L : ℝ) + A) * N
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨α, D, hα0, hα1, hD, hPower⟩ :=
    exists_uniform_dirichlet_boundary_quotient_power_decay hn hc hKc hS hB
  refine ⟨α, D, hα0, hα1, hD, ?_⟩
  intro t ht u hu hu0 huP hEq T hTJ M hTM hM hTangent hTN
  let f : E n → ℝ := fun x => Real.exp (t * g x)
  let q : E n → ℝ := fun x => fderiv ℝ u x (T x)
  have hf : SmoothNear (closedUnitBall n) f := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  have hq : SmoothNear (closedUnitBall n) q := smoothNear_dirichlet_linearFieldDerivative hu T
  have hq0 (x : E n) (hx : x ∈ unitSphere n) : q x = 0 :=
    dirichlet_linearFieldDerivative_zero_on_sphere hu hu0 T hTangent hx
  obtain ⟨hLip, hAt0⟩ := hJet t ht hu hu0 huP hEq
  have hDu (x : E n) (hx : x ∈ closedUnitBall n) :
      HasFDerivWithinAt u (fderiv ℝ u x) (closedUnitBall n) x :=
    ((hu.contDiffAt hx).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hBound (x : E n) (hx : x ∈ unitBall n) : |q x / dirichletBoundaryDistanceProxy x| ≤ B := by
    have h := abs_dirichlet_rotation_firstJet_quotient_le hn0 hLip hDu hu0 T hTangent hx
    have hFirst : 2 * (2 * (L : ℝ) + ‖fderiv ℝ u 0‖) ≤ 2 * (2 * (L : ℝ) + A) := by
      linarith only [hAt0]
    exact h.trans (mul_le_mul hFirst hTN (norm_nonneg T) (by positivity))
  have hSource (x : E n) (hx : x ∈ unitBall n) :
      |dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
        (dirichletCofactorOperator u x) (realHessian q x)| ≤ S := by
    rw [← dirichletCofactorOfMatrix_complexHessian]
    have h := abs_dirichlet_rotation_cofactor_source_le hu hf huP hEq T hTJ M hTM hM
      (pow_nonneg hb.le n) hKg
      (fun y hy => ((hData t ht).1 y (ball_subset_closedBall hy)).2)
      (fun y hy => (hData t ht).2.1 y (ball_subset_closedBall hy)) hx
    exact h.trans (mul_le_mul_of_nonneg_left hTN (by positivity))
  exact hPower u hu huP (fun x hx => (hCoeff t ht hu hu0 huP hEq x hx).1)
    (fun x hx => (hCoeff t ht hu hu0 huP hEq x hx).2) q hq hq0 hBound hSource

end KEBall
