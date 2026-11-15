import KEBall.DirichletBoundaryDefectImprovement
import KEBall.DirichletBoundaryDefects
import KEBall.DirichletBoundaryInterval

/-!
# Boundary quotient interval contraction for the actual cofactor operator

The lower and upper defects are constructed from the original function.
Their source bounds include the trace term caused by the distance proxy.
The refined interval stays inside the original interval, so its endpoints
retain the fixed bound needed at every subsequent scale.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_uniform_dirichlet_boundary_interval_contraction {n : ℕ} (hn : 2 ≤ n)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ δ loss : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ loss ∧
      ∀ (u : E n → ℝ), SmoothNear (closedUnitBall n) u →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, ‖dirichletCofactorOperator u x‖ ≤ K) →
        (∀ x ∈ unitBall n, ∀ v : E n,
          c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v) →
      ∀ (q : E n → ℝ), SmoothNear (closedUnitBall n) q →
        (∀ x ∈ unitSphere n, q x = 0) → ∀ S B : ℝ, 0 ≤ S → 0 ≤ B →
        (∀ x ∈ unitBall n,
          |dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian q x)| ≤ S) →
        ∀ m M : ℝ, -B ≤ m → m ≤ M → M ≤ B →
        ∀ p₀ ∈ unitSphere n, ∀ R : ℝ, 0 < R → R ≤ 1 →
          (∀ x ∈ unitBall n, x ∈ ball p₀ (4 * R) →
            m ≤ q x / dirichletBoundaryDistanceProxy x ∧
              q x / dirichletBoundaryDistanceProxy x ≤ M) →
          ∃ a b : ℝ, m ≤ a ∧ b ≤ M ∧ a ≤ b ∧
            (∀ x ∈ unitBall n, x ∈ ball p₀ (R / 64) →
              a ≤ q x / dirichletBoundaryDistanceProxy x ∧
                q x / dirichletBoundaryDistanceProxy x ≤ b) ∧
            b - a ≤ (1 - δ) * (M - m) + loss * (S + B * (2 * n : ℝ) * K) * R := by
  obtain ⟨δ, loss, hδ, hδ1, hLoss, hImprove⟩ :=
    exists_uniform_dirichlet_boundary_defect_improvement hn hc hK
  refine ⟨δ, loss, hδ, hδ1, hLoss, ?_⟩
  intro u hu huP hNorm hEll q hq hq0 S B hS hB hSource m M hmB hmM hMB p₀ hp₀ R hR hR1 hBounds
  let S' : ℝ := S + B * (2 * n : ℝ) * K
  have hS' : 0 ≤ S' := by dsimp [S']; positivity
  have hDefSource (x : E n) (hx : x ∈ unitBall n) :
      dirichletBilinearContraction e[n] (dirichletCofactorOperator u x)
        (realHessian (dirichletLowerBoundaryDefect q m) x) ≤ S' ∧
      dirichletBilinearContraction e[n] (dirichletCofactorOperator u x)
        (realHessian (dirichletUpperBoundaryDefect q M) x) ≤ S' := by
    have hq2 : ContDiffAt ℝ 2 q x :=
      (hq.contDiffAt (ball_subset_closedBall hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    exact dirichlet_boundary_defect_source_bounds e[n] (hNorm x hx) hB
      (fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hEll x hx v))
      hmB hmM hMB hq2 (hSource x hx)
  have hNonneg (x : E n) (hx : x ∈ closedUnitBall n) (hxCap : x ∈ ball p₀ (4 * R)) :
      0 ≤ dirichletLowerBoundaryDefect q m x ∧ 0 ≤ dirichletUpperBoundaryDefect q M x :=
    dirichlet_boundary_defects_nonnegative hq0 hx (fun hi => hBounds x hi hxCap)
  have hAlt := hImprove u hu huP hNorm hEll
    (dirichletLowerBoundaryDefect q m) (dirichletUpperBoundaryDefect q M)
    (smoothNear_dirichletLowerBoundaryDefect hq m) (smoothNear_dirichletUpperBoundaryDefect hq M)
    S' (M - m) hS' (sub_nonneg.mpr hmM)
    (fun x hx => (hDefSource x hx).1) (fun x hx => (hDefSource x hx).2)
    p₀ hp₀ R hR hR1
    (fun x hx hcap => (hNonneg x hx hcap).1) (fun x hx hcap => (hNonneg x hx hcap).2)
    (fun x _ _ => dirichlet_boundary_defect_sum q m M x)
  let f : E n → ℝ := fun x => q x / dirichletBoundaryDistanceProxy x
  let s : Set (E n) := unitBall n ∩ ball p₀ (R / 64)
  have hs : s.Nonempty := dirichlet_boundary_small_cap_nonempty hp₀ hR hR1
  have hBsmall (x : E n) (hx : x ∈ s) : m ≤ f x ∧ f x ≤ M :=
    hBounds x hx.1 (ball_subset_ball (by linarith) hx.2)
  have hAlternative :
      (∀ x ∈ s, δ * (M - m) - loss * S' * R ≤ f x - m) ∨
      (∀ x ∈ s, δ * (M - m) - loss * S' * R ≤ M - f x) := by
    rcases hAlt with hLo | hHi
    · left
      intro x hx
      have h := hLo x hx.1 hx.2
      rw [(dirichlet_boundary_defect_quotients q m M hx.1).1] at h
      exact h
    · right
      intro x hx
      have h := hHi x hx.1 hx.2
      rw [(dirichlet_boundary_defect_quotients q m M hx.1).2] at h
      exact h
  obtain ⟨a, b, hma, hbM, hab, hNew, hWidth⟩ :=
    dirichlet_interval_refinement_of_alternative hs f hBsmall hAlternative
  exact ⟨a, b, hma, hbM, hab, fun x hx hcap => hNew x ⟨hx, hcap⟩, hWidth⟩

end KEBall
