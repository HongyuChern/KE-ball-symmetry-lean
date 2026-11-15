import KEBall.DirichletBoundaryIntervalContraction
import KEBall.DirichletBoundaryOscillation

/-!
# Boundary quotient oscillation contraction at ratio 1/256

Extrema are taken over the original quotient on the actual open-ball cap.
All constants are uniform for the prescribed coefficient, source and
quotient bounds; no boundary Hölder hypothesis is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_uniform_dirichlet_boundary_quotient_oscillation_step {n : ℕ} (hn : 2 ≤ n)
    {c K S B : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hS : 0 ≤ S) (hB : 0 ≤ B) :
    ∃ θ C : ℝ, 0 ≤ θ ∧ θ < 1 ∧ 0 ≤ C ∧
      ∀ (u : E n → ℝ), SmoothNear (closedUnitBall n) u →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, ‖dirichletCofactorOperator u x‖ ≤ K) →
        (∀ x ∈ unitBall n, ∀ v : E n,
          c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v) →
      ∀ (q : E n → ℝ), SmoothNear (closedUnitBall n) q →
        (∀ x ∈ unitSphere n, q x = 0) →
        (∀ x ∈ unitBall n, |q x / dirichletBoundaryDistanceProxy x| ≤ B) →
        (∀ x ∈ unitBall n,
          |dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian q x)| ≤ S) →
        ∀ p ∈ unitSphere n, ∀ R : ℝ, 0 < R → R ≤ 1 →
          dirichletBoundaryOscillation (fun x => q x / dirichletBoundaryDistanceProxy x) p (R / 256) ≤
            θ * dirichletBoundaryOscillation (fun x => q x / dirichletBoundaryDistanceProxy x) p R + C * R := by
  obtain ⟨δ, loss, hδ, hδ1, hLoss, hContract⟩ :=
    exists_uniform_dirichlet_boundary_interval_contraction hn hc hK
  let C : ℝ := loss * (S + B * (2 * n : ℝ) * K) / 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1 - δ, C, sub_nonneg.mpr hδ1.le, by linarith, hC, ?_⟩
  intro u hu huP hNorm hEll q hq hq0 hqB hSource p hp R hR hR1
  let f : E n → ℝ := fun x => q x / dirichletBoundaryDistanceProxy x
  let m : ℝ := sInf (f '' dirichletBoundaryCap p R)
  let M : ℝ := sSup (f '' dirichletBoundaryCap p R)
  have hGlobal (x : E n) (hx : x ∈ dirichletBoundaryCap p R) : -B ≤ f x ∧ f x ≤ B :=
    abs_le.mp (hqB x hx.1)
  obtain ⟨hmB, hMB, hmM, hRange⟩ := dirichlet_bounded_function_extrema
    (dirichletBoundaryCap_nonempty hp hR) f hGlobal
  obtain ⟨a, b, hma, hbM, hab, hNew, hWidth⟩ := hContract u hu huP hNorm hEll q hq hq0
    S B hS hB hSource m M hmB hmM hMB p hp (R / 4) (by positivity) (by linarith) (by
      intro x hx hxCap
      apply hRange x
      refine ⟨hx, ?_⟩
      simpa only [show 4 * (R / 4) = R by ring] using hxCap)
  have hNew' (x : E n) (hx : x ∈ dirichletBoundaryCap p (R / 256)) : a ≤ f x ∧ f x ≤ b := by
    apply hNew x hx.1
    simpa only [show (R / 4) / 64 = R / 256 by ring] using hx.2
  have hOsc := (dirichletBoundaryOscillation_le_of_bounds f hp (by positivity) hNew').2
  calc
    _ ≤ b - a := hOsc
    _ ≤ (1 - δ) * (M - m) + loss * (S + B * (2 * n : ℝ) * K) * (R / 4) := hWidth
    _ = (1 - δ) * dirichletBoundaryOscillation f p R + C * R := by
      change (1 - δ) * (M - m) + loss * (S + B * (2 * n : ℝ) * K) * (R / 4) =
        (1 - δ) * (M - m) + C * R
      dsimp [C]
      ring

end KEBall
