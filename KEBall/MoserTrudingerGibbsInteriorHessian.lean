import KEBall.DirichletPoissonLocalSchauder
import KEBall.MoserTrudingerGibbsLaplacianHolder
import KEBall.MoserTrudingerGibbsClosedGradientHolder

/-! Uniform interior bounds for the full real Hessian of actual Gibbs
outputs, obtained from the genuine Poisson equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000

open Metric Set
open scoped ComplexOrder ContDiff Laplacian NNReal

namespace KEBall.MoserTrudinger
open DifferentialGeometry.Analysis.Schauder

private theorem holder_zero_on_of_bound {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : E n → F} {s : Set (E n)} {A : ℝ≥0} (h : ∀ x ∈ s, ‖f x‖ ≤ A) :
    HolderOnWith (2 * A) 0 f s :=
  HolderWith.restrict_iff.mp (holderWith_zero_of_norm_le (fun x : s => h x x.property))

theorem exists_uniform_interior_realHessian_holder_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ β : ℝ≥0, 0 < β ∧ β < 1 ∧
      ∀ (p : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall p (2 * R) ⊆ unitBall n →
        ∃ C : ℝ≥0, ∀ j,
          (∀ x ∈ ball p (R / 8), ‖fderiv ℝ (fderiv ℝ (u (j + 2))) x‖ ≤ C) ∧
          HolderOnWith C β (fderiv ℝ (fderiv ℝ (u (j + 2)))) (ball p (R / 8)) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration
      (by omega) hγ hu hu0 huP hEq hM huB
  obtain ⟨θ, KG, hθ, hθ1, hGH⟩ :=
    exists_uniform_closed_gradient_holder_of_smoothGibbs_bounds hn hD hG.le
      hu hu0 huP hTrace hGrad
  obtain ⟨α, KL, hα, _, hKL, hLH⟩ :=
    exists_uniform_laplacian_holder_of_bounded_smoothGibbsIteration hn hγ hu hu0 huP hEq hM huB
  let a : ℝ≥0 := ⟨α, hα.le⟩
  let β : ℝ≥0 := min a θ / 2
  have hβ : 0 < β := div_pos (lt_min (show 0 < a from hα) hθ) (by norm_num)
  have hβmin : β ≤ min a θ := div_le_self (by positivity) (by norm_num)
  have hβa : β ≤ a := hβmin.trans (min_le_left _ _)
  have hβθ : β ≤ θ := hβmin.trans (min_le_right _ _)
  have hβ1 : β < 1 := hβθ.trans_lt hθ1
  let A : ℝ≥0 := Real.toNNReal B
  let Gn : ℝ≥0 := ⟨G, hG.le⟩
  let L : ℝ≥0 := ⟨4 * D, by positivity⟩
  have hAmp (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) : ‖u j x‖ ≤ A := by
    rw [Real.norm_eq_abs, abs_of_nonpos (huB j x hx).2]
    have hneg : -u j x ≤ B := by linarith only [(huB j x hx).1]
    exact hneg.trans (Real.le_coe_toNNReal B)
  have hLip (j : ℕ) : LipschitzOnWith Gn (u j) (closedUnitBall n) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall (0 : E n) 1)
    · intro x _
      exact (hu j).differentiable (by simp) x
    · intro x hx
      exact_mod_cast hGrad j x hx
  have hUH (j : ℕ) : HolderOnWith (max (2 * A) Gn) β (u j) (closedUnitBall n) :=
    (holder_zero_on_of_bound (hAmp j)).of_le_of_le (hLip j).holderOnWith (by positivity) hβ1.le
  have hGH' (j : ℕ) : HolderOnWith (max (2 * Gn) KG) β
      (fderiv ℝ (u (j + 2))) (closedUnitBall n) := by
    have hz : HolderOnWith (2 * Gn) 0 (fderiv ℝ (u (j + 2))) (closedUnitBall n) :=
      holder_zero_on_of_bound (hGrad (j + 2))
    exact hz.of_le_of_le (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hGH (j + 1))
      (by positivity) hβθ
  have hLap (j : ℕ) (x : E n) (hx : x ∈ unitBall n) : ‖Δ (u (j + 2)) x‖ ≤ L := by
    have htr : (complexHessian (u (j + 2)) x).trace.re ≤ D := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using hTrace (j + 1) x (ball_subset_closedBall hx)
    have htr0 := (dirichlet_posDef_trace_re_pos (huP (j + 2) x hx)).le
    rw [euclideanLaplacian_eq_four_complexHessian_trace_re (hu (j + 2)).contDiffAt,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) htr0)]
    exact mul_le_mul_of_nonneg_left htr (by norm_num)
  refine ⟨β, hβ, hβ1, ?_⟩
  intro p R hR hR1 hBall
  have hSub : closedBall p (R / 4) ⊆ unitBall n :=
    (closedBall_subset_closedBall (by linarith : R / 4 ≤ 2 * R)).trans hBall
  have hSubC : closedBall p (R / 4) ⊆ closedUnitBall n := hSub.trans ball_subset_closedBall
  have hSubHalf : closedBall p (R / 4) ⊆ ball p (R / 2) := closedBall_subset_ball (by linarith)
  let Kr : ℝ≥0 := ⟨KL * (8 / R) ^ α, mul_nonneg hKL (Real.rpow_nonneg (by positivity) _)⟩
  have hLocalLH (j : ℕ) : HolderOnWith Kr a (Δ (u (j + 2))) (closedBall p (R / 4)) := by
    apply dirichlet_holderOnWith_of_norm_bound
    intro x hx y hy
    simpa only [Real.norm_eq_abs] using hLH j p R hR hR1 hBall x (hSubHalf hx) y (hSubHalf hy)
  have hLocalLH' (j : ℕ) : HolderOnWith (max (2 * L) Kr) β
      (Δ (u (j + 2))) (closedBall p (R / 4)) :=
    (holder_zero_on_of_bound (fun x hx => hLap j x (hSub hx))).of_le_of_le
      (hLocalLH j) (by positivity) hβa
  obtain ⟨C, hC⟩ := exists_uniform_local_poisson_hessian_holder (by omega : 0 < n)
    p (by positivity : 0 < R / 4) β A Gn L (max (2 * A) Gn)
    (max (2 * Gn) KG) (max (2 * L) Kr) hβ hβ1
  refine ⟨C, ?_⟩
  intro j
  have h := hC (u (j + 2)) (hu (j + 2))
    (fun x hx => hAmp (j + 2) x (hSubC hx))
    (fun x hx => hGrad (j + 2) x (hSubC hx))
    (fun x hx => hLap j x (hSub hx))
    ((hUH (j + 2)).mono hSubC) ((hGH' j).mono hSubC) (hLocalLH' j)
  simpa only [show R / 4 / 2 = R / 8 by ring] using h

end KEBall.MoserTrudinger
