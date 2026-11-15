import KEBall.DirichletBoundaryHolderGluing
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! A common boundary-gluing constant for an arbitrary indexed family.
The family is lifted to a bounded continuous function space on the discrete
index set, so the existential constant precedes every index.  Draft. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped NNReal

noncomputable section
namespace KEBall

theorem exists_uniform_dirichlet_closedBall_holder_of_boundary_power
    {n : ℕ} (hn : 0 < n) {J F : Type*} [NormedAddCommGroup F]
    (f : J → E n → F) {B C H K α β η : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hη : 0 < η)
    (hBound : ∀ j x, x ∈ closedUnitBall n → ‖f j x‖ ≤ B)
    (hBoundary : ∀ j p, p ∈ unitSphere n → ∀ q, q ∈ unitSphere n →
      ‖f j p - f j q‖ ≤ K * dist p q ^ α)
    (hApproach : ∀ j x, x ∈ closedUnitBall n → 1 - ‖x‖ ≤ 1 / 2 →
      ∀ p, p ∈ unitSphere n → dist x p = 1 - ‖x‖ →
        ‖f j x - f j p‖ ≤ C * (1 - ‖x‖) ^ η)
    (hInterior : ∀ j x, x ∈ unitBall n → ∀ y, y ∈ ball x ((1 - ‖x‖) / 8) →
      ‖f j x - f j y‖ ≤ (H / (1 - ‖x‖) ^ β) * dist x y ^ β) :
    ∃ θ : ℝ≥0, (θ : ℝ) = min η (min α β) / 2 ∧ 0 < θ ∧ θ < 1 ∧
      ∃ M : ℝ≥0, ∀ j, HolderOnWith M θ (f j) (closedUnitBall n) := by
  classical
  letI : TopologicalSpace J := ⊥
  letI : DiscreteTopology J := ⟨rfl⟩
  let F' : E n → BoundedContinuousFunction J F := fun x =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun j => if x ∈ closedUnitBall n then f j x else 0)
      continuous_of_discreteTopology B (by
        intro j
        split_ifs with hx
        · exact hBound j x hx
        · simpa only [norm_zero] using hB)
  have hEval (x : E n) (hx : x ∈ closedUnitBall n) (j : J) : F' x j = f j x := by
    change (if x ∈ closedUnitBall n then f j x else 0) = _
    rw [if_pos hx]
  have hN (x : E n) (hx : x ∈ closedUnitBall n) : ‖F' x‖ ≤ B := by
    apply (BoundedContinuousFunction.norm_le hB).mpr
    intro j
    rw [hEval x hx]
    exact hBound j x hx
  have hSub {x y : E n} (hx : x ∈ closedUnitBall n) (hy : y ∈ closedUnitBall n)
      {T : ℝ} (hT : 0 ≤ T) (h : ∀ j, ‖f j x - f j y‖ ≤ T) :
      ‖F' x - F' y‖ ≤ T := by
    apply (BoundedContinuousFunction.norm_le hT).mpr
    intro j
    simpa only [BoundedContinuousFunction.sub_apply, hEval x hx, hEval y hy] using h j
  have hBdy (p : E n) (hp : p ∈ unitSphere n) (q : E n) (hq : q ∈ unitSphere n) :
      ‖F' p - F' q‖ ≤ K * dist p q ^ α :=
    hSub (sphere_subset_closedBall hp) (sphere_subset_closedBall hq) (by positivity)
      (fun j => hBoundary j p hp q hq)
  have hApp (x : E n) (hx : x ∈ closedUnitBall n) (hs : 1 - ‖x‖ ≤ 1 / 2)
      (p : E n) (hp : p ∈ unitSphere n) (hd : dist x p = 1 - ‖x‖) :
      ‖F' x - F' p‖ ≤ C * (1 - ‖x‖) ^ η := by
    have hr : 0 ≤ 1 - ‖x‖ := sub_nonneg.mpr (mem_closedBall_zero_iff.mp hx)
    exact hSub hx (sphere_subset_closedBall hp) (by positivity)
      (fun j => hApproach j x hx hs p hp hd)
  have hInt (x : E n) (hx : x ∈ unitBall n)
      (y : E n) (hy : y ∈ ball x ((1 - ‖x‖) / 8)) :
      ‖F' x - F' y‖ ≤ (H / (1 - ‖x‖) ^ β) * dist x y ^ β := by
    have hr : 0 < 1 - ‖x‖ := sub_pos.mpr (mem_ball_zero_iff.mp hx)
    have hyB : y ∈ closedUnitBall n := by
      apply mem_closedBall_zero_iff.mpr
      have ht := norm_le_norm_sub_add y x
      have hyD : ‖y - x‖ < (1 - ‖x‖) / 8 := by simpa only [mem_ball, dist_eq_norm] using hy
      linarith only [ht, hyD, hr]
    exact hSub (ball_subset_closedBall hx) hyB (by positivity)
      (fun j => hInterior j x hx y hy)
  obtain ⟨θ, hθ, hθ0, hθ1, M, hHolder⟩ :=
    exists_dirichlet_closedBall_holder_of_boundary_power hn hB hC hH hK hα hα1 hβ hη
      hN hBdy hApp hInt
  refine ⟨θ, hθ, hθ0, hθ1, M, ?_⟩
  intro j
  apply dirichlet_holderOnWith_of_norm_bound M.coe_nonneg θ.coe_nonneg
  intro x hx y hy
  have h := hHolder.dist_le hx hy
  simp only [dist_eq_norm] at h
  have he := (F' x - F' y).norm_coe_le_norm j
  simp only [BoundedContinuousFunction.sub_apply, hEval x hx, hEval y hy] at he
  exact he.trans h

end KEBall
