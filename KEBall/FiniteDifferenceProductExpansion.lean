import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Group.Pi.Basic

/-! A finite expansion for an additive operator with an exact indexed
Leibniz rule. This module is independent of all geometric and analytic
imports. The profile and term count are preserved at every order. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped BigOperators

namespace KEBall

theorem dirichlet_difference_profile_increment_sum {m k : ℕ}
    (j : Fin m → ℕ) (hj : ∑ l, j l = k) (i : Fin m) :
    (∑ l, Function.update j i (j i + 1) l) = k + 1 := by
  classical
  have he : Function.update j i (j i + 1) = fun l => j l + if l = i then 1 else 0 := by
    funext l
    by_cases h : l = i
    · subst l; simp
    · simp only [Function.update_of_ne h, if_neg h, add_zero]
  rw [he, Finset.sum_add_distrib, hj]
  simp

theorem iterated_additive_operator_profile_expansion {X A : Type*}
    [AddCommMonoid A] {m : ℕ}
    (D : (X → A) →+ (X → A))
    (M : ((Fin m → ℕ) × (Fin m → ℕ)) → X → A)
    (hStep : ∀ p : (Fin m → ℕ) × (Fin m → ℕ), D (M p) = ∑ i : Fin m,
      M (Function.update p.1 i (p.1 i + 1), fun l => p.2 l + if l < i then 1 else 0))
    (k : ℕ) :
    ∃ L : List ((Fin m → ℕ) × (Fin m → ℕ)),
      L.length = m ^ k ∧
      (∀ p ∈ L, ∑ i, p.1 i = k) ∧
      D^[k] (M (fun _ => 0, fun _ => 0)) = (L.map M).sum := by
  classical
  induction k with
  | zero =>
    refine ⟨[(fun _ => 0, fun _ => 0)], by simp, ?_, by simp⟩
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    simp
  | succ k ih =>
    obtain ⟨L, hLen, hProfile, hExpansion⟩ := ih
    let step (p : (Fin m → ℕ) × (Fin m → ℕ)) := List.ofFn
      (fun i : Fin m => (Function.update p.1 i (p.1 i + 1),
        fun l => p.2 l + if l < i then 1 else 0))
    refine ⟨L.flatMap step, ?_, ?_, ?_⟩
    · simp only [List.length_flatMap, step, List.length_ofFn]
      simp only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, hLen, pow_succ]
    · intro p hp
      obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpq
      subst p
      exact dirichlet_difference_profile_increment_sum q.1 (hProfile q hq) i
    · rw [Function.iterate_succ_apply', hExpansion, ← List.sum_hom (L.map M) D]
      simp only [List.flatMap_def, List.map_flatten, List.sum_flatten,
        List.map_map, Function.comp_def, hStep, step, List.map_ofFn, List.sum_ofFn]

end KEBall
