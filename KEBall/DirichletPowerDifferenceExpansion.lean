import KEBall.FiniteDifferenceProductExpansion
import KEBall.DirichletDifferenceMonomials

/-! Instantiate the algebraic expansion with the actual normalized
orthogonal difference. All additive and Leibniz laws are proved here
from the existing concrete difference definitions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000
open scoped BigOperators

namespace KEBall

theorem dirichletIteratedFieldDifference_product_expansion {n m : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F : Fin m → E n → ℝ) (k : ℕ) :
    ∃ L : List ((Fin m → ℕ) × (Fin m → ℕ)),
      L.length = m ^ k ∧
      (∀ p ∈ L, ∑ i, p.1 i = k) ∧
      ∀ x, dirichletIteratedFieldDifference R τ (fun y => ∏ i, F i y) k x =
        (L.map (fun p => dirichletDifferenceMonomial R τ Finset.univ F p.1 p.2 x)).sum := by
  classical
  let D : (E n → ℝ) →+ (E n → ℝ) :=
    { toFun := dirichletFieldDifference R τ
      map_zero' := by funext x; simp [dirichletFieldDifference]
      map_add' := fun f g => dirichletFieldDifference_add R τ f g }
  let M (p : (Fin m → ℕ) × (Fin m → ℕ)) :=
    dirichletDifferenceMonomial R τ Finset.univ F p.1 p.2
  have hStep : ∀ p : (Fin m → ℕ) × (Fin m → ℕ), D (M p) = ∑ i : Fin m,
      M (Function.update p.1 i (p.1 i + 1), fun l => p.2 l + if l < i then 1 else 0) := by
    intro p
    funext x
    have hD : D (M p) x = dirichletFieldDifference R τ
        (dirichletDifferenceMonomial R τ Finset.univ F p.1 p.2) x := rfl
    rw [hD]
    simpa only [M, Finset.sum_apply] using
      dirichletFieldDifference_monomial R τ Finset.univ F p.1 p.2 x
  have hM0 : M (fun _ => 0, fun _ => 0) = (fun x => ∏ i, F i x) := by
    funext x
    simp only [M, dirichletDifferenceMonomial, dirichletIteratedFieldDifference,
      Function.iterate_zero, id_eq]
  have hIter (f : E n → ℝ) (j : ℕ) : D^[j] f = dirichletIteratedFieldDifference R τ f j := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
  obtain ⟨L, hLen, hProfile, hValue⟩ := iterated_additive_operator_profile_expansion D M hStep k
  rw [hM0, hIter] at hValue
  refine ⟨L, hLen, hProfile, ?_⟩
  intro x
  have hEval (L' : List ((Fin m → ℕ) × (Fin m → ℕ))) :
      ((L'.map M).sum) x = (L'.map (fun p => M p x)).sum := by
    induction L' with
    | nil => rfl
    | cons p L' ih =>
      simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using
        congrArg (fun z : ℝ => M p x + z) ih
  exact (congrFun hValue x).trans (hEval L)

end KEBall
