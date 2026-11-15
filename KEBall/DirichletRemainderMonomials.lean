import KEBall.DirichletDifferenceMonomials

/-! The exact product remainder belongs to the span of strictly lower-order-factor monomials. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000

open Metric Set
open scoped BigOperators

namespace KEBall

theorem dirichletDifferenceMonomial_erase_mul {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [DecidableEq ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A)
    (j a : ι → ℕ) (i : ι) (hi : i ∈ s) (m : ℕ) (x : E n) :
    dirichletDifferenceMonomial R τ (s.erase i) F j a x *
        dirichletIteratedFieldDifference R τ (F i) m x =
      dirichletDifferenceMonomial R τ s F (Function.update j i m) (Function.update a i 0) x := by
  classical
  let G (l : ι) := dirichletIteratedFieldDifference R τ (F l)
    (Function.update j i m l) (R^[Function.update a i 0 l] x)
  change _ = ∏ l ∈ s, G l
  rw [← Finset.prod_erase_mul s G hi]
  have hiG : G i = dirichletIteratedFieldDifference R τ (F i) m x := by
    simp only [G, Function.update_self, Function.iterate_zero, id_eq]
  rw [hiG]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  have hli := (Finset.mem_erase.mp hl).1
  simp only [G, Function.update_of_ne hli]

theorem dirichletProductDifferenceCoefficient_eq_monomial {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A) (k : ℕ) (i : ι) :
    dirichletProductDifferenceCoefficient R s F k i =
      dirichletDifferenceMonomial R τ (s.erase i) F (fun _ => 0)
        (fun l => if l < i then k + 1 else k) := by
  funext x
  change _ = ∏ l ∈ s.erase i, F l (R^[if l < i then k + 1 else k] x)
  have hEq (l : ι) : F l (R^[if l < i then k + 1 else k] x) =
      if l < i then F l (R^[k + 1] x) else F l (R^[k] x) := by
    by_cases h : l < i <;> simp [h]
  simp only [hEq]
  exact (dirichlet_prod_erase_mixed s (fun l => F l (R^[k + 1] x)) (fun l => F l (R^[k] x)) i).symm

theorem dirichlet_two_positive_profile {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i l : ι) (hi : i ∈ s) (hl : l ∈ s) (hli : l ≠ i)
    (m : ℕ) (hm : 0 < m) :
    (∑ q ∈ s, Function.update (Function.update (fun _ => 0) l 1) i m q) = m + 1 ∧
      ∀ q ∈ s, Function.update (Function.update (fun _ => 0) l 1) i m q < m + 1 := by
  have hEq : Function.update (Function.update (fun _ => 0) l 1) i m =
      fun q => (if q = i then m else 0) + (if q = l then 1 else 0) := by
    funext q
    by_cases hqi : q = i
    · subst q
      simp [hli.symm]
    · by_cases hql : q = l
      · subst q
        simp [hli]
      · simp only [Function.update_of_ne hqi, Function.update_of_ne hql, if_neg hqi, if_neg hql, add_zero]
  constructor
  · rw [hEq, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', hi, hl, if_true]
  · intro q hq
    by_cases hqi : q = i
    · subst q; simp only [Function.update_self]; omega
    · by_cases hql : q = l
      · subst q; simp only [Function.update_of_ne hli, Function.update_self]; omega
      · simp only [Function.update_of_ne hqi, Function.update_of_ne hql]; omega

theorem dirichlet_coefficient_error_mem_properSpan {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (s : Finset ι) (F : ι → E n → A) (k : ℕ) (i : ι) (hi : i ∈ s) :
    (fun R τ x => dirichletFieldDifference R τ (dirichletProductDifferenceCoefficient R s F k i) x *
      dirichletIteratedFieldDifference R τ (F i) (k + 1) x) ∈ dirichletProperDifferenceSpan s F (k + 2) := by
  classical
  let a (l : ι) := if l < i then k + 1 else k
  let j (l : ι) := Function.update (fun _ => 0) l 1
  let b (l : ι) (q : ι) := a q + if q < l then 1 else 0
  have hEq : (fun R τ x => dirichletFieldDifference R τ (dirichletProductDifferenceCoefficient R s F k i) x *
      dirichletIteratedFieldDifference R τ (F i) (k + 1) x) =
        ∑ l ∈ s.erase i, (fun R τ x => dirichletDifferenceMonomial R τ s F
          (Function.update (j l) i (k + 1)) (Function.update (b l) i 0) x) := by
    funext R τ x
    rw [dirichletProductDifferenceCoefficient_eq_monomial R τ,
      dirichletFieldDifference_monomial, Finset.sum_mul]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro l hl
    exact dirichletDifferenceMonomial_erase_mul R τ s F (j l) (b l) i hi (k + 1) x
  rw [hEq]
  apply Submodule.sum_mem
  intro l hl
  have hli := Finset.mem_erase.mp hl
  have hProf := dirichlet_two_positive_profile s i l hi hli.2 hli.1 (k + 1) (by omega)
  exact dirichletDifferenceMonomial_mem_properSpan s F _ _ hProf.1 hProf.2

theorem dirichletProductDifferenceRemainder_mem_properSpan {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (s : Finset ι) (F : ι → E n → A) (k : ℕ) :
    (fun R τ x => dirichletProductDifferenceRemainder R τ s F k x) ∈
      dirichletProperDifferenceSpan s F (k + 1) := by
  induction k with
  | zero => exact Submodule.zero_mem _
  | succ k ih =>
    have hDiff := dirichletFamilyDifference_mem_properSpan s F ih
    have hSum : (∑ i ∈ s, (fun R τ x =>
        dirichletFieldDifference R τ (dirichletProductDifferenceCoefficient R s F k i) x *
          dirichletIteratedFieldDifference R τ (F i) (k + 1) x)) ∈ dirichletProperDifferenceSpan s F (k + 2) :=
      Submodule.sum_mem _ (fun i hi => dirichlet_coefficient_error_mem_properSpan s F k i hi)
    have h := Submodule.add_mem _ hDiff hSum
    convert! h using 1
    funext R τ x
    simp only [Pi.add_apply, Finset.sum_apply, dirichletProductDifferenceRemainder]
    rfl

end KEBall
