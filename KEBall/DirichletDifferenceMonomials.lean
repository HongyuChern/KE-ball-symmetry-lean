import KEBall.DirichletProductResidualBound
import Mathlib.LinearAlgebra.Span.Basic

/-! Exact spatial-difference rule for finite shifted monomials. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000

open Metric Set
open scoped BigOperators

namespace KEBall

theorem dirichletFieldDifference_iterate_comp {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (F : E n → V) (a : ℕ) (x : E n) :
    dirichletFieldDifference R τ (fun y => F (R^[a] y)) x =
      dirichletFieldDifference R τ F (R^[a] x) := by
  have h : R^[a] (R x) = R (R^[a] x) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  simp only [dirichletFieldDifference, h]

noncomputable def dirichletDifferenceMonomial {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A)
    (j a : ι → ℕ) (x : E n) : A :=
  ∏ i ∈ s, dirichletIteratedFieldDifference R τ (F i) (j i) (R^[a i] x)

theorem dirichletDifferenceMonomial_increment {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A)
    (j a : ι → ℕ) (i : ι) (hi : i ∈ s) (x : E n) :
    dirichletDifferenceMonomial R τ s F (Function.update j i (j i + 1))
        (fun l => a l + if l < i then 1 else 0) x =
      ((∏ l ∈ s with l < i, dirichletIteratedFieldDifference R τ (F l) (j l) (R^[a l] (R x))) *
        (∏ l ∈ s with i < l, dirichletIteratedFieldDifference R τ (F l) (j l) (R^[a l] x))) *
          dirichletIteratedFieldDifference R τ (F i) (j i + 1) (R^[a i] x) := by
  classical
  let G (l : ι) := dirichletIteratedFieldDifference R τ (F l)
    (Function.update j i (j i + 1) l) (R^[a l + if l < i then 1 else 0] x)
  change (∏ l ∈ s, G l) = _
  rw [← Finset.prod_erase_mul s G hi]
  have hiG : G i = dirichletIteratedFieldDifference R τ (F i) (j i + 1) (R^[a i] x) := by
    simp only [G, Function.update_self, lt_self_iff_false, if_false, add_zero]
  rw [hiG]
  congr 1
  calc
    (∏ l ∈ s.erase i, G l) = ∏ l ∈ s.erase i,
        if l < i then dirichletIteratedFieldDifference R τ (F l) (j l) (R^[a l] (R x))
          else dirichletIteratedFieldDifference R τ (F l) (j l) (R^[a l] x) := by
      apply Finset.prod_congr rfl
      intro l hl
      have hli : l ≠ i := (Finset.mem_erase.mp hl).1
      dsimp only [G]
      rw [Function.update_of_ne hli]
      by_cases hlt : l < i
      · simp only [if_pos hlt, Function.iterate_succ_apply]
      · simp only [if_neg hlt, add_zero]
    _ = _ := dirichlet_prod_erase_mixed s _ _ i

theorem dirichletFieldDifference_monomial {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A)
    (j a : ι → ℕ) (x : E n) :
    dirichletFieldDifference R τ (dirichletDifferenceMonomial R τ s F j a) x =
      ∑ i ∈ s, dirichletDifferenceMonomial R τ s F (Function.update j i (j i + 1))
        (fun l => a l + if l < i then 1 else 0) x := by
  change dirichletFieldDifference R τ
    (fun y => ∏ i ∈ s, dirichletIteratedFieldDifference R τ (F i) (j i) (R^[a i] y)) x = _
  rw [dirichletFieldDifference_finsetProd]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dirichletDifferenceMonomial_increment R τ s F j a i hi x,
    dirichletFieldDifference_iterate_comp]
  rfl

theorem dirichlet_proper_profile_increment {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (j : ι → ℕ) {k : ℕ} (hSum : ∑ l ∈ s, j l = k)
    (hj : ∀ l ∈ s, j l < k) (i : ι) (hi : i ∈ s) :
    (∑ l ∈ s, Function.update j i (j i + 1) l) = k + 1 ∧
      ∀ l ∈ s, Function.update j i (j i + 1) l < k + 1 := by
  have hEq : Function.update j i (j i + 1) = fun l => j l + if l = i then 1 else 0 := by
    funext l
    by_cases hli : l = i
    · subst l; simp
    · simp only [Function.update_of_ne hli, if_neg hli, add_zero]
  constructor
  · rw [hEq, Finset.sum_add_distrib, hSum]
    simp only [Finset.sum_ite_eq', hi, if_true]
  · intro l hl
    rw [hEq]
    dsimp only
    have h := hj l hl
    split_ifs <;> omega

noncomputable def dirichletFamilyDifference {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ((E n ≃ₗᵢ[ℝ] E n) → ℝ → E n → V) →ₗ[ℝ] ((E n ≃ₗᵢ[ℝ] E n) → ℝ → E n → V) where
  toFun F R τ x := dirichletFieldDifference R τ (F R τ) x
  map_add' F G := by
    funext R τ x
    change dirichletFieldDifference R τ (fun y => F R τ y + G R τ y) x = _
    rw [dirichletFieldDifference_add]
    rfl
  map_smul' c F := by
    funext R τ x
    change τ⁻¹ • (c • F R τ (R x) - c • F R τ x) = c • (τ⁻¹ • (F R τ (R x) - F R τ x))
    rw [← smul_sub, smul_comm]

noncomputable def dirichletProperDifferenceSpan {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A]
    (s : Finset ι) (F : ι → E n → A) (k : ℕ) :
    Submodule ℝ ((E n ≃ₗᵢ[ℝ] E n) → ℝ → E n → A) :=
  Submodule.span ℝ {G | ∃ (j a : ι → ℕ), (∑ i ∈ s, j i) = k ∧
    (∀ i ∈ s, j i < k) ∧ G = fun R τ x => dirichletDifferenceMonomial R τ s F j a x}

theorem dirichletDifferenceMonomial_mem_properSpan {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A]
    (s : Finset ι) (F : ι → E n → A) {k : ℕ} (j a : ι → ℕ)
    (hSum : ∑ i ∈ s, j i = k) (hj : ∀ i ∈ s, j i < k) :
    (fun R τ x => dirichletDifferenceMonomial R τ s F j a x) ∈ dirichletProperDifferenceSpan s F k :=
  Submodule.subset_span ⟨j, a, hSum, hj, rfl⟩

theorem dirichletFamilyDifference_mem_properSpan {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (s : Finset ι) (F : ι → E n → A) {k : ℕ}
    {G : (E n ≃ₗᵢ[ℝ] E n) → ℝ → E n → A}
    (hG : G ∈ dirichletProperDifferenceSpan s F k) :
    dirichletFamilyDifference G ∈ dirichletProperDifferenceSpan s F (k + 1) := by
  apply Submodule.span_induction (p := fun G _ => dirichletFamilyDifference G ∈ dirichletProperDifferenceSpan s F (k + 1))
    ?_ ?_ ?_ ?_ hG
  · rintro G ⟨j, a, hSum, hj, rfl⟩
    have hEq : dirichletFamilyDifference (fun R τ x => dirichletDifferenceMonomial R τ s F j a x) =
        ∑ i ∈ s, (fun R τ x => dirichletDifferenceMonomial R τ s F (Function.update j i (j i + 1))
          (fun l => a l + if l < i then 1 else 0) x) := by
      funext R τ x
      change dirichletFieldDifference R τ (dirichletDifferenceMonomial R τ s F j a) x = _
      simpa only [Finset.sum_apply] using dirichletFieldDifference_monomial R τ s F j a x
    rw [hEq]
    apply Submodule.sum_mem
    intro i hi
    have hProf := dirichlet_proper_profile_increment s j hSum hj i hi
    exact dirichletDifferenceMonomial_mem_properSpan s F _ _ hProf.1 hProf.2
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro G H _ _ hG hH
    rw [map_add]
    exact Submodule.add_mem _ hG hH
  · intro c G _ hG
    rw [map_smul]
    exact Submodule.smul_mem _ c hG

end KEBall
