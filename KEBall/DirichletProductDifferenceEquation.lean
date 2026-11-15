import KEBall.DirichletIteratedTensorDifferences
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# An exact leading-term equation for arbitrary iterated product differences

All factors are evaluated on the actual orthogonal orbit. The remainder is
defined recursively from lower-order differences, with no regularity assumptions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped BigOperators

namespace KEBall

theorem dirichletFieldDifference_finsetSum {n : ℕ} {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → V) :
    dirichletFieldDifference R τ (fun x => ∑ i ∈ s, F i x) =
      fun x => ∑ i ∈ s, dirichletFieldDifference R τ (F i) x := by
  funext x
  simp only [dirichletFieldDifference, ← Finset.sum_sub_distrib, Finset.smul_sum]

theorem dirichletFieldDifference_mul {n : ℕ} {A : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (f g : E n → A) (x : E n) :
    dirichletFieldDifference R τ (fun y => f y * g y) x =
      f (R x) * dirichletFieldDifference R τ g x +
        dirichletFieldDifference R τ f x * g x := by
  simp only [dirichletFieldDifference, Algebra.smul_def]
  ring

theorem dirichletIteratedFieldDifference_finsetSum {n : ℕ} {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → V) (k : ℕ) :
    dirichletIteratedFieldDifference R τ (fun x => ∑ i ∈ s, F i x) k =
      fun x => ∑ i ∈ s, dirichletIteratedFieldDifference R τ (F i) k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dirichletIteratedFieldDifference, ih, dirichletFieldDifference_finsetSum]
    rfl

theorem dirichletIteratedFieldDifference_const_mul {n : ℕ} {A : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (c : A) (F : E n → A) (k : ℕ) :
    dirichletIteratedFieldDifference R τ (fun x => c * F x) k =
      fun x => c * dirichletIteratedFieldDifference R τ F k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dirichletIteratedFieldDifference, ih]
    funext x
    simp only [dirichletIteratedFieldDifference, dirichletFieldDifference, Algebra.smul_def]
    ring

theorem dirichletFieldDifference_finsetProd {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A) (x : E n) :
    dirichletFieldDifference R τ (fun y => ∏ i ∈ s, F i y) x =
      ∑ i ∈ s, ((∏ j ∈ s with j < i, F j (R x)) * (∏ j ∈ s with i < j, F j x)) *
        dirichletFieldDifference R τ (F i) x := by
  classical
  have h := Finset.prod_add_ordered s (fun i => F i x) (fun i => F i (R x) - F i x)
  simp only [add_sub_cancel] at h
  unfold dirichletFieldDifference
  dsimp only
  rw [h, add_sub_cancel_left, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Algebra.smul_def]
  ring

noncomputable def dirichletProductDifferenceCoefficient {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (s : Finset ι) (F : ι → E n → A) (k : ℕ) (i : ι) (x : E n) : A :=
  (∏ j ∈ s with j < i, F j (R^[k + 1] x)) * (∏ j ∈ s with i < j, F j (R^[k] x))

theorem dirichletProductDifferenceCoefficient_shift {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (s : Finset ι) (F : ι → E n → A) (k : ℕ) (i : ι) (x : E n) :
    dirichletProductDifferenceCoefficient R s F k i (R x) =
      dirichletProductDifferenceCoefficient R s F (k + 1) i x := by
  simp only [dirichletProductDifferenceCoefficient, Function.iterate_succ_apply]

noncomputable def dirichletProductDifferenceRemainder {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A) : ℕ → E n → A
  | 0 => fun _ => 0
  | k + 1 => fun x => dirichletFieldDifference R τ (dirichletProductDifferenceRemainder R τ s F k) x +
      ∑ i ∈ s, dirichletFieldDifference R τ (dirichletProductDifferenceCoefficient R s F k i) x *
        dirichletIteratedFieldDifference R τ (F i) (k + 1) x

theorem dirichletIteratedFieldDifference_finsetProd_eq {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A) (k : ℕ) :
    dirichletIteratedFieldDifference R τ (fun y => ∏ i ∈ s, F i y) (k + 1) =
      fun x => (∑ i ∈ s, dirichletProductDifferenceCoefficient R s F k i x *
        dirichletIteratedFieldDifference R τ (F i) (k + 1) x) +
        dirichletProductDifferenceRemainder R τ s F k x := by
  induction k with
  | zero =>
    funext x
    simpa only [dirichletIteratedFieldDifference, dirichletProductDifferenceRemainder,
      dirichletProductDifferenceCoefficient, Function.iterate_zero, Function.iterate_one,
      id_eq, add_zero, Nat.zero_add] using dirichletFieldDifference_finsetProd R τ s F x
  | succ k ih =>
    rw [dirichletIteratedFieldDifference, ih, dirichletFieldDifference_add,
      dirichletFieldDifference_finsetSum]
    funext x
    have hTop (i : ι) : dirichletFieldDifference R τ
        (dirichletIteratedFieldDifference R τ (F i) (k + 1)) x =
        dirichletIteratedFieldDifference R τ (F i) (k + 1 + 1) x := rfl
    simp only [dirichletFieldDifference_mul, dirichletProductDifferenceCoefficient_shift,
      dirichletProductDifferenceRemainder, Finset.sum_add_distrib, hTop]
    change (_ + _) + _ = _ + (_ + _)
    abel

theorem continuousOn_dirichlet_orthogonal_iterate_comp {n : ℕ} {V : Type*}
    [TopologicalSpace V] (R : E n ≃ₗᵢ[ℝ] E n) {F : E n → V}
    (hF : ContinuousOn F (closedUnitBall n)) (k : ℕ) :
    ContinuousOn (fun x => F (R^[k] x)) (closedUnitBall n) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    simpa only [Function.iterate_succ_apply] using continuousOn_dirichlet_orthogonal_comp ih R

theorem continuousOn_dirichletProductDifferenceCoefficient {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (s : Finset ι) (F : ι → E n → A)
    (hF : ∀ i ∈ s, ContinuousOn (F i) (closedUnitBall n)) (k : ℕ) (i : ι) :
    ContinuousOn (dirichletProductDifferenceCoefficient R s F k i) (closedUnitBall n) := by
  have hL : ContinuousOn (fun x => ∏ j ∈ s with j < i, F j (R^[k + 1] x)) (closedUnitBall n) :=
    continuousOn_finsetProd _ (fun j hj =>
      continuousOn_dirichlet_orthogonal_iterate_comp R (hF j (Finset.mem_filter.mp hj).1) (k + 1))
  have hR : ContinuousOn (fun x => ∏ j ∈ s with i < j, F j (R^[k] x)) (closedUnitBall n) :=
    continuousOn_finsetProd _ (fun j hj =>
      continuousOn_dirichlet_orthogonal_iterate_comp R (hF j (Finset.mem_filter.mp hj).1) k)
  exact hL.mul hR

theorem continuousOn_dirichletProductDifferenceRemainder {n : ℕ} {A ι : Type*}
    [NormedCommRing A] [NormedAlgebra ℝ A] [LinearOrder ι]
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (s : Finset ι) (F : ι → E n → A)
    (hF : ∀ i ∈ s, ContinuousOn (F i) (closedUnitBall n)) (k : ℕ) :
    ContinuousOn (dirichletProductDifferenceRemainder R τ s F k) (closedUnitBall n) := by
  induction k with
  | zero => exact continuousOn_const
  | succ k ih =>
    exact (continuousOn_dirichletFieldDifference R τ ih).add
      (continuousOn_finsetSum _ (fun i hi =>
        (continuousOn_dirichletFieldDifference R τ
          (continuousOn_dirichletProductDifferenceCoefficient R s F hF k i)).mul
        (continuousOn_dirichletIteratedFieldDifference R τ (hF i hi) (k + 1))))

end KEBall
