import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Ring

/-!
# Finite-frame contraction for complex covariant tensors

Stage03 source draft, not kernel checked. This module has no KE hypothesis,
no differential operator, and no assumed norm conclusion. The finite-frame
moment identities used below are verified for the actual metric frame by
MetricFrameMoments. Product frames then handle both covariant tensor slots.
-/

set_option autoImplicit false
open scoped BigOperators

namespace KEBall

/-- Reorder two finite linear combinations and factor their coefficients. -/
theorem sum_mul_linear_forms {α ι κ : Type*}
    [Fintype α] [Fintype ι] [Fintype κ]
    (p : ι → ℂ) (q : κ → ℂ) (c : α → ι → ℂ) (d : α → κ → ℂ) :
    (∑ a, (∑ i, p i * c a i) * (∑ j, q j * d a j)) =
      ∑ i, ∑ j, p i * q j * (∑ a, c a i * d a j) := by
  classical
  calc
    _ = ∑ a : α, ∑ i : ι, ∑ j : κ,
        (p i * c a i) * (q j * d a j) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ i : ι, ∑ a : α, ∑ j : κ,
        (p i * c a i) * (q j * d a j) := Finset.sum_comm
    _ = ∑ i : ι, ∑ j : κ, ∑ a : α,
        (p i * c a i) * (q j * d a j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem sq_twice_re (z : ℂ) :
    (2 * z.re) ^ 2 = 2 * (z * star z).re + 2 * (z * z).re := by
  classical
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- A real-part norm formula for any isotropic finite complex frame.
Both frame identities are mathematical hypotheses of this generic lemma;
the KE consumer proves them for its actual orthonormal basis. -/
theorem sum_sq_twice_re_of_moments {α ι : Type*} [Fintype α] [Fintype ι]
    (c : α → ι → ℂ) (B : ι → ι → ℂ) (p : ι → ℂ)
    (hpair : ∀ i j, (∑ a, c a i * star (c a j)) = B i j)
    (hhol : ∀ i j, (∑ a, c a i * c a j) = 0) :
    (∑ a, (2 * (∑ i, p i * c a i).re) ^ 2) =
      2 * (∑ i, ∑ j, p i * star (p j) * B i j).re := by
  classical
  have hp := sum_mul_linear_forms p (fun j => star (p j)) c
    (fun a j => star (c a j))
  have hh := sum_mul_linear_forms p p c c
  simp only [hpair] at hp
  simp only [hhol, mul_zero, Finset.sum_const_zero] at hh
  have hstar (a : α) :
      star (∑ i, p i * c a i) = ∑ i, star (p i) * star (c a i) := by
    change (starRingEnd ℂ) (∑ i, p i * c a i) = _
    simp only [map_sum, map_mul, starRingEnd_apply]
  calc
    _ = 2 * (∑ a, (∑ i, p i * c a i) *
          star (∑ i, p i * c a i)).re +
        2 * (∑ a, (∑ i, p i * c a i) * (∑ i, p i * c a i)).re := by
      calc
        _ = ∑ a, (2 * ((∑ i, p i * c a i) * star (∑ i, p i * c a i)).re +
            2 * ((∑ i, p i * c a i) * (∑ i, p i * c a i)).re) := by
          apply Finset.sum_congr rfl
          intro a _
          exact sq_twice_re _
        _ = _ := by
          simp only [Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
    _ = _ := by
      simp_rw [hstar]
      rw [hp, hh]
      simp

/-- Finite sums of products on independent factors separate exactly. -/
theorem sum_prod_pair_factor {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (h : β → ℂ) :
    (∑ a : α × β, f a.1 * h a.2) = (∑ a, f a) * (∑ b, h b) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

/-- The two-tensor identity. No symmetry of S is needed. Indices are ordered
as B(i,k) B(j,l), so the transpose convention is retained by the consumer. -/
theorem complex_tensor_real_norm_of_moments {α ι : Type*}
    [Fintype α] [Fintype ι]
    (c : α → ι → ℂ) (B S : ι → ι → ℂ)
    (hpair : ∀ i k, (∑ a, c a i * star (c a k)) = B i k)
    (hhol : ∀ i k, (∑ a, c a i * c a k) = 0) :
    (∑ a, ∑ b, (2 * (∑ i, ∑ j, S i j * c a i * c b j).re) ^ 2) =
      2 * (∑ i, ∑ j, ∑ k, ∑ l,
        B i k * B j l * S i j * star (S k l)).re := by
  classical
  let C : (α × α) → (ι × ι) → ℂ := fun a i => c a.1 i.1 * c a.2 i.2
  let Q : (ι × ι) → (ι × ι) → ℂ := fun i k => B i.1 k.1 * B i.2 k.2
  have hC (i k : ι × ι) : (∑ a : α × α, C a i * star (C a k)) = Q i k := by
    calc
      _ = ∑ a : α × α,
          (c a.1 i.1 * star (c a.1 k.1)) *
            (c a.2 i.2 * star (c a.2 k.2)) := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp [C]
        rw [map_mul]
        ring
      _ = _ := by
        rw [sum_prod_pair_factor
          (fun a => c a i.1 * star (c a k.1))
          (fun a => c a i.2 * star (c a k.2)), hpair, hpair]
  have hH (i k : ι × ι) : (∑ a : α × α, C a i * C a k) = 0 := by
    calc
      _ = ∑ a : α × α,
          (c a.1 i.1 * c a.1 k.1) * (c a.2 i.2 * c a.2 k.2) := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp [C]
        ring
      _ = _ := by
        rw [sum_prod_pair_factor (fun a => c a i.1 * c a k.1)
          (fun a => c a i.2 * c a k.2), hhol, hhol, mul_zero]
  have h := sum_sq_twice_re_of_moments C Q (fun i => S i.1 i.2) hC hH
  simp only [Fintype.sum_prod_type, C, Q] at h
  calc
    _ = ∑ a, ∑ b, (2 * (∑ i, ∑ j, S i j * (c a i * c b j)).re) ^ 2 := by
      simp only [mul_assoc]
    _ = 2 * (∑ i, ∑ j, ∑ k, ∑ l,
        S i j * star (S k l) * (B i k * B j l)).re := h
    _ = _ := by
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

end KEBall
