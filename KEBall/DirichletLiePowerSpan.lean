import KEBall.DirichletPolynomialCoefficientSpan

/-! Finite ordered products in a Lie-closed real subspace are spanned by pure powers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
open Polynomial
namespace KEBall

noncomputable def dirichletLieWordSpan {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) (k : ℕ) : Submodule ℝ A :=
  Submodule.span ℝ {a | ∃ w : List A, w.length ≤ k ∧ (∀ x ∈ w, x ∈ L) ∧ w.prod = a}

noncomputable def dirichletLiePowerSpan {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) (k : ℕ) : Submodule ℝ A :=
  Submodule.span ℝ {a | ∃ x ∈ L, ∃ j ≤ k, x ^ j = a}

theorem dirichletLieWordSpan_mono {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) {j k : ℕ} (h : j ≤ k) :
    dirichletLieWordSpan L j ≤ dirichletLieWordSpan L k := by
  apply Submodule.span_mono
  rintro a ⟨w, hw, hL, rfl⟩
  exact ⟨w, hw.trans h, hL, rfl⟩

theorem dirichletLiePowerSpan_mono {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) {j k : ℕ} (h : j ≤ k) :
    dirichletLiePowerSpan L j ≤ dirichletLiePowerSpan L k := by
  apply Submodule.span_mono
  rintro a ⟨x, hx, i, hi, rfl⟩
  exact ⟨x, hx, i, hi.trans h, rfl⟩

theorem dirichletLieWordSpan_mul_left {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) {k : ℕ} {x a : A} (hx : x ∈ L)
    (ha : a ∈ dirichletLieWordSpan L k) : x * a ∈ dirichletLieWordSpan L (k+1) := by
  classical
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨w, hw, hL, rfl⟩
    apply Submodule.subset_span
    exact ⟨x :: w, by simpa using Nat.add_le_add_right hw 1,
      by simpa using And.intro hx hL, by simp⟩
  | zero => simpa using (dirichletLieWordSpan L (k+1)).zero_mem
  | add a b _ _ ha hb => simpa only [mul_add] using (dirichletLieWordSpan L (k+1)).add_mem ha hb
  | smul r a _ ha => simpa only [mul_smul_comm] using (dirichletLieWordSpan L (k+1)).smul_mem r ha

theorem dirichletLieWordSpan_mul_right {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) {k : ℕ} {x a : A} (hx : x ∈ L)
    (ha : a ∈ dirichletLieWordSpan L k) : a * x ∈ dirichletLieWordSpan L (k+1) := by
  classical
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨w, hw, hL, rfl⟩
    apply Submodule.subset_span
    refine ⟨w ++ [x], by simpa using Nat.add_le_add_right hw 1, ?_, by simp⟩
    intro y hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hL y hy
    · exact hx
  | zero => simpa using (dirichletLieWordSpan L (k+1)).zero_mem
  | add a b _ _ ha hb => simpa only [add_mul] using (dirichletLieWordSpan L (k+1)).add_mem ha hb
  | smul r a _ ha => simpa only [smul_mul_assoc] using (dirichletLieWordSpan L (k+1)).smul_mem r ha

theorem dirichlet_commutator_power_mem_wordSpan {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) (hLie : ∀ x ∈ L, ∀ y ∈ L, x*y-y*x ∈ L)
    {x y : A} (hx : x ∈ L) (hy : y ∈ L) (k : ℕ) :
    y^k*x-x*y^k ∈ dirichletLieWordSpan L k := by
  classical
  induction k with
  | zero => simpa using (dirichletLieWordSpan L 0).zero_mem
  | succ k ih =>
    have hb : (y*x-x*y)*y^k ∈ dirichletLieWordSpan L (k+1) := by
      apply Submodule.subset_span
      refine ⟨(y*x-x*y) :: List.replicate k y, by simp, ?_, by simp⟩
      intro a ha
      simp only [List.mem_cons, List.mem_replicate] at ha
      rcases ha with rfl | ⟨_, rfl⟩
      · exact hLie y hy x hx
      · exact hy
    have h := (dirichletLieWordSpan L (k+1)).add_mem
      (dirichletLieWordSpan_mul_left L hy ih) hb
    convert! h using 1 <;> rw [pow_succ'] <;> noncomm_ring

theorem dirichlet_linear_polynomial_coeff_zero {A : Type*} [Ring A]
    (x y : A) (k : ℕ) : ((C y + monomial 1 x)^k).coeff 0 = y^k := by
  change Polynomial.constantCoeff ((C y + monomial 1 x)^k) = y^k
  rw [map_pow]
  simp

theorem dirichlet_linear_power_coeff_one_error {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) (hLie : ∀ x ∈ L, ∀ y ∈ L, x*y-y*x ∈ L)
    {x y : A} (hx : x ∈ L) (hy : y ∈ L) (k : ℕ) :
    ((C y + monomial 1 x)^(k+1)).coeff 1 - (k+1) • (x*y^k)
      ∈ dirichletLieWordSpan L k := by
  induction k with
  | zero => simpa using (dirichletLieWordSpan L 0).zero_mem
  | succ k ih =>
    have h := (dirichletLieWordSpan L (k+1)).add_mem
      (dirichlet_commutator_power_mem_wordSpan L hLie hx hy (k+1))
      (dirichletLieWordSpan_mul_right L hy ih)
    rw [pow_succ, Polynomial.mul_coeff_one, dirichlet_linear_polynomial_coeff_zero]
    simp only [coeff_add, coeff_C, coeff_monomial, if_pos rfl, if_neg (by decide : (1:ℕ) ≠ 0),
      if_neg (by decide : (0:ℕ) ≠ 1), zero_add, add_zero]
    convert! h using 1
    simp only [sub_mul, smul_mul_assoc, pow_succ, succ_nsmul, mul_assoc, add_mul]
    abel_nf <;> ac_rfl

theorem dirichlet_linear_power_coeff_mem_powerSpan {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) {x y : A} (hx : x ∈ L) (hy : y ∈ L)
    {j k : ℕ} (hjk : j ≤ k) (i : ℕ) :
    ((C y + monomial 1 x)^j).coeff i ∈ dirichletLiePowerSpan L k := by
  apply dirichlet_polynomial_coeff_mem_of_scalar_eval_mem
  intro t
  rw [map_pow]
  have he : dirichletScalarPolynomialEval t (C y + monomial 1 x) = y + t • x := by
    simp only [map_add, dirichletScalarPolynomialEval, Polynomial.eval₂RingHom'_apply,
      Polynomial.eval₂_C, Polynomial.eval₂_monomial, RingHom.id_apply, pow_one]
    rw [Algebra.smul_def, Algebra.commutes t x]
  rw [he]
  exact Submodule.subset_span ⟨y + t • x, L.add_mem hy (L.smul_mem t hx), j, hjk, rfl⟩

theorem dirichletLieWordSpan_le_powerSpan {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) (hLie : ∀ x ∈ L, ∀ y ∈ L, x*y-y*x ∈ L) (k : ℕ) :
    dirichletLieWordSpan L k ≤ dirichletLiePowerSpan L k := by
  classical
  induction k with
  | zero =>
    apply Submodule.span_le.mpr
    rintro a ⟨w, hw, _, rfl⟩
    have hw0 : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    exact Submodule.subset_span ⟨0, L.zero_mem, 0, le_rfl, by simp⟩
  | succ k ih =>
    have hmul {x a : A} (hx : x ∈ L) (ha : a ∈ dirichletLiePowerSpan L k) :
        x*a ∈ dirichletLiePowerSpan L (k+1) := by
      induction ha using Submodule.span_induction with
      | mem a ha =>
        rcases ha with ⟨y, hy, j, hj, rfl⟩
        have hc := dirichlet_linear_power_coeff_mem_powerSpan L hx hy
          (Nat.add_le_add_right hj 1) 1
        have he := dirichletLiePowerSpan_mono L (Nat.le_succ k)
          (ih (dirichletLieWordSpan_mono L hj
            (dirichlet_linear_power_coeff_one_error L hLie hx hy j)))
        have hscaled : (j+1) • (x*y^j) ∈ dirichletLiePowerSpan L (k+1) := by
          convert! (dirichletLiePowerSpan L (k+1)).sub_mem hc he using 1 <;> abel
        have hr : (j+1 : ℝ) ≠ 0 := by positivity
        have hreal : (j+1 : ℝ) • (x*y^j) ∈ dirichletLiePowerSpan L (k+1) := by
          have hh : ((j+1 : ℕ) : ℝ) • (x*y^j) ∈ dirichletLiePowerSpan L (k+1) := by
            simpa only [Nat.cast_smul_eq_nsmul] using hscaled
          simpa only [Nat.cast_add, Nat.cast_one] using hh
        have hh := (dirichletLiePowerSpan L (k+1)).smul_mem (j+1 : ℝ)⁻¹ hreal
        simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hh
      | zero => simpa using (dirichletLiePowerSpan L (k+1)).zero_mem
      | add a b _ _ ha hb => simpa only [mul_add] using (dirichletLiePowerSpan L (k+1)).add_mem ha hb
      | smul r a _ ha => simpa only [mul_smul_comm] using (dirichletLiePowerSpan L (k+1)).smul_mem r ha
    apply Submodule.span_le.mpr
    rintro a ⟨w, hw, hL, rfl⟩
    cases w with
    | nil => exact Submodule.subset_span ⟨0, L.zero_mem, 0, Nat.zero_le _, by simp⟩
    | cons x w =>
      simp only [List.prod_cons]
      apply hmul (hL x (by simp))
      apply ih
      apply Submodule.subset_span
      exact ⟨w, by simpa using hw, fun y hy => hL y (by simp [hy]), rfl⟩

theorem dirichlet_lie_word_mem_span_powers {A : Type*} [Ring A] [Algebra ℝ A]
    (L : Submodule ℝ A) (hLie : ∀ x ∈ L, ∀ y ∈ L, x*y-y*x ∈ L)
    (w : List A) (hw : ∀ x ∈ w, x ∈ L) :
    w.prod ∈ dirichletLiePowerSpan L w.length :=
  dirichletLieWordSpan_le_powerSpan L hLie w.length
    (Submodule.subset_span ⟨w, le_rfl, hw, rfl⟩)

end KEBall
