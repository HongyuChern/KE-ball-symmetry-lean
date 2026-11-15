import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
Stage15 SOURCE_REPAIR_CANDIDATE_UNCOMPILED.
Pair commutation now uses four explicit degree-one swaps.
Genuine products in mathlib's ExteriorAlgebra. The factorial and determinant
are proved from multiplication, square-zero generators and alternation;
neither is a definition of a top exterior power.
-/
set_option autoImplicit false
open scoped BigOperators

namespace KEBall.ExteriorPair

section Ring
variable {R : Type*} [Ring R]

/-- Binomial expansion with one commuting square-zero term. -/
theorem add_pow_of_sq_zero {a b : R} (hab : Commute a b) (ha : a * a = 0)
    (k : ℕ) : (a + b) ^ (k + 1) = b ^ (k + 1) + (k + 1) • (a * b ^ k) := by
  induction k with
  | zero => simp [add_comm]
  | succ k ih =>
    have hba : b ^ (k + 1) * a = a * b ^ (k + 1) :=
      (hab.symm.pow_left (k + 1)).eq
    have hzero : (a * b ^ k) * a = 0 := by
      rw [mul_assoc, (hab.symm.pow_left k).eq, ← mul_assoc, ha, zero_mul]
    calc
      (a + b) ^ (k + 1 + 1) =
          (b ^ (k + 1) + (k + 1) • (a * b ^ k)) * (a + b) := by
        rw [pow_succ, ih]
      _ = b ^ (k + 1) * a + b ^ (k + 1 + 1) +
          (k + 1) • ((a * b ^ k) * a) +
          (k + 1) • (a * b ^ (k + 1)) := by
        simp only [add_mul, mul_add, smul_mul_assoc, pow_succ, mul_assoc]
        abel
      _ = b ^ (k + 1 + 1) + (k + 1 + 1) • (a * b ^ (k + 1)) := by
        rw [hba, hzero]
        simp only [nsmul_zero, add_zero, add_nsmul, one_nsmul]
        abel

end Ring

section Exterior
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

noncomputable def pairProd : (n : ℕ) → (Fin n → M) → (Fin n → M) → ExteriorAlgebra ℂ M
  | 0, _, _ => 1
  | n + 1, a, b =>
      (ExteriorAlgebra.ι ℂ (a 0) * ExteriorAlgebra.ι ℂ (b 0)) *
        pairProd n (fun i => a i.succ) (fun i => b i.succ)

theorem pairProd_eq_list (n : ℕ) (a b : Fin n → M) :
    pairProd n a b =
      (List.ofFn (fun i => ExteriorAlgebra.ι ℂ (a i) * ExteriorAlgebra.ι ℂ (b i))).prod := by
  induction n with
  | zero => simp [pairProd]
  | succ n ih => rw [pairProd, List.ofFn_succ, List.prod_cons, ih]

theorem pair_sq_zero (a b : M) :
    (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b) *
      (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b) = 0 := by
  have hswap : ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ a =
      -(ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap b a)
  calc
    _ = ExteriorAlgebra.ι ℂ a *
        (ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ a) * ExteriorAlgebra.ι ℂ b := by
      simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ a) *
        (ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ b) := by
      rw [hswap]
      noncomm_ring
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

theorem pair_commute (a b c d : M) :
    Commute (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b)
      (ExteriorAlgebra.ι ℂ c * ExteriorAlgebra.ι ℂ d) := by
  change (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b) *
      (ExteriorAlgebra.ι ℂ c * ExteriorAlgebra.ι ℂ d) =
    (ExteriorAlgebra.ι ℂ c * ExteriorAlgebra.ι ℂ d) *
      (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b)
  have hswap (x y : M) : ExteriorAlgebra.ι ℂ x * ExteriorAlgebra.ι ℂ y =
      -(ExteriorAlgebra.ι ℂ y * ExteriorAlgebra.ι ℂ x) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)
  calc
    _ = ExteriorAlgebra.ι ℂ a *
        (ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ c) *
          ExteriorAlgebra.ι ℂ d := by noncomm_ring
    _ = -(ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ c) *
        (ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ d) := by
      rw [hswap b c]
      noncomm_ring
    _ = (ExteriorAlgebra.ι ℂ c * ExteriorAlgebra.ι ℂ a) *
        (ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ d) := by
      rw [hswap a c]
      noncomm_ring
    _ = -(ExteriorAlgebra.ι ℂ c * ExteriorAlgebra.ι ℂ a) *
        (ExteriorAlgebra.ι ℂ d * ExteriorAlgebra.ι ℂ b) := by
      rw [hswap b d]
      noncomm_ring
    _ = -ExteriorAlgebra.ι ℂ c *
        (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ d) *
          ExteriorAlgebra.ι ℂ b := by noncomm_ring
    _ = (ExteriorAlgebra.ι ℂ c * ExteriorAlgebra.ι ℂ d) *
        (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b) := by
      rw [hswap a d]
      noncomm_ring

/-- The n! coefficient and the next nilpotent power, in every dimension. -/
theorem sum_pairs_pow (n : ℕ) (a b : Fin n → M) :
    (∑ i, ExteriorAlgebra.ι ℂ (a i) * ExteriorAlgebra.ι ℂ (b i)) ^ n =
        n.factorial • pairProd n a b ∧
    (∑ i, ExteriorAlgebra.ι ℂ (a i) * ExteriorAlgebra.ι ℂ (b i)) ^ (n + 1) = 0 := by
  induction n with
  | zero => simp [pairProd]
  | succ n ih =>
    let a' : Fin n → M := fun i => a i.succ
    let b' : Fin n → M := fun i => b i.succ
    let q := ExteriorAlgebra.ι ℂ (a 0) * ExteriorAlgebra.ι ℂ (b 0)
    let s := ∑ i, ExteriorAlgebra.ι ℂ (a' i) * ExteriorAlgebra.ι ℂ (b' i)
    obtain ⟨htop, hnil⟩ := ih a' b'
    have hcomm : Commute q s := by
      change q * (∑ i, _) = (∑ i, _) * q
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => pair_commute (a 0) (b 0) (a' i) (b' i))
    have hq : q * q = 0 := pair_sq_zero (a 0) (b 0)
    have hnil' : s ^ (n + 1) = 0 := hnil
    have htop' : s ^ n = n.factorial • pairProd n a' b' := htop
    constructor
    · rw [Fin.sum_univ_succ]
      change (q + s) ^ (n + 1) = _
      rw [add_pow_of_sq_zero hcomm hq, hnil', zero_add, htop',
        mul_smul_comm, smul_smul, ← Nat.factorial_succ]
      rfl
    · rw [Fin.sum_univ_succ]
      change (q + s) ^ (n + 1 + 1) = 0
      rw [add_pow_of_sq_zero hcomm hq, pow_succ s (n + 1), hnil']
      simp

theorem iota_mul_multi (c : M) (n : ℕ) (a : Fin n → M) :
    ExteriorAlgebra.ι ℂ c * ExteriorAlgebra.ιMulti ℂ n a =
      ((-1 : ℤˣ) ^ n) • (ExteriorAlgebra.ιMulti ℂ n a * ExteriorAlgebra.ι ℂ c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hswap : ExteriorAlgebra.ι ℂ c * ExteriorAlgebra.ι ℂ (a 0) =
        -(ExteriorAlgebra.ι ℂ (a 0) * ExteriorAlgebra.ι ℂ c) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap c (a 0))
    rw [ExteriorAlgebra.ιMulti_succ_apply,
      ← mul_assoc, hswap, neg_mul, mul_assoc, ih, mul_smul_comm]
    simp [pow_succ, mul_smul, Units.smul_def, mul_assoc]

/-- Separating the two families records every odd-degree crossing. -/
theorem pairProd_eq_multi (n : ℕ) (a b : Fin n → M) :
    pairProd n a b = ((-1 : ℤˣ) ^ (n.choose 2)) •
      (ExteriorAlgebra.ιMulti ℂ n a * ExteriorAlgebra.ιMulti ℂ n b) := by
  induction n with
  | zero => simp [pairProd]
  | succ n ih =>
    let a' : Fin n → M := fun i => a i.succ
    let b' : Fin n → M := fun i => b i.succ
    rw [pairProd, ih]
    have hmove := iota_mul_multi (b 0) n a'
    calc
      _ = ((-1 : ℤˣ) ^ (n.choose 2)) •
          (ExteriorAlgebra.ι ℂ (a 0) *
            (ExteriorAlgebra.ι ℂ (b 0) * ExteriorAlgebra.ιMulti ℂ n a') *
              ExteriorAlgebra.ιMulti ℂ n b') := by
        simp only [a', b', mul_smul_comm, mul_assoc]
      _ = (((-1 : ℤˣ) ^ (n.choose 2)) * ((-1 : ℤˣ) ^ n)) •
          ((ExteriorAlgebra.ι ℂ (a 0) * ExteriorAlgebra.ιMulti ℂ n a') *
            (ExteriorAlgebra.ι ℂ (b 0) * ExteriorAlgebra.ιMulti ℂ n b')) := by
        rw [hmove]
        simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      _ = _ := by
        rw [← pow_add]
        simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm,
          ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, a', b', Function.comp_def]

/-- Top alternating maps with arbitrary module codomain obey determinant change. -/
theorem alternating_matrix {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
    (f : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] N) (A : Matrix (Fin n) (Fin n) ℂ) :
    f A = A.det • f (Pi.basisFun ℂ (Fin n)) := by
  classical
  let e := Pi.basisFun ℂ (Fin n)
  let g := (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).smulRight (f e)
  have hfg : f = g := by
    apply e.ext_alternating
    intro v hv
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v
      ((Fintype.bijective_iff_injective_and_card v).mpr ⟨hv, rfl⟩)
    change f (e ∘ σ) = g (e ∘ σ)
    rw [f.map_perm, g.map_perm]
    congr 1
    change f e = (Matrix.detRowAlternating e) • f e
    have he : (fun i => e i) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      simp [e, Pi.basisFun_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
    have hdet : Matrix.detRowAlternating e = (1 : ℂ) := by
      change Matrix.det (fun i => e i) = 1
      rw [he, Matrix.det_one]
    rw [hdet, one_smul]
  have h := congrArg (fun F : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] N => F A) hfg
  exact h

theorem multi_linearCombination {n : ℕ} (b : Fin n → M)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ExteriorAlgebra.ιMulti ℂ n (fun i => ∑ j, A i j • b j) =
      A.det • ExteriorAlgebra.ιMulti ℂ n b := by
  classical
  let L : (Fin n → ℂ) →ₗ[ℂ] M := ∑ j, (LinearMap.proj j).smulRight (b j)
  have hL (v : Fin n → ℂ) : L v = ∑ j, v j • b j := by simp [L]
  have he (i : Fin n) : L (Pi.basisFun ℂ (Fin n) i) = b i := by
    simp [hL, Pi.basisFun_apply]
  have h := alternating_matrix ((ExteriorAlgebra.ιMulti ℂ n).compLinearMap L) A
  simp only [AlternatingMap.compLinearMap_apply] at h
  rw [show (fun i => L (Pi.basisFun ℂ (Fin n) i)) = b from funext he] at h
  change ExteriorAlgebra.ιMulti ℂ n (fun i => L (A i)) =
    A.det • ExteriorAlgebra.ιMulti ℂ n b at h
  simpa only [hL] using h

theorem pairProd_linearCombination {n : ℕ} (a b : Fin n → M)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    pairProd n a (fun i => ∑ j, A i j • b j) = A.det • pairProd n a b := by
  rw [pairProd_eq_multi, pairProd_eq_multi, multi_linearCombination]
  rw [mul_smul_comm, smul_comm]

/-- The determinant formula for a genuine n-fold exterior product. -/
theorem sum_pairs_matrix_pow {n : ℕ} (a b : Fin n → M)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ExteriorAlgebra.ι ℂ (a i) *
      ExteriorAlgebra.ι ℂ (∑ j, A i j • b j)) ^ n =
        n.factorial • (A.det • pairProd n a b) := by
  rw [(sum_pairs_pow n a (fun i => ∑ j, A i j • b j)).1,
    pairProd_linearCombination]

theorem pairProd_of_pair_eq {n : ℕ} (a b c d : Fin n → M) (q : ℂ)
    (h : ∀ i, ExteriorAlgebra.ι ℂ (a i) * ExteriorAlgebra.ι ℂ (b i) =
      q • (ExteriorAlgebra.ι ℂ (c i) * ExteriorAlgebra.ι ℂ (d i))) :
    pairProd n a b = q ^ n • pairProd n c d := by
  induction n with
  | zero => simp [pairProd]
  | succ n ih =>
    rw [pairProd, pairProd, h 0, ih _ _ _ _ (fun i => h i.succ)]
    rw [smul_mul_smul, pow_succ']

#print axioms sum_pairs_matrix_pow

end Exterior
end KEBall.ExteriorPair
