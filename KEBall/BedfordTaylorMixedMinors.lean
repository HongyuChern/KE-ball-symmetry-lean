import Mathlib.Analysis.Matrix.Order

/-!
# Mixed minors of Hermitian Hessians

The mixed coefficient of order k is a matrix on ordered k-tuples
of coordinate indices. Positivity is inherited from an explicit
Gram matrix whose entries are determinants.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped ComplexOrder MatrixOrder

namespace KEBall.BedfordTaylor

abbrev CoordinateTuple (n k : ℕ) := Fin k → Fin n

/-- The mixed-minor recursion, with one row and one column deleted at each
step. Repeating one matrix yields k! times its minor. -/
noncomputable def mixedMinorMatrix {n : ℕ} :
    (k : ℕ) → (Fin k → Matrix (Fin n) (Fin n) ℂ) →
      Matrix (CoordinateTuple n k) (CoordinateTuple n k) ℂ
  | 0, _ => Matrix.of fun _ _ => 1
  | k + 1, A => Matrix.of fun I J =>
      ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
        (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A 0 (I i) (J j) *
          mixedMinorMatrix k (Fin.tail A) (i.removeNth I) (j.removeNth J)

@[simp]
theorem mixedMinorMatrix_zero {n : ℕ}
    (A : Fin 0 → Matrix (Fin n) (Fin n) ℂ) (I J : CoordinateTuple n 0) :
    mixedMinorMatrix 0 A I J = 1 := rfl

theorem mixedMinorMatrix_succ {n k : ℕ}
    (A : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (I J : CoordinateTuple n (k + 1)) :
    mixedMinorMatrix (k + 1) A I J =
      ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
        (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A 0 (I i) (J j) *
          mixedMinorMatrix k (Fin.tail A) (i.removeNth I) (j.removeNth J) := rfl

/-- The repeated-factor recursion equals the determinant with the
factorial normalization. -/
theorem mixedMinorMatrix_const {n : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (I J : CoordinateTuple n k) :
    mixedMinorMatrix k (fun _ => A) I J = (k.factorial : ℂ) * (A.submatrix I J).det := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mixedMinorMatrix_succ, Nat.factorial_succ, Nat.cast_mul]
    have htail : Fin.tail (fun _ : Fin (k + 1) => A) = fun _ : Fin k => A := rfl
    simp only [htail, ih]
    have heq (i : Fin (k + 1)) :
        ∑ j : Fin (k + 1), (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A (I i) (J j) *
          ((k.factorial : ℂ) * (A.submatrix (i.removeNth I) (j.removeNth J)).det) =
          (k.factorial : ℂ) * (A.submatrix I J).det := by
      conv_rhs => rw [Matrix.det_succ_row _ i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hI : i.removeNth I = I ∘ i.succAbove := funext fun _ => rfl
      have hJ : j.removeNth J = J ∘ j.succAbove := funext fun _ => rfl
      simp only [Matrix.submatrix_apply, Matrix.submatrix_submatrix, hI, hJ]
      ring
    simp_rw [heq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

private noncomputable def determinantGramMatrix {n k : ℕ}
    (S : Fin k → Matrix (Fin n) (Fin n) ℂ) : Matrix (CoordinateTuple n k) (CoordinateTuple n k) ℂ :=
  Matrix.of fun R I => (Matrix.of fun a b => S a (R a) (I b)).det

private theorem determinantGramMatrix_cons {n k : ℕ}
    (S : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin n) (R : CoordinateTuple n k) (I : CoordinateTuple n (k + 1)) :
    determinantGramMatrix S (Fin.cons x R) I =
      ∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) * S 0 x (I i) *
        determinantGramMatrix (Fin.tail S) R (i.removeNth I) := by
  rw [determinantGramMatrix, Matrix.of_apply, Matrix.det_succ_row_zero]
  simp only [Matrix.of_apply, Fin.cons_zero, determinantGramMatrix]
  rfl

private theorem sum_coordinateTuple_cons {n k : ℕ} (f : CoordinateTuple n (k + 1) → ℂ) :
    (∑ R, f R) = ∑ x : Fin n, ∑ R : CoordinateTuple n k, f (Fin.cons x R) := by
  let e := Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)
  exact (e.sum_comp f).symm.trans (by rw [Fintype.sum_prod_type]; rfl)

private theorem sum_sum_sum_sum_exchange {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ ab : α × β, ∑ cd : γ × δ, f ab.1 ab.2 cd.1 cd.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ cd : γ × δ, ∑ ab : α × β, f ab.1 ab.2 cd.1 cd.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

private theorem mixedMinorMatrix_gram {n : ℕ} (k : ℕ)
    (S : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    mixedMinorMatrix k (fun r => (S r)ᴴ * S r) =
      (determinantGramMatrix S)ᴴ * determinantGramMatrix S := by
  induction k with
  | zero =>
    ext I J : 1
    simp [determinantGramMatrix, Matrix.mul_apply]
  | succ k ih =>
    ext I J : 1
    rw [mixedMinorMatrix_succ, Matrix.mul_apply, sum_coordinateTuple_cons]
    simp only [Matrix.conjTranspose_apply, determinantGramMatrix_cons]
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [sum_sum_sum_sum_exchange]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have htail :
        Fin.tail (fun r => (S r)ᴴ * S r) = fun r => (Fin.tail S r)ᴴ * Fin.tail S r := rfl
    rw [htail, ih (Fin.tail S), Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, star_mul, star_pow, star_neg, star_one, pow_add]
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun R _ => ?_
    ring

theorem mixedMinorMatrix_posSemidef {n k : ℕ} {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i, (A i).PosSemidef) : (mixedMinorMatrix k A).PosSemidef := by
  classical
  have h (i : Fin k) : ∃ B : Matrix (Fin n) (Fin n) ℂ, A i = Bᴴ * B := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hA i).nonneg)
  choose S hS using h
  rw [show A = (fun i => (S i)ᴴ * S i) from funext hS, mixedMinorMatrix_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Permuting positive semidefinite factors preserves every mixed minor. -/
theorem mixedMinorMatrix_comp_perm {n k : ℕ} {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i, (A i).PosSemidef) (σ : Equiv.Perm (Fin k)) :
    mixedMinorMatrix k (A ∘ σ) = mixedMinorMatrix k A := by
  classical
  have h (i : Fin k) : ∃ B : Matrix (Fin n) (Fin n) ℂ, A i = Bᴴ * B := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hA i).nonneg)
  choose S hS using h
  rw [show A = (fun i => (S i)ᴴ * S i) from funext hS, mixedMinorMatrix_gram]
  change mixedMinorMatrix k (fun i => (S (σ i))ᴴ * S (σ i)) = _
  refine (mixedMinorMatrix_gram k (S ∘ σ)).trans ?_
  have hperm (R I : CoordinateTuple n k) :
      determinantGramMatrix (S ∘ σ) (R ∘ σ) I =
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * determinantGramMatrix S R I := by
    let M := Matrix.of fun a b : Fin k => S a (R a) (I b)
    change (M.submatrix σ id).det = _ * M.det
    exact Matrix.det_permute σ M
  ext I J : 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  let e : CoordinateTuple n k ≃ CoordinateTuple n k :=
    (Equiv.piCongrLeft' (fun _ => Fin n) σ.symm)
  let F : CoordinateTuple n k → ℂ := fun R =>
    star (determinantGramMatrix (S ∘ σ) R I) * determinantGramMatrix (S ∘ σ) R J
  change (∑ R, F R) = _
  rw [← e.sum_comp F]
  refine Finset.sum_congr rfl fun R _ => ?_
  have he : e R = R ∘ σ := by
    funext i
    simp [e]
  change star (determinantGramMatrix (S ∘ σ) (e R) I) *
    determinantGramMatrix (S ∘ σ) (e R) J = _
  rw [he, hperm, hperm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

#print axioms mixedMinorMatrix_const
#print axioms mixedMinorMatrix_posSemidef

end KEBall.BedfordTaylor
