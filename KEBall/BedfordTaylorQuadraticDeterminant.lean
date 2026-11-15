import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# Determinant bounds under a positive scalar perturbation
-/

set_option autoImplicit false

open scoped BigOperators ComplexOrder

namespace KEBall.BedfordTaylor

private theorem prod_add_const_ge {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) {c : ℝ} (hc : 0 ≤ c) :
    (∏ i, a i) + c ^ n ≤ ∏ i, (a i + c) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have h := ih (by omega) (fun i => a i.succ) (fun i => ha i.succ)
      have hp : 0 ≤ ∏ i : Fin (n + 1), a i.succ :=
        Finset.prod_nonneg fun i _ => ha i.succ
      calc
        (∏ i, a i) + c ^ (n + 1 + 1) =
            a 0 * (∏ i : Fin (n + 1), a i.succ) + c * c ^ (n + 1) := by
          rw [Fin.prod_univ_succ a, pow_succ']
        _ ≤ (a 0 + c) * ((∏ i : Fin (n + 1), a i.succ) + c ^ (n + 1)) := by
          nlinarith only [mul_nonneg (ha 0) (pow_nonneg hc (n + 1)), mul_nonneg hc hp]
        _ ≤ (a 0 + c) * (∏ i : Fin (n + 1), (a i.succ + c)) :=
          mul_le_mul_of_nonneg_left h (add_nonneg (ha 0) hc)
        _ = ∏ i, (a i + c) := (Fin.prod_univ_succ (fun i => a i + c)).symm

/-- Adding a positive scalar multiple of the identity increases the
determinant by at least the determinant of the scalar matrix. -/
theorem det_re_add_scalar_one_ge {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    A.det.re + c ^ n ≤ (A + (c : ℂ) • 1).det.re := by
  let H := hA.isHermitian
  let U := H.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => (H.eigenvalues i : ℂ))
  let F := Unitary.conjStarAlgAut ℂ _ U
  have hF : F D = A := H.spectral_theorem.symm
  have hI : F ((c : ℂ) • 1) = (c : ℂ) • 1 := by simp [F]
  have hconj (M : Matrix (Fin n) (Fin n) ℂ) : (F M).det = M.det := by
    rw [show F M = (U : Matrix (Fin n) (Fin n) ℂ) * M * (star U : Matrix (Fin n) (Fin n) ℂ) from
      Unitary.conjStarAlgAut_apply U M, Matrix.det_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [← hF, ← hI, ← map_add, hconj, hconj]
  have he : D + (c : ℂ) • 1 = Matrix.diagonal (fun i => ((H.eigenvalues i + c : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.diagonal_apply_eq]
    · simp [D, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [he]
  simp only [D, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact prod_add_const_ge hn H.eigenvalues hA.eigenvalues_nonneg hc

end KEBall.BedfordTaylor
