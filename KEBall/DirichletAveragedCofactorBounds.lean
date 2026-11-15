import KEBall.DirichletAveragedCofactor
import KEBall.DirichletDifferenceQuotientHolder

/-!
# Bounds preserved by averaging the cofactor

Segment averages preserve norm and coercivity bounds.  On a fixed matrix
ball the polynomial cofactor map is Lipschitz, so two Holder endpoint
fields give a Holder averaged field with a constant independent of the
translation parameter used to form those endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem norm_dirichlet_affine_segment_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A B : F} {R t : ℝ}
    (hA : ‖A‖ ≤ R) (hB : ‖B‖ ≤ R) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖A + t • (B - A)‖ ≤ R := by
  have he : A + t • (B - A) = (1 - t) • A + t • B := by module
  rw [he]
  calc
    _ ≤ ‖(1 - t) • A‖ + ‖t • B‖ := norm_add_le _ _
    _ = (1 - t) * ‖A‖ + t * ‖B‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2),
        Real.norm_of_nonneg ht.1]
    _ ≤ (1 - t) * R + t * R := add_le_add
      (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hB ht.1)
    _ = R := by ring

theorem norm_dirichlet_affine_segment_sub_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A B C D : F} {M t : ℝ}
    (hA : ‖A - C‖ ≤ M) (hB : ‖B - D‖ ≤ M) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(A + t • (B - A)) - (C + t • (D - C))‖ ≤ M := by
  have he : (A + t • (B - A)) - (C + t • (D - C)) =
      (A - C) + t • ((B - D) - (A - C)) := by module
  rw [he]
  exact norm_dirichlet_affine_segment_le hA hB ht

theorem dirichletMeanCofactor_same {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    dirichletMeanCofactor A A = dirichletCofactorOfMatrix A := by
  simp only [dirichletMeanCofactor, sub_self, smul_zero, add_zero,
    intervalIntegral.integral_const, sub_zero, one_smul]

theorem norm_dirichletMeanCofactor_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖dirichletCofactorOfMatrix (A + t • (B - A))‖ ≤ M) :
    ‖dirichletMeanCofactor A B‖ ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (fun t ht =>
    hM t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)))
  simpa only [dirichletMeanCofactor, sub_zero, abs_one, mul_one] using h

theorem norm_dirichletMeanCofactor_sub_le {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) ℂ) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖dirichletCofactorOfMatrix (A + t • (B - A)) -
        dirichletCofactorOfMatrix (C + t • (D - C))‖ ≤ M) :
    ‖dirichletMeanCofactor A B - dirichletMeanCofactor C D‖ ≤ M := by
  rw [dirichletMeanCofactor, dirichletMeanCofactor, ← intervalIntegral.integral_sub
    ((continuous_dirichlet_cofactor_segment A B).intervalIntegrable 0 1)
    ((continuous_dirichlet_cofactor_segment C D).intervalIntegrable 0 1)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (fun t ht =>
    hM t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)))
  simpa only [sub_zero, abs_one, mul_one] using h

theorem norm_dirichletMeanCofactor_sub_le_of_lipschitz {n : ℕ} {R M : ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K (@dirichletCofactorOfMatrix n) (closedBall 0 R))
    {A B C D : Matrix (Fin n) (Fin n) ℂ}
    (hA : ‖A‖ ≤ R) (hB : ‖B‖ ≤ R) (hC : ‖C‖ ≤ R) (hD : ‖D‖ ≤ R)
    (hAC : ‖A - C‖ ≤ M) (hBD : ‖B - D‖ ≤ M) :
    ‖dirichletMeanCofactor A B - dirichletMeanCofactor C D‖ ≤ (K : ℝ) * M := by
  apply norm_dirichletMeanCofactor_sub_le
  intro t ht
  have h := hLip.dist_le_mul _
    (mem_closedBall_zero_iff.mpr (norm_dirichlet_affine_segment_le hA hB ht)) _
    (mem_closedBall_zero_iff.mpr (norm_dirichlet_affine_segment_le hC hD ht))
  rw [dist_eq_norm, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (norm_dirichlet_affine_segment_sub_le hAC hBD ht) K.coe_nonneg)

theorem holderOnWith_dirichletMeanCofactor {n : ℕ} {R : ℝ} {L K α : ℝ≥0}
    (hLip : LipschitzOnWith L (@dirichletCofactorOfMatrix n) (closedBall 0 R))
    {A B : E n → Matrix (Fin n) (Fin n) ℂ} {S : Set (E n)}
    (hA : HolderOnWith K α A S) (hB : HolderOnWith K α B S)
    (hANorm : ∀ x ∈ S, ‖A x‖ ≤ R) (hBNorm : ∀ x ∈ S, ‖B x‖ ≤ R) :
    HolderOnWith (L * K) α (fun x => dirichletMeanCofactor (A x) (B x)) S := by
  apply dirichlet_holderOnWith_of_norm_sub_le
  intro x hx y hy
  have hAC : ‖A x - A y‖ ≤ (K : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hA.dist_le hx hy
  have hBD : ‖B x - B y‖ ≤ (K : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hB.dist_le hx hy
  simpa only [NNReal.coe_mul, mul_assoc] using norm_dirichletMeanCofactor_sub_le_of_lipschitz hLip
    (hANorm x hx) (hBNorm x hx) (hANorm y hy) (hBNorm y hy) hAC hBD

theorem dirichletMeanCofactor_coercive {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) {l : ℝ}
    (hE : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOfMatrix (A + t • (B - A)) v) v)
    (v : E n) : l * ‖v‖ ^ 2 ≤ inner ℝ (dirichletMeanCofactor A B v) v := by
  rw [inner_dirichletMeanCofactor]
  have hCont : Continuous (fun t : ℝ =>
      inner ℝ (dirichletCofactorOfMatrix (A + t • (B - A)) v) v) :=
    ((continuous_dirichlet_cofactor_segment A B).clm_apply continuous_const).inner continuous_const
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one (intervalIntegrable_const)
    (hCont.intervalIntegrable 0 1) (fun t ht => hE t ht v)
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using h

end KEBall
