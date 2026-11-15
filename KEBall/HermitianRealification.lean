import KEBall.Domain
import Mathlib.Analysis.Matrix.PosDef

/-! Actual real bilinear forms associated with a complex Hermitian matrix,
in the interleaved real coordinates of `KEBall.E`. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators ComplexOrder

namespace KEBall

noncomputable def coordinateProduct {n : ℕ} (i j : Fin (2 * n)) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)

@[simp] theorem coordinateProduct_apply {n : ℕ} (i j : Fin (2 * n)) (v w : E n) :
    coordinateProduct i j v w = v i * w j := rfl

noncomputable def hermitianRealification {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  (2 : ℝ) • ∑ i : Fin n, ∑ j : Fin n,
    ((A i j).re • (coordinateProduct (realIndex i) (realIndex j) +
       coordinateProduct (imagIndex i) (imagIndex j)) +
     (A i j).im • (coordinateProduct (realIndex i) (imagIndex j) -
       coordinateProduct (imagIndex i) (realIndex j)))

theorem hermitianRealification_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (v w : E n) :
    hermitianRealification A v w =
      2 * (∑ i : Fin n, ∑ j : Fin n,
        A i j * complexCoord v i * star (complexCoord w j)).re := by
  simp only [hermitianRealification, _root_.smul_apply,
    _root_.sum_apply, _root_.add_apply, _root_.sub_apply,
    coordinateProduct_apply, smul_eq_mul, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [complexCoord, Complex.mul_re, Complex.mul_im]
  ring

theorem complexCoord_eq_zero_iff {n : ℕ} {v : E n} :
    complexCoord v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext k
    let i : Fin n := ⟨k.val / 2, by omega⟩
    have hre : v (realIndex i) = 0 := by
      have hh := congrArg Complex.re (congrFun h i)
      simpa [complexCoord] using hh
    have him : v (imagIndex i) = 0 := by
      have hh := congrArg Complex.im (congrFun h i)
      simpa [complexCoord] using hh
    by_cases hk : k.val % 2 = 0
    · have he : realIndex i = k := by
        apply Fin.ext
        simp only [realIndex, i]
        omega
      simpa [he] using hre
    · have he : imagIndex i = k := by
        apply Fin.ext
        simp only [imagIndex, i]
        omega
      simpa [he] using him
  · rintro rfl
    funext i
    simp [complexCoord]

theorem hermitianRealification_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (v : E n) (hv : v ≠ 0) :
    0 < hermitianRealification A v v := by
  have hz : star (complexCoord v) ≠ 0 := by
    intro h
    apply hv
    apply complexCoord_eq_zero_iff.mp
    simpa only [star_eq_zero] using h
  have hpos := hA.re_dotProduct_pos hz
  rw [hermitianRealification_apply]
  apply mul_pos (by norm_num : (0 : ℝ) < 2)
  change 0 < Complex.re _ at hpos
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, star_star,
    mul_assoc, mul_left_comm] using hpos

theorem hermitianRealification_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (v w : E n) :
    hermitianRealification A v w = hermitianRealification A w v := by
  rw [hermitianRealification_apply, hermitianRealification_apply]
  simp only [Complex.re_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hh := hA.apply i j
  have hr := congrArg Complex.re hh
  have hi := congrArg Complex.im hh
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hr hi
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  rw [← hr, ← hi]
  ring

theorem realMetricForm_eq {n : ℕ} (u : E n → ℝ) (x v w : E n) :
    realMetricForm u x v w = hermitianRealification (complexHessian u x) v w := by
  exact (hermitianRealification_apply (complexHessian u x) v w).symm

theorem complexHessian_contDiffOn {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => complexHessian u x i j) U := by
  intro x hx
  have hc : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (hu.contDiffAt (hU.mem_nhds hx))
  exact (smoothAt_dz (smoothAt_dz hc (realDirection j) (-imagDirection j))
    (realDirection i) (imagDirection i)).contDiffWithinAt

theorem hermitianRealification_contDiffOn {n : ℕ}
    {A : E n → Matrix (Fin n) (Fin n) ℂ} {U : Set (E n)}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) :
    ContDiffOn ℝ ∞ (fun x => hermitianRealification (A x)) U := by
  unfold hermitianRealification
  apply ContDiffOn.const_smul (2 : ℝ)
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  have hr : ContDiffOn ℝ ∞ (fun x => (A x i j).re) U :=
    Complex.reCLM.contDiff.comp_contDiffOn (hA i j)
  have hi : ContDiffOn ℝ ∞ (fun x => (A x i j).im) U :=
    Complex.imCLM.contDiff.comp_contDiffOn (hA i j)
  exact (hr.smul contDiffOn_const).add (hi.smul contDiffOn_const)

end KEBall
