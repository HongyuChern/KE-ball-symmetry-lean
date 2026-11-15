import KEBall.Domain
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Algebra.BigOperators.Fin

/-!
# Concrete complex coordinates on the real Euclidean model

All coordinate derivatives below are computed from the actual real Frechet
derivative. The norm is the Euclidean l2 norm from `KEBall.E`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators RealInnerProductSpace

namespace KEBall
open KEBallProbe

@[simp] theorem realIndex_inj {n : ℕ} {i j : Fin n} :
    realIndex i = realIndex j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [realIndex] at hv
    omega
  · intro h
    subst j
    rfl

@[simp] theorem imagIndex_inj {n : ℕ} {i j : Fin n} :
    imagIndex i = imagIndex j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [imagIndex] at hv
    omega
  · intro h
    subst j
    rfl

@[simp] theorem realIndex_ne_imagIndex {n : ℕ} (i j : Fin n) :
    realIndex i ≠ imagIndex j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [realIndex, imagIndex] at hv
  omega

@[simp] theorem imagIndex_ne_realIndex {n : ℕ} (i j : Fin n) :
    imagIndex i ≠ realIndex j := (realIndex_ne_imagIndex j i).symm

noncomputable def complexCoordCLM {n : ℕ} (i : Fin n) : E n →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj (realIndex i)) +
    Complex.I • Complex.ofRealCLM.comp (EuclideanSpace.proj (imagIndex i))

@[simp] theorem complexCoordCLM_apply {n : ℕ} (i : Fin n) (x : E n) :
    complexCoordCLM i x = complexCoord x i := rfl

theorem smooth_complexCoord {n : ℕ} (i : Fin n) :
    ContDiff ℝ ∞ (fun x : E n => complexCoord x i) := (complexCoordCLM i).contDiff

@[simp] theorem complexCoord_neg {n : ℕ} (x : E n) (i : Fin n) :
    complexCoord (-x) i = -complexCoord x i := (complexCoordCLM i).map_neg x

@[simp] theorem complexCoord_realDirection {n : ℕ} (i j : Fin n) :
    complexCoord (realDirection i) j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [complexCoord, realDirection]
  · simp [complexCoord, realDirection, h, Ne.symm h]

@[simp] theorem complexCoord_imagDirection {n : ℕ} (i j : Fin n) :
    complexCoord (imagDirection i) j = if i = j then Complex.I else 0 := by
  by_cases h : i = j
  · subst j
    simp [complexCoord, imagDirection]
  · simp [complexCoord, imagDirection, h, Ne.symm h]

lemma rd_complexCoord {n : ℕ} (i : Fin n) (v x : E n) :
    rd v (fun y => complexCoord y i) x = complexCoord v i := by
  have h : HasFDerivAt (fun y : E n => complexCoord y i) (complexCoordCLM i) x :=
    (complexCoordCLM i).hasFDerivAt
  rw [rd, h.fderiv]
  rfl

@[simp] theorem partialZ_complexCoord {n : ℕ} (i j : Fin n) (x : E n) :
    partialZ i (fun y => complexCoord y j) x = if i = j then 1 else 0 := by
  unfold partialZ dz
  rw [rd_complexCoord, rd_complexCoord]
  by_cases h : i = j
  · norm_num [h]
  · simp [h]

@[simp] theorem partialBar_complexCoord {n : ℕ} (i j : Fin n) (x : E n) :
    partialBar i (fun y => complexCoord y j) x = 0 := by
  unfold partialBar dz
  rw [rd_complexCoord, rd_complexCoord]
  by_cases h : i = j
  · simp [h]
  · simp [h]

def interleavedEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

@[simp] theorem interleavedEquiv_zero {n : ℕ} (i : Fin n) :
    interleavedEquiv n (i, 0) = realIndex i := by
  apply Fin.ext
  simp [interleavedEquiv, finProdFinEquiv, realIndex]

@[simp] theorem interleavedEquiv_one {n : ℕ} (i : Fin n) :
    interleavedEquiv n (i, 1) = imagIndex i := by
  apply Fin.ext
  simp [interleavedEquiv, finProdFinEquiv, imagIndex, Nat.add_comm]

theorem norm_sq_interleaved {n : ℕ} (x : E n) :
    ‖x‖ ^ 2 = ∑ i : Fin n, ((x (realIndex i)) ^ 2 + (x (imagIndex i)) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← (interleavedEquiv n).sum_comp (fun k => (x k) ^ 2)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

theorem sum_star_complexCoord_mul {n : ℕ} (x : E n) :
    (∑ i : Fin n, star (complexCoord x i) * complexCoord x i) = (‖x‖ ^ 2 : ℝ) := by
  rw [norm_sq_interleaved]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [complexCoord, star_add, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp

lemma rd_ofReal_comp_norm_sq {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {ρ : ℝ → ℝ} {c : ℝ} {x : X} (hρ : HasDerivAt ρ c (‖x‖ ^ 2)) (v : X) :
    rd v (fun y => (ρ (‖y‖ ^ 2) : ℂ)) x = (2 * c * inner ℝ x v : ℝ) := by
  have hreal := hρ.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hreal
  change HasFDerivAt (fun y => (ρ (‖y‖ ^ 2) : ℂ))
    (Complex.ofRealCLM.comp (c • (2 • innerSL ℝ x))) x at h
  rw [rd, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

lemma partialZ_ofReal_comp_norm_sq {n : ℕ} {ρ : ℝ → ℝ} {c : ℝ} {x : E n}
    (hρ : HasDerivAt ρ c (‖x‖ ^ 2)) (i : Fin n) :
    partialZ i (fun y => (ρ (‖y‖ ^ 2) : ℂ)) x =
      (c : ℂ) * star (complexCoord x i) := by
  unfold partialZ dz
  rw [rd_ofReal_comp_norm_sq hρ, rd_ofReal_comp_norm_sq hρ]
  simp only [realDirection, imagDirection, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, complexCoord, star_add, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma partialBar_ofReal_comp_norm_sq {n : ℕ} {ρ : ℝ → ℝ} {c : ℝ} {x : E n}
    (hρ : HasDerivAt ρ c (‖x‖ ^ 2)) (i : Fin n) :
    partialBar i (fun y => (ρ (‖y‖ ^ 2) : ℂ)) x =
      (c : ℂ) * complexCoord x i := by
  unfold partialBar dz
  rw [rd_ofReal_comp_norm_sq hρ, rd_ofReal_comp_norm_sq hρ]
  simp only [realDirection, imagDirection, inner_neg_right, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, complexCoord]
  push_cast
  ring

#print axioms norm_sq_interleaved
#print axioms partialZ_ofReal_comp_norm_sq
#print axioms partialBar_ofReal_comp_norm_sq

end KEBall
