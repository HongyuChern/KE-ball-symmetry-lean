import KEBall.DirichletNormalRecovery
import KEBall.ScalarLaplacian
import KEBall.DirichletTraceEllipticity

/-! The J-invariant projection of the actual real Hessian.  Its complex
Hessian is unchanged; its directional quadratics are controlled by the
complex trace.  No full real Hessian bound is inferred. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

open Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff

namespace KEBall

noncomputable def complexProjectedHessian {n : ℕ} (u : E n → ℝ) (x : E n) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  hermitianRealification (complexHessian u x)

theorem complexProjectedHessian_eq_average {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    complexProjectedHessian u x v w =
      (realHessian u x v w + realHessian u x (J v) (J w)) / 2 := by
  rw [complexProjectedHessian, ← realMetricForm_eq]
  exact realMetricForm_eq_average_hessian hu v w

theorem complexHessianOfRealBilinear_projected {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) :
    complexHessianOfRealBilinear (complexProjectedHessian u x) = complexHessian u x := by
  ext i j
  rw [complexHessian_real_entry hu]
  simp only [complexHessianOfRealBilinear, complexProjectedHessian_eq_average hu,
    J_realDirection, J_imagDirection, map_neg, _root_.neg_apply, neg_neg]
  push_cast
  ring

theorem complexProjectedHessian_contDiff {n : ℕ} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (complexProjectedHessian u) := by
  rw [← contDiffOn_univ]
  exact hermitianRealification_contDiffOn
    (complexHessian_contDiffOn isOpen_univ hu.contDiffOn)

private theorem projected_dotProduct_unitary_conj {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    star z ⬝ᵥ ((Unitary.conjStarAlgAut ℂ _ U A) *ᵥ z) =
      star (star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z) ⬝ᵥ
        (A *ᵥ (star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z)) := by
  rw [Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem complex_quadratic_bounds_of_eigenvalues {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {l L : ℝ}
    (hE : ∀ i, l ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ L) (z : Fin n → ℂ) :
    l * (star z ⬝ᵥ z).re ≤ (star z ⬝ᵥ (A *ᵥ z)).re ∧
      (star z ⬝ᵥ (A *ᵥ z)).re ≤ L * (star z ⬝ᵥ z).re := by
  let U := hA.eigenvectorUnitary
  let v := star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z
  have hzv : star z ⬝ᵥ z = star v ⬝ᵥ v := by
    simpa only [v, map_one, Matrix.one_mulVec] using
      projected_dotProduct_unitary_conj U (1 : Matrix (Fin n) (Fin n) ℂ) z
  have hTerm (d : ℝ) (w : ℂ) :
      (star w * ((d : ℂ) * w)).re = d * Complex.normSq w := by
    rw [show star w * ((d : ℂ) * w) = (d : ℂ) * (w * star w) by ring]
    rw [Complex.star_def, Complex.mul_conj]
    simp
  have hWeighted : (star z ⬝ᵥ (A *ᵥ z)).re =
      ∑ i, hA.eigenvalues i * Complex.normSq (v i) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [projected_dotProduct_unitary_conj]
    change (star v ⬝ᵥ (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *ᵥ v)).re = _
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum, hTerm]
  have hMass : (star z ⬝ᵥ z).re = ∑ i, Complex.normSq (v i) := by
    rw [hzv]
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.ofReal_one, one_mul] using hTerm 1 (v i)
  rw [hWeighted, hMass, Finset.mul_sum, Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro i _
  · exact mul_le_mul_of_nonneg_right (hE i).1 (Complex.normSq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (hE i).2 (Complex.normSq_nonneg _)

theorem hermitianRealification_quadratic_bounds_of_eigenvalues {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {l L : ℝ}
    (hE : ∀ i, l ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ L) (v : E n) :
    (2 * l) * ‖v‖ ^ 2 ≤ hermitianRealification A v v ∧
      hermitianRealification A v v ≤ (2 * L) * ‖v‖ ^ 2 := by
  have h := complex_quadratic_bounds_of_eigenvalues hA hE (star (complexCoord v))
  have hMass : (star (star (complexCoord v)) ⬝ᵥ star (complexCoord v)).re = ‖v‖ ^ 2 := by
    rw [star_star, dotProduct_comm]
    have he := sum_star_complexCoord_mul v
    change star (complexCoord v) ⬝ᵥ complexCoord v = _ at he
    rw [he, Complex.ofReal_re]
  have hForm : hermitianRealification A v v =
      2 * (star (star (complexCoord v)) ⬝ᵥ (A *ᵥ star (complexCoord v))).re := by
    rw [hermitianRealification_apply]
    simp only [star_star, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hMass] at h
  rw [hForm]
  constructor <;> nlinarith only [h.1, h.2]

theorem complexProjectedHessian_self_bounds_of_trace {n : ℕ}
    {u : E n → ℝ} {x : E n} (hA : (complexHessian u x).PosDef)
    {D : ℝ} (hTrace : (complexHessian u x).trace.re ≤ D) (v : E n) :
    0 ≤ complexProjectedHessian u x v v ∧
      complexProjectedHessian u x v v ≤ (2 * D) * ‖v‖ ^ 2 := by
  have htr : (complexHessian u x).trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    rfl
  have hE (i : Fin n) : 0 ≤ hA.isHermitian.eigenvalues i ∧ hA.isHermitian.eigenvalues i ≤ D := by
    refine ⟨(hA.eigenvalues_pos i).le, le_trans ?_ hTrace⟩
    rw [htr]
    exact Finset.single_le_sum (fun j _ => (hA.eigenvalues_pos j).le) (Finset.mem_univ i)
  simpa only [complexProjectedHessian, mul_zero, zero_mul] using hermitianRealification_quadratic_bounds_of_eigenvalues
    hA.isHermitian hE v

end KEBall
