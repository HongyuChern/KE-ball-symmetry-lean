import KEBall.DirichletUnitaryHessian
import KEBall.DirichletTangentGenerator

/-! Every actual real unitary infinitesimal field has its skew-Hermitian matrix. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix Set
open scoped ComplexOrder ContDiff

namespace KEBall

theorem exists_dirichlet_skewHermitian_matrix_of_field {n : ℕ}
    (R : E n →L[ℝ] E n) (hR : star R = -R) (hJ : ∀ x, R (J x) = J (R x)) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ,
      (∀ x, complexCoord (R x) = M *ᵥ complexCoord x) ∧ Mᴴᵀ = -Mᵀ := by
  let e := complexCoordinates n
  let F := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (R.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have heJ (x : E n) : e (J x) = Complex.I • e x := by
    ext i
    exact complexCoord_J x i
  have hI (z : EuclideanSpace ℂ (Fin n)) : F (Complex.I • z) = Complex.I • F z := by
    have hInv : e.symm (Complex.I • z) = J (e.symm z) := by
      apply e.injective
      rw [e.apply_symm_apply, heJ, e.apply_symm_apply]
    change e (R (e.symm (Complex.I • z))) = Complex.I • e (R (e.symm z))
    rw [hInv, hJ, heJ]
  let B₀ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toFun := F
      map_add' := F.map_add
      map_smul' := fun c z => by
        change F (c • z) = c • F z
        rw [← Complex.re_add_im c]
        simp only [add_smul, mul_smul, map_add, Complex.coe_smul, map_smul, hI] }
  let B := B₀.toContinuousLinearMap
  have hApply (x : E n) : B (e x) = e (R x) := by
    change e (R (e.symm (e x))) = e (R x)
    rw [e.symm_apply_apply]
  have hPair (x y : E n) : inner ℂ (e x) (e y) =
      (inner ℝ x y : ℂ) + Complex.I * (inner ℝ (J x) y : ℂ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact complexCoord_pairing x y
  have hSkew (x y : E n) : inner ℝ (R x) y = -inner ℝ x (R y) := by
    have h := ContinuousLinearMap.adjoint_inner_right R x y
    rw [← ContinuousLinearMap.star_eq_adjoint, hR, _root_.neg_apply, inner_neg_right] at h
    exact h.symm
  have hBAdj : B.adjoint = -B := by
    ext1 z
    apply ext_inner_left ℂ
    intro w
    obtain ⟨x, rfl⟩ := e.surjective w
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [ContinuousLinearMap.adjoint_inner_right, _root_.neg_apply,
      inner_neg_right, hApply, hApply, hPair, hPair, ← hJ, hSkew, hSkew]
    push_cast
    ring
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.toEuclideanLin.symm B.toLinearMap
  have hM : M.toEuclideanLin = B.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hMAdj : Mᴴ = -M := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, map_neg, hM,
      ContinuousLinearMap.adjoint_toLinearMap, hBAdj]
    rfl
  refine ⟨M, ?_, ?_⟩
  · intro x
    have hMat := Matrix.ofLp_toLpLin 2 2 M (e x)
    change WithLp.ofLp (M.toEuclideanLin (e x)) = M *ᵥ WithLp.ofLp (e x) at hMat
    rw [hM] at hMat
    exact (congrArg WithLp.ofLp (hApply x)).symm.trans hMat
  · rw [hMAdj, Matrix.transpose_neg]

theorem inner_dirichlet_skew_field_self {n : ℕ} (R : E n →L[ℝ] E n)
    (hR : star R = -R) (x : E n) : inner ℝ x (R x) = 0 := by
  have h := ContinuousLinearMap.adjoint_inner_right R x x
  rw [← ContinuousLinearMap.star_eq_adjoint, hR, _root_.neg_apply,
    inner_neg_right] at h
  linarith [real_inner_comm (R x) x]

end KEBall
