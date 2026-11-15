import KEBall.DirichletClassicalComparison
import KEBall.DirichletUnitaryFlow
import KEBall.DirichletRotations

/-! Covariance of the complex Hessian under unitary changes of coordinates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Matrix Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

theorem realHessian_comp_linearIsometryEquiv {n : ℕ} (u : E n → ℝ)
    (R : E n ≃ₗᵢ[ℝ] E n) (x a b : E n) :
    realHessian (u ∘ R) x a b = realHessian u (R x) (R a) (R b) := by
  let e := R.toContinuousLinearEquiv
  have h := e.iteratedFDerivWithin_comp_right u
    (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set (E n))) (mem_univ (e x)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have hvec : (fun i => e (![a, b] i)) = ![e a, e b] := by
    ext i
    fin_cases i <;> rfl
  change realHessian (u ∘ e) x a b = realHessian u (e x) (e a) (e b)
  have hLeft : iteratedFDeriv ℝ 2 (u ∘ e) x ![a, b] = realHessian (u ∘ e) x a b := by
    simp only [iteratedFDeriv_two_apply, realHessian, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hLeft, h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ 2 u (e x) (fun i => e (![a, b] i)) = _
  rw [hvec]
  simp only [iteratedFDeriv_two_apply, realHessian, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem complexCoordinates_apply_J {n : ℕ} (x : E n) :
    complexCoordinates n (J x) = Complex.I • complexCoordinates n x := by
  ext i
  change complexCoord (J x) i = Complex.I * complexCoord x i
  exact complexCoord_J x i

private noncomputable def unitaryComplexLinearIsometry {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (hJ : ∀ x, R (J x) = J (R x)) :
    EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) := by
  let e := complexCoordinates n
  let F := e.symm.trans (R.trans e)
  have hI (z : EuclideanSpace ℂ (Fin n)) : F (Complex.I • z) = Complex.I • F z := by
    have hInv : e.symm (Complex.I • z) = J (e.symm z) := by
      apply e.injective
      rw [e.apply_symm_apply, complexCoordinates_apply_J, e.apply_symm_apply]
    change e (R (e.symm (Complex.I • z))) = Complex.I • e (R (e.symm z))
    rw [hInv, hJ, complexCoordinates_apply_J]
  exact
    { toLinearMap :=
        { toFun := F
          map_add' := F.map_add
          map_smul' := fun c z => by
            change F (c • z) = c • F z
            rw [← Complex.re_add_im c]
            simp only [add_smul, mul_smul, map_add, Complex.coe_smul, map_smul, hI] }
      norm_map' := F.norm_map }

private theorem exists_matrix_of_complexLinearIsometry {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (hJ : ∀ x, R (J x) = J (R x)) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, (∀ x, complexCoord (R x) = M *ᵥ complexCoord x) ∧
      Mᴴ * M = 1 := by
  let C := unitaryComplexLinearIsometry R hJ
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.toEuclideanLin.symm C.toLinearMap
  have hM : M.toEuclideanLin = C.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hApply (z : Fin n → ℂ) : M *ᵥ z = WithLp.ofLp (C (WithLp.toLp 2 z)) := by
    have h := Matrix.ofLp_toLpLin 2 2 M (WithLp.toLp 2 z)
    change WithLp.ofLp (M.toEuclideanLin (WithLp.toLp 2 z)) = M *ᵥ z at h
    rw [hM] at h
    exact h.symm
  have hCoord (x : E n) : complexCoord (R x) = M *ᵥ complexCoord x := by
    rw [hApply]
    change WithLp.ofLp (complexCoordinates n (R x)) =
      WithLp.ofLp (complexCoordinates n (R ((complexCoordinates n).symm (complexCoordinates n x))))
    rw [LinearIsometryEquiv.symm_apply_apply]
  refine ⟨M, hCoord, ?_⟩
  apply Matrix.mulVec_injective
  funext z
  rw [Matrix.one_mulVec, ← mulVec_mulVec]
  have hAdj : Mᴴ.toEuclideanLin = C.toLinearMap.adjoint := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hM]
  have hConj : Mᴴ *ᵥ (M *ᵥ z) = WithLp.ofLp (C.toLinearMap.adjoint (C (WithLp.toLp 2 z))) := by
    have h := Matrix.ofLp_toLpLin 2 2 Mᴴ (C (WithLp.toLp 2 z))
    change WithLp.ofLp (Mᴴ.toEuclideanLin (C (WithLp.toLp 2 z))) =
      Mᴴ *ᵥ WithLp.ofLp (C (WithLp.toLp 2 z)) at h
    rw [hAdj, ← hApply z] at h
    exact h.symm
  rw [hConj]
  have hIs := LinearIsometry.adjoint_comp_self' C
  exact congrArg WithLp.ofLp (LinearMap.congr_fun hIs (WithLp.toLp 2 z))

/-- Unitary pullback preserves positivity and the determinant of the
complex Hessian, with the evaluation point transported by the isometry. -/
theorem complexHessian_posDef_and_det_comp_unitary {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (hJ : ∀ x, R (J x) = J (R x))
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ 2 u (R x)) :
    ((complexHessian (u ∘ R) x).PosDef ↔ (complexHessian u (R x)).PosDef) ∧
      (complexHessian (u ∘ R) x).det = (complexHessian u (R x)).det := by
  obtain ⟨M, hCoord, hM⟩ := exists_matrix_of_complexLinearIsometry R hJ
  let H := complexHessian u (R x)
  have huR : ContDiffAt ℝ 2 (u ∘ R) x :=
    hu.comp x R.toContinuousLinearEquiv.contDiff.contDiffAt
  have hForm (v w : E n) : realMetricForm (u ∘ R) x v w = realMetricForm u (R x) (R v) (R w) := by
    rw [realMetricForm_eq_average_hessian_C2 huR, realMetricForm_eq_average_hessian_C2 hu,
      realHessian_comp_linearIsometryEquiv, realHessian_comp_linearIsometryEquiv, hJ v, hJ w]
  have hMat : complexHessian (u ∘ R) x = Mᵀ * H * Mᴴᵀ := by
    apply hermitianRealification_injective
    ext v w
    rw [← realMetricForm_eq, hForm, realMetricForm_eq, hermitianRealification_eq_re_dotProduct,
      hermitianRealification_eq_re_dotProduct, hCoord v, hCoord w]
    congr 2
    change (M *ᵥ complexCoord v) ⬝ᵥ (H *ᵥ star (M *ᵥ complexCoord w)) =
      complexCoord v ⬝ᵥ ((Mᵀ * H * Mᴴᵀ) *ᵥ star (complexCoord w))
    rw [star_mulVec, ← mulVec_transpose, Matrix.mul_assoc]
    let z := (H * Mᴴᵀ) *ᵥ star (complexCoord w)
    rw [mulVec_mulVec (star (complexCoord w)) H Mᴴᵀ,
      ← mulVec_mulVec (star (complexCoord w)) Mᵀ (H * Mᴴᵀ)]
    change (M *ᵥ complexCoord v) ⬝ᵥ z = complexCoord v ⬝ᵥ (Mᵀ *ᵥ z)
    rw [dotProduct_transpose_mulVec, dotProduct_comm]
  have hInv' : Mᵀ * Mᴴᵀ = 1 := by
    rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]
  have hInv : Mᴴᵀ * Mᵀ = 1 := mul_eq_one_comm.mp hInv'
  have hTranspose : (Mᵀ)ᴴ = Mᴴᵀ := by
    ext i j
    rfl
  have hInj : Function.Injective Mᴴᵀ.mulVec := by
    intro v w he
    have h := congrArg (Mᵀ *ᵥ ·) he
    rwa [mulVec_mulVec, mulVec_mulVec, hInv', one_mulVec, one_mulVec] at h
  have hInj' : Function.Injective Mᵀ.mulVec := by
    intro v w he
    have h := congrArg (Mᴴᵀ *ᵥ ·) he
    rwa [mulVec_mulVec, mulVec_mulVec, hInv, one_mulVec, one_mulVec] at h
  rw [hMat]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    have hh := h.conjTranspose_mul_mul_same (B := Mᵀ) hInj'
    rw [hTranspose, ← mul_assoc Mᴴᵀ (Mᵀ * H) Mᴴᵀ,
      ← mul_assoc Mᴴᵀ Mᵀ H, hInv, one_mul, mul_assoc H Mᴴᵀ Mᵀ,
      hInv, mul_one] at hh
    exact hh
  · intro h
    have hh := h.conjTranspose_mul_mul_same (B := Mᴴᵀ) hInj
    rw [← hTranspose, conjTranspose_conjTranspose, hTranspose] at hh
    exact hh
  · have hd := congrArg Matrix.det hInv'
    rw [det_mul, det_one] at hd
    rw [det_mul, det_mul, mul_right_comm, hd, one_mul]

end KEBall
