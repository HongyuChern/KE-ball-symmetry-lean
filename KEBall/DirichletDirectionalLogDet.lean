import KEBall.DirichletCofactorContraction
import KEBall.DirichletHessianDirectionalFrame
import KEBall.DirichletHessianOscillationAlgebra

/-!
# Two-point comparison for the actual directional Hessians

Log-determinant concavity is used at the cofactor at the first point.
The positive finite frame is that of this same cofactor.  In particular,
the scalar family below consists of evaluations of the original real
bilinear Hessian, not of an independently chosen matrix representative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open InnerProductSpace Matrix MeasureTheory
open scoped BigOperators ComplexOrder

noncomputable section

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem complexHessianOfRealBilinear_sub {n : ℕ}
    (D F : E n →L[ℝ] E n →L[ℝ] ℝ) :
    complexHessianOfRealBilinear (D - F) =
      complexHessianOfRealBilinear D - complexHessianOfRealBilinear F := by
  ext i j
  simp only [complexHessianOfRealBilinear, _root_.sub_apply, Matrix.sub_apply, Complex.ofReal_sub]
  ring

theorem dirichlet_cofactor_logdet_comparison {n : ℕ}
    (D F : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hD : (complexHessianOfRealBilinear D).PosDef)
    (hF : (complexHessianOfRealBilinear F).PosDef) :
    dirichletBilinearContraction e[n]
        (dirichletCofactorOfMatrix (complexHessianOfRealBilinear D)) (D - F) ≤
      (complexHessianOfRealBilinear D).det.re *
        (Real.log (complexHessianOfRealBilinear D).det.re -
          Real.log (complexHessianOfRealBilinear F).det.re) := by
  let A := complexHessianOfRealBilinear D
  let B := complexHessianOfRealBilinear F
  have ht := mul_le_mul_of_nonneg_left (posDef_logdet_tangent hD hF)
    (posDef_det_re_pos hD).le
  have he (C : Matrix (Fin n) (Fin n) ℂ) :
      (A.adjugate * C).trace.re = A.det.re * (A⁻¹ * C).trace.re := by
    rw [adjugate_eq_det_smul_inv hD, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      posDef_det_eq_ofReal_re hD]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  change A.det.re * (Real.log B.det.re - Real.log A.det.re) ≤
    A.det.re * (A⁻¹ * (B - A)).trace.re at ht
  rw [← he] at ht
  rw [dirichletBilinearContraction_cofactor, complexHessianOfRealBilinear_sub]
  change (A.adjugate * (A - B)).trace.re ≤ A.det.re * (Real.log A.det.re - Real.log B.det.re)
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at ht ⊢
  nlinarith only [ht]

theorem dirichlet_directional_logdet_comparison {n m : ℕ}
    (D F : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hD : (complexHessianOfRealBilinear D).PosDef)
    (hF : (complexHessianOfRealBilinear F).PosDef)
    (v : Fin m → E n) (β : Fin m → ℝ)
    (hFrame : dirichletCofactorOfMatrix (complexHessianOfRealBilinear D) =
      ∑ k : Fin m, β k • rankOne ℝ (v k) (v k)) :
    (∑ k : Fin m, β k * (D (v k) (v k) - F (v k) (v k))) ≤
      (complexHessianOfRealBilinear D).det.re *
        (Real.log (complexHessianOfRealBilinear D).det.re -
          Real.log (complexHessianOfRealBilinear F).det.re) := by
  have h := dirichlet_cofactor_logdet_comparison D F hD hF
  rw [dirichletBilinearContraction_of_frame e[n] (D - F) β v hFrame] at h
  simpa only [_root_.sub_apply] using h

/-- The finite directional comparison holds for the actual a.e. Hessian
and the actual prescribed exponential density, with one fixed family of
directions and uniformly positive weights. -/
theorem exists_dirichlet_directional_comparison {n : ℕ}
    {D : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {g : E n → ℝ}
    (hPos : ∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (D x)).PosDef)
    (hDet : ∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (D x)).det.re = Real.exp (g x))
    (hFrame : HasUniformDirichletDirectionalFrame
      (fun x => dirichletCofactorOfMatrix (complexHessianOfRealBilinear (D x)))) :
    ∃ (m : ℕ) (v : Fin m → E n) (c C : ℝ), 0 < c ∧ 0 < C ∧
      (∀ i : Fin (2 * n), ∃ k : Fin m, v k = e[n] i) ∧
      (∀ i j : Fin (2 * n), ∃ k : Fin m, v k = e[n] i + e[n] j) ∧
      ∀ᵐ x ∂ν[n], ∃ β : Fin m → ℝ, (∀ k, c ≤ β k ∧ β k ≤ C) ∧
        ∀ᵐ y ∂ν[n], (∑ k : Fin m, β k * (D x (v k) (v k) - D y (v k) (v k))) ≤
          Real.exp (g x) * (g x - g y) := by
  obtain ⟨m, v, c, C, hc, hC, hb, hp, hRep⟩ := hFrame
  refine ⟨m, v, c, C, hc, hC, hb, hp, ?_⟩
  filter_upwards [hPos, hDet, hRep] with x hx hxDet hxRep
  obtain ⟨β, hβ, hβRep⟩ := hxRep
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hPos, hDet] with y hy hyDet
  have h := dirichlet_directional_logdet_comparison (D x) (D y) hx hy v β hβRep
  simpa only [hxDet, hyDet, Real.log_exp] using h

end KEBall
