import KEBall.DirichletRotations
import KEBall.DirichletCofactorContraction

/-!
# The actual rotation derivative equation for the real cofactor operator

The zero boundary value, smoothness and source estimates below apply to
`x ↦ Du(x)(T x)` for the original Dirichlet solution.  The real/complex
normalization is inherited from the verified cofactor contraction identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem smoothNear_dirichlet_linearFieldDerivative {n : ℕ}
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u) (T : E n →L[ℝ] E n) :
    SmoothNear (closedUnitBall n) (fun x => fderiv ℝ u x (T x)) := by
  obtain ⟨U, hU, hSub, huU⟩ := hu
  exact ⟨U, hU, hSub, (huU.fderiv_of_isOpen hU (by simp)).clm_apply T.contDiff.contDiffOn⟩

theorem dirichletBilinearContraction_cofactor_eq {n : ℕ}
    (u v : E n → ℝ) {x : E n} (hv : ContDiffAt ℝ 2 v x) :
    dirichletBilinearContraction e[n] (dirichletCofactorOfMatrix (complexHessian u x))
      (realHessian v x) = MoserTrudinger.cofactorContraction u v x := by
  rw [dirichletBilinearContraction_cofactor, complexHessianOfRealBilinear_eq hv]
  unfold MoserTrudinger.cofactorContraction
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_comm

theorem dirichlet_rotation_cofactor_equation {n : ℕ} {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (T : E n →L[ℝ] E n) (hTJ : ∀ y, T (J y) = J (T y))
    (M : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ y, complexCoord (T y) = M *ᵥ complexCoord y)
    (hM : Mᴴᵀ = -Mᵀ) {x : E n} (hx : x ∈ unitBall n) :
    dirichletBilinearContraction e[n] (dirichletCofactorOfMatrix (complexHessian u x))
      (realHessian (fun y => fderiv ℝ u y (T y)) x) =
      f x * fderiv ℝ (fun y => Real.log (f y)) x (T x) := by
  have hR := smoothNear_dirichlet_linearFieldDerivative hu T
  rw [dirichletBilinearContraction_cofactor_eq u _
      ((hR.contDiffAt (ball_subset_closedBall hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    cofactorContraction_eq_det_mul_complexLaplacian (huP x hx), hEq x hx,
    complexLaplacian_skewHermitianField_eq_logDensity hu hf huP hEq T hTJ M hT hM hx]

theorem dirichlet_linearFieldDerivative_zero_on_sphere {n : ℕ}
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (T : E n →L[ℝ] E n) (hTangent : ∀ x ∈ unitSphere n, inner ℝ x (T x) = 0)
    {x : E n} (hx : x ∈ unitSphere n) : fderiv ℝ u x (T x) = 0 := by
  rw [sphere_fderiv_normal hu hu0 hx, hTangent x hx, mul_zero]

theorem abs_dirichlet_rotation_cofactor_source_le {n : ℕ} {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (T : E n →L[ℝ] E n) (hTJ : ∀ y, T (J y) = J (T y))
    (M : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ y, complexCoord (T y) = M *ᵥ complexCoord y)
    (hM : Mᴴᵀ = -Mᵀ) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hDensity : ∀ x ∈ unitBall n, f x ≤ B)
    (hLog : ∀ x ∈ unitBall n, ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K)
    {x : E n} (hx : x ∈ unitBall n) :
    |dirichletBilinearContraction e[n] (dirichletCofactorOfMatrix (complexHessian u x))
      (realHessian (fun y => fderiv ℝ u y (T y)) x)| ≤ B * K * ‖T‖ := by
  rw [dirichlet_rotation_cofactor_equation hu hf huP hEq T hTJ M hT hM hx, abs_mul]
  have hf0 : 0 ≤ f x := (hEq x hx) ▸ (posDef_det_re_pos (huP x hx)).le
  rw [abs_of_nonneg hf0]
  have hTx : ‖T x‖ ≤ ‖T‖ :=
    (T.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _)
      (mem_ball_zero_iff.mp hx).le)
  have hD : |fderiv ℝ (fun y => Real.log (f y)) x (T x)| ≤ K * ‖T‖ := by
    have h := (fderiv ℝ (fun y => Real.log (f y)) x).le_opNorm (T x)
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul (hLog x hx) hTx (norm_nonneg _) hK)
  calc
    f x * |fderiv ℝ (fun y => Real.log (f y)) x (T x)| ≤ B * (K * ‖T‖) :=
      mul_le_mul (hDensity x hx) hD (abs_nonneg _) hB
    _ = B * K * ‖T‖ := by ring

end KEBall
