import KEBall.DirichletHessianL2Limit

/-! Passing positivity and the determinant through almost-everywhere convergence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Matrix MeasureTheory Set
open scoped ComplexOrder Matrix Matrix.Norms.Elementwise Topology

namespace KEBall

/-- Recover the matrix entries from their Euclidean coordinate vector. -/
def dirichletHessianMatrix {n : ℕ} (z : DirichletHessianCoordinates n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => z (i, j)

@[simp] theorem dirichletHessianMatrix_coordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    dirichletHessianMatrix (dirichletHessianCoordinates A) = A := rfl

private theorem continuous_dirichletHessianMatrix (n : ℕ) :
    Continuous (dirichletHessianMatrix (n := n)) :=
  continuous_matrix fun i j => (EuclideanSpace.proj (i, j)).continuous

private theorem posSemidef_of_tendsto_matrix {n : ℕ} {A : ℕ → Matrix (Fin n) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ}
    (hT : Tendsto A atTop (𝓝 B)) (hP : ∀ j, (A j).PosSemidef) : B.PosSemidef := by
  have hHerm : B.IsHermitian := by
    have hC : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => Aᴴ) :=
      continuous_id.matrix_conjTranspose
    exact tendsto_nhds_unique ((hC.tendsto B).comp hT)
      (hT.congr fun j => (hP j).isHermitian.eq.symm)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  let F (C : Matrix (Fin n) (Fin n) ℂ) := star v ⬝ᵥ (C *ᵥ v)
  have hC : Continuous F :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact isClosed_Ici.mem_of_tendsto ((hC.tendsto B).comp hT)
    (Eventually.of_forall fun j => (hP j).dotProduct_mulVec_nonneg v)

/-- The almost-everywhere Hessian limit has the limiting determinant
and is positive definite wherever the limiting density is positive. -/
theorem ae_posDef_and_det_eq_of_dirichletHessian_limit {n : ℕ}
    {μ : Measure (E n)} {A : ℕ → E n → Matrix (Fin n) (Fin n) ℂ}
    {H : E n → DirichletHessianCoordinates n} {p : E n → ℝ}
    (hA : ∀ᵐ x ∂μ, ∀ j, (A j x).PosDef)
    (hH : ∀ᵐ x ∂μ, Tendsto (fun j => dirichletHessianCoordinates (A j x)) atTop (𝓝 (H x)))
    (hD : ∀ᵐ x ∂μ, Tendsto (fun j => (A j x).det.re) atTop (𝓝 (p x)))
    (hP : ∀ᵐ x ∂μ, 0 < p x) :
    ∀ᵐ x ∂μ, (dirichletHessianMatrix (H x)).PosDef ∧
      (dirichletHessianMatrix (H x)).det.re = p x := by
  filter_upwards [hA, hH, hD, hP] with x hxA hxH hxD hxP
  let B := dirichletHessianMatrix (H x)
  have hT : Tendsto (fun j => A j x) atTop (𝓝 B) := by
    exact (((continuous_dirichletHessianMatrix n).tendsto (H x)).comp hxH).congr
      (fun j => dirichletHessianMatrix_coordinates (A j x))
  have hPSD := posSemidef_of_tendsto_matrix hT (fun j => (hxA j).posSemidef)
  have hDet := tendsto_nhds_unique
    ((Complex.continuous_re.comp continuous_id.matrix_det).tendsto B |>.comp hT) hxD
  refine ⟨hPSD.posDef_iff_det_ne_zero.mpr ?_, hDet⟩
  intro he
  change B.det.re = p x at hDet
  rw [he, Complex.zero_re] at hDet
  exact hxP.ne' hDet.symm

end KEBall
