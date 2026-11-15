import KEBall.DirichletCofactorMonotonicity
import KEBall.DirichletLaplacianTrace

/-! The exact positive trace comparison used in the Ricci-iteration cancellation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ContDiff Laplacian
namespace KEBall

private theorem dirichlet_trace_mul_re_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  obtain ⟨C,hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  change A=Cᴴ*C at hC
  rw [hC,← Matrix.trace_mul_cycle]
  exact (RCLike.nonneg_iff.mp (hB.mul_mul_conjTranspose_same C).trace_nonneg).1

theorem dirichlet_posDef_trace_re_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) : 0<A.trace.re := by
  have he : A.trace.re=∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues,← RCLike.ofReal_sum]
    rfl
  rw [he]
  exact Finset.sum_pos (fun i _ => hA.eigenvalues_pos i) Finset.univ_nonempty

theorem dirichlet_posSemidef_trace_ratio_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosSemidef) :
    B.trace.re/A.trace.re ≤ (A⁻¹*B).trace.re := by
  have hTrace : A.trace.re=∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues,← RCLike.ofReal_sum]
    rfl
  have hEig (i : ι) : hA.isHermitian.eigenvalues i ≤ A.trace.re := by
    rw [hTrace]
    exact Finset.single_le_sum (fun j _ => (hA.eigenvalues_pos j).le) (Finset.mem_univ i)
  have hInv := smul_one_le_inverse_of_eigenvalues_le hA (dirichlet_posDef_trace_re_pos hA) hEig
  have h := dirichlet_trace_mul_re_nonneg (Matrix.le_iff.mp hInv) hB
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul,
    Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at h
  simpa only [div_eq_mul_inv,mul_comm] using sub_nonneg.mp h

theorem dirichlet_complexHessian_trace_ratio_le {n : ℕ} (hn : 0<n)
    (u v : E n → ℝ) (x : E n)
    (hu : (complexHessian u x).PosDef) (hv : (complexHessian v x).PosSemidef) :
    (complexHessian v x).trace.re/(complexHessian u x).trace.re ≤ complexLaplacian u v x := by
  letI : NeZero n := ⟨hn.ne'⟩
  rw [complexLaplacian_eq_trace]
  exact dirichlet_posSemidef_trace_ratio_le hu hv

end KEBall
