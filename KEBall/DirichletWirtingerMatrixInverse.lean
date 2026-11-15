import KEBall.ComplexFlux
import KEBall.LogDetConcavity

/-! Actual Wirtinger differentiation of the matrix inverse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 200000
open Filter Matrix
open scoped ContDiff BigOperators Matrix Matrix.Norms.Elementwise Topology
namespace KEBall
open KEBallProbe
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dirichlet_matrix_inv_entry_differentiableAt {G : V → Matrix ι ι ℂ} {x : V}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x)
    (hdet : (G x).det≠0) (i j : ι) :
    DifferentiableAt ℝ (fun y => (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def,Matrix.smul_apply,Ring.inverse_eq_inv',smul_eq_mul]
  exact ((field_det_differentiableAt hG).inv hdet).mul
    (field_adjugate_differentiableAt hG i j)

theorem dirichlet_dz_matrix_mul {F G : V → Matrix ι ι ℂ} {x : V}
    (hF : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) (a b : V) :
    (Matrix.of fun i j => dz a b (fun y => (F y*G y) i j) x)=
      (Matrix.of fun i j => dz a b (fun y => F y i j) x)*G x+
        F x*(Matrix.of fun i j => dz a b (fun y => G y i j) x) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.add_apply,Matrix.of_apply]
  rw [dz_sum_differentiableAt (f := fun k y => F y i k * G y k j)
    (fun k => (hF i k).fun_mul (hG k j))]
  simp_rw [dz_mul_differentiableAt (hF i _) (hG _ j)]
  rw [Finset.sum_add_distrib]

theorem dirichlet_dz_matrix_inv {G : V → Matrix ι ι ℂ} {x : V}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x)
    (hdet : (G x).det≠0) (a b : V) :
    (Matrix.of fun i j => dz a b (fun y => (G y)⁻¹ i j) x)=
      -((G x)⁻¹*(Matrix.of fun i j => dz a b (fun y => G y i j) x)*(G x)⁻¹) := by
  have hI := dirichlet_matrix_inv_entry_differentiableAt hG hdet
  have hNe : ∀ᶠ y in 𝓝 x, (G y).det≠0 :=
    (field_det_differentiableAt hG).continuousAt.eventually_ne hdet
  have hZero : (Matrix.of fun i j => dz a b (fun y => (G y*(G y)⁻¹) i j) x)=0 := by
    ext i j
    simp only [Matrix.of_apply,Matrix.zero_apply]
    have he : (fun y => (G y*(G y)⁻¹) i j)=ᶠ[𝓝 x] (fun _ => (1 : Matrix ι ι ℂ) i j) := by
      filter_upwards [hNe] with y hy
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy)]
    rw [LogDetAux.dz_congr_of_eventuallyEq he]
    simp only [dz,rd,fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.zero_apply,
      mul_zero,sub_self]
  have h := dirichlet_dz_matrix_mul hG hI a b
  rw [hZero] at h
  have h' := congrArg (fun N : Matrix ι ι ℂ => (G x)⁻¹*N) h.symm
  simp only [Matrix.mul_add,← mul_assoc,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    one_mul,mul_zero] at h'
  exact eq_neg_of_add_eq_zero_right h'

end KEBall
