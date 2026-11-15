import KEBall.DirichletWirtingerLog
import KEBall.DirichletWirtingerMatrixInverse

/-! The actual first and second Wirtinger derivatives of a positive matrix log determinant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 400000
open Filter Set Matrix
open scoped ContDiff BigOperators ComplexOrder Matrix Matrix.Norms.Elementwise Topology
namespace KEBall
open KEBallProbe
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem dirichlet_dz_matrix_trace {ι : Type*} [Fintype ι]
    {G : V → Matrix ι ι ℂ} {x : V}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) (a b : V) :
    dz a b (fun y => (G y).trace) x=
      (Matrix.of fun i j => dz a b (fun y => G y i j) x).trace :=
  dz_sum_differentiableAt (fun i => hG i i) a b

theorem dirichlet_dz_logdet {n : ℕ} {G : V → Matrix (Fin n) (Fin n) ℂ} {x : V}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x)
    (hP : ∀ᶠ y in 𝓝 x, (G y).PosDef) (a b : V) :
    dz a b (fun y => (Real.log (G y).det.re : ℂ)) x=
      ((G x)⁻¹*(Matrix.of fun i j => dz a b (fun y => G y i j) x)).trace := by
  have hPx : (G x).PosDef := hP.self_of_nhds
  have hUnit : IsUnit (G x).det := (Matrix.isUnit_iff_isUnit_det _).mp hPx.isUnit
  have hR : DifferentiableAt ℝ (fun y => (G y).det.re) x :=
    (Complex.reCLM.hasFDerivAt.comp x (field_det_differentiableAt hG).hasFDerivAt).differentiableAt
  have he : (fun y => (((G y).det.re : ℝ) : ℂ))=ᶠ[𝓝 x] (fun y => (G y).det) := by
    filter_upwards [hP] with y hy
    exact (posDef_det_eq_ofReal_re hy).symm
  rw [dirichlet_dz_log_real hR (ne_of_gt (posDef_det_re_pos hPx)),
    LogDetAux.dz_congr_of_eventuallyEq he,← posDef_det_eq_ofReal_re hPx,dz_det_field hG]
  have hAdj := adjugate_contraction_eq_det_mul (G x)
    (Matrix.of fun i j => dz a b (fun y => G y i j) x) hUnit
  simp only [Matrix.of_apply] at hAdj
  rw [hAdj,← mul_assoc,inv_mul_cancel₀ (isUnit_iff_ne_zero.mp hUnit),one_mul]
  simp only [Matrix.trace,Matrix.mul_apply,Matrix.of_apply]
  exact Finset.sum_comm

theorem dirichlet_dz_dz_logdet {n : ℕ} {U : Set V}
    (hU : IsOpen U) {G : V → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun y => G y i j) U)
    (hP : ∀ y∈U, (G y).PosDef) {x : V} (hx : x∈U) (a b c d : V) :
    dz a b (dz c d (fun y => (Real.log (G y).det.re : ℂ))) x=
      ((G x)⁻¹*(Matrix.of fun i j => dz a b (dz c d (fun y => G y i j)) x)).trace-
        ((G x)⁻¹*(Matrix.of fun i j => dz a b (fun y => G y i j) x)*(G x)⁻¹*
          (Matrix.of fun i j => dz c d (fun y => G y i j) x)).trace := by
  have hGx (i j : Fin n) : DifferentiableAt ℝ (fun y => G y i j) x :=
    ((hG i j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdet : (G x).det≠0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hP x hx).isUnit)
  let D : V → Matrix (Fin n) (Fin n) ℂ :=
    fun y => Matrix.of fun i j => dz c d (fun z => G z i j) y
  have hD (i j : Fin n) : DifferentiableAt ℝ (fun y => D y i j) x :=
    ((smoothOn_dz hU (hG i j) c d).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hI := dirichlet_matrix_inv_entry_differentiableAt hGx hdet
  have he : dz c d (fun y => (Real.log (G y).det.re : ℂ))=ᶠ[𝓝 x]
      (fun y => ((G y)⁻¹*D y).trace) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    apply dirichlet_dz_logdet
      (fun i j => ((hG i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hP z hz
  have hProd (i j : Fin n) : DifferentiableAt ℝ (fun y => ((G y)⁻¹*D y) i j) x := by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (hI i k).fun_mul (hD k j)
  rw [LogDetAux.dz_congr_of_eventuallyEq he,dirichlet_dz_matrix_trace hProd,
    dirichlet_dz_matrix_mul hI hD,dirichlet_dz_matrix_inv hGx hdet]
  simp only [neg_mul,Matrix.trace_add,Matrix.trace_neg,D,Matrix.of_apply]
  ring

end KEBall
