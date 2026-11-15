import KEBall.DirichletMatrixFiniteLpJets

/-! Nonlinear and linearized rank-one normal recovery for actual finite Lp jets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem hasDirichletFiniteLpJets_of_rankOne_det {n m k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A : E n → Matrix (Fin m) (Fin m) ℂ} {z : E n → Fin m → ℂ} {t f : E n → ℝ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j))
    (hz : ∀ i, HasDirichletComplexFiniteLpJets U μ k (fun x => z x i))
    (hP : ∀ x ∈ U, (A x).PosDef) (hZ : ∀ x ∈ U, z x ≠ 0)
    (hf : HasDirichletFiniteLpJets U μ k f) {C : ℝ}
    (hBound : ∀ x ∈ U, ‖(hermitianRankOneDetSlope (A x) (z x))⁻¹‖ ≤ C)
    (hEq : ∀ x ∈ U, (A x + (t x : ℂ) • Matrix.vecMulVec (z x) (star (z x))).det.re = f x) :
    HasDirichletFiniteLpJets U μ k t := by
  have hD := (hasDirichletComplexFiniteLpJets_det hU hμ hA).1
  have hS := hasDirichletFiniteLpJets_hermitianRankOneDetSlope hU hμ hA hz
  refine ((hf.sub hU hμ hD).div hU hμ hS
    (fun x hx => (hermitianRankOneDetSlope_pos (hP x hx) (hZ x hx)).ne') hBound).congr hU hμ ?_
  intro x hx
  change (f x-(A x).det.re) / hermitianRankOneDetSlope (A x) (z x) = t x
  rw [hermitianRankOneDetSlope_eq (hP x hx),← hEq x hx]
  exact (real_rankOne_coefficient_eq_of_det (hP x hx) (hZ x hx) rfl).symm

theorem hasDirichletFiniteLpJets_of_rankOne_linearized_det {n m k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A D : E n → Matrix (Fin m) (Fin m) ℂ} {z : E n → Fin m → ℂ} {t f : E n → ℝ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j))
    (hD : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => D x i j))
    (hz : ∀ i, HasDirichletComplexFiniteLpJets U μ k (fun x => z x i))
    (hP : ∀ x ∈ U, (A x).PosDef) (hZ : ∀ x ∈ U, z x ≠ 0)
    (hf : HasDirichletFiniteLpJets U μ k f) {C : ℝ}
    (hBound : ∀ x ∈ U, ‖(hermitianRankOneDetSlope (A x) (z x))⁻¹‖ ≤ C)
    (hEq : ∀ x ∈ U, ((A x).adjugate *
      (D x + (t x : ℂ) • Matrix.vecMulVec (z x) (star (z x)))).trace.re = f x) :
    HasDirichletFiniteLpJets U μ k t := by
  let g (x : E n) := ((A x).adjugate * D x).trace.re
  have hG := hasDirichletFiniteLpJets_adjugate_trace hU hμ hA hD
  have hS := hasDirichletFiniteLpJets_hermitianRankOneDetSlope hU hμ hA hz
  refine ((hf.sub hU hμ hG).div hU hμ hS
    (fun x hx => (hermitianRankOneDetSlope_pos (hP x hx) (hZ x hx)).ne') hBound).congr hU hμ ?_
  intro x hx
  change (f x-g x)/hermitianRankOneDetSlope (A x) (z x) = t x
  rw [div_eq_iff (hermitianRankOneDetSlope_pos (hP x hx) (hZ x hx)).ne',← hEq x hx]
  have hTrace (M : Matrix (Fin m) (Fin m) ℂ) (v w : Fin m → ℂ) :
      (M * Matrix.vecMulVec v w).trace = w ⬝ᵥ (M *ᵥ v) := by
    rw [Matrix.mul_vecMulVec]
    simp [Matrix.trace,Matrix.diag,Matrix.vecMulVec_apply,dotProduct,mul_comm]
  simp only [g,Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,smul_eq_mul,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    hTrace,hermitianRankOneDetSlope]
  ring

end KEBall
