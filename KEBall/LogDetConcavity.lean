import KEBall.RadialJacobi
import Mathlib.Analysis.Matrix.Order

/-!
# The positive Hermitian log-determinant tangent inequality

The scalar logarithm inequality is summed over the actual Hermitian spectrum.
A Gram factor of the positive inverse matrix reduces the general tangent
inequality to the identity-matrix case.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace KEBall
open KEBallProbe

lemma posDef_det_re_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) : 0 < A.det.re :=
  (RCLike.pos_iff.mp hA.det_pos).1

lemma posDef_det_eq_ofReal_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) : A.det = (A.det.re : ℂ) := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  rfl

theorem posDef_logdet_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    Real.log A.det.re ≤ A.trace.re - (Fintype.card ι : ℝ) := by
  have hdet : A.det.re = ∏ i : ι, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    rfl
  have htrace : A.trace.re = ∑ i : ι, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    rfl
  rw [hdet, htrace, Real.log_prod (fun i _ => ne_of_gt (hA.eigenvalues_pos i))]
  calc
    (∑ i : ι, Real.log (hA.isHermitian.eigenvalues i)) ≤
        ∑ i : ι, (hA.isHermitian.eigenvalues i - 1) :=
      Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)
    _ = (∑ i : ι, hA.isHermitian.eigenvalues i) - (Fintype.card ι : ℝ) := by
      simp [Finset.sum_sub_distrib]

theorem posDef_logdet_tangent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det.re - Real.log A.det.re ≤ ((A⁻¹ * (B - A)).trace).re := by
  obtain ⟨C, hCeq⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.inv.posSemidef.nonneg
  change A⁻¹ = Cᴴ * C at hCeq
  have hCdet : IsUnit C.det := by
    have hprod : IsUnit (Cᴴ * C).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (hCeq ▸ hA.inv.isUnit)
    rw [Matrix.det_mul] at hprod
    exact isUnit_of_mul_isUnit_right hprod
  have hC : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hCdet
  have hnorm : (C * B * Cᴴ).PosDef :=
    hB.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hC)
  have htrace : (C * B * Cᴴ).trace = (A⁻¹ * B).trace := by
    rw [Matrix.trace_mul_cycle, ← hCeq]
  have hdet : (C * B * Cᴴ).det = A.det⁻¹ * B.det := by
    calc
      (C * B * Cᴴ).det = (Cᴴ * C).det * B.det := by
        simp only [Matrix.det_mul]
        ring
      _ = A⁻¹.det * B.det := by rw [← hCeq]
      _ = A.det⁻¹ * B.det := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hdetC : (C * B * Cᴴ).det = ((B.det.re / A.det.re : ℝ) : ℂ) := by
    calc
      (C * B * Cᴴ).det = A.det⁻¹ * B.det := hdet
      _ = (A.det.re : ℂ)⁻¹ * (B.det.re : ℂ) := by
        rw [← posDef_det_eq_ofReal_re hA, ← posDef_det_eq_ofReal_re hB]
      _ = ((B.det.re / A.det.re : ℝ) : ℂ) := by
        push_cast
        ring
  have hdetR : (C * B * Cᴴ).det.re = B.det.re / A.det.re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hdetC
  have hineq := posDef_logdet_le_trace hnorm
  rw [hdetR, htrace, Real.log_div (ne_of_gt (posDef_det_re_pos hB))
    (ne_of_gt (posDef_det_re_pos hA))] at hineq
  have hAunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hAunit, Matrix.trace_sub,
    Matrix.trace_one, Complex.sub_re, Complex.natCast_re]
  exact hineq

namespace LogDetAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma dz_sub_differentiableAt {f h : X → ℂ} {x : X}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (a b : X) :
    dz a b (fun y => f y - h y) x = dz a b f x - dz a b h x := by
  unfold dz rd
  rw [fderiv_fun_sub hf hh]
  simp only [sub_apply]
  ring

lemma dz_congr_of_eventuallyEq {f h : X → ℂ} {x : X}
    (heq : f =ᶠ[𝓝 x] h) (a b : X) : dz a b f x = dz a b h x := by
  have hd : fderiv ℝ f x = fderiv ℝ h x := heq.fderiv_eq
  simp only [dz, rd, hd]

lemma dz_dz_sub_at {f h : X → ℂ} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hh : ContDiffAt ℝ ∞ h x) (a b c d : X) :
    dz a b (dz c d (fun y => f y - h y)) x =
      dz a b (dz c d f) x - dz a b (dz c d h) x := by
  have hf₁ : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  have hh₁ : ContDiffAt ℝ 1 h x := hh.of_le (by simp)
  have hinner : dz c d (fun y => f y - h y) =ᶠ[𝓝 x]
      (fun y => dz c d f y - dz c d h y) := by
    filter_upwards [hf₁.eventually (by simp), hh₁.eventually (by simp)] with y hyf hyh
    exact dz_sub_differentiableAt (hyf.differentiableAt (by simp))
      (hyh.differentiableAt (by simp)) c d
  rw [dz_congr_of_eventuallyEq hinner]
  exact dz_sub_differentiableAt ((smoothAt_dz hf c d).differentiableAt (by simp))
    ((smoothAt_dz hh c d).differentiableAt (by simp)) a b

end LogDetAux

theorem complexHessian_sub_at {n : ℕ} {u v : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) :
    complexHessian (fun y => u y - v y) x = complexHessian u x - complexHessian v x := by
  have huC : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have hvC : ContDiffAt ℝ ∞ (fun y => (v y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hv
  ext i j
  change dz (realDirection i) (imagDirection i)
    (dz (realDirection j) (-imagDirection j) (fun y => ((u y - v y : ℝ) : ℂ))) x =
      dz (realDirection i) (imagDirection i)
        (dz (realDirection j) (-imagDirection j) (fun y => (u y : ℂ))) x -
      dz (realDirection i) (imagDirection i)
        (dz (realDirection j) (-imagDirection j) (fun y => (v y : ℂ))) x
  simp only [Complex.ofReal_sub]
  exact LogDetAux.dz_dz_sub_at huC hvC _ _ _ _

theorem complexLaplacian_sub_at {n : ℕ} (u : E n → ℝ) {f h : E n → ℝ} {x : E n}
    (hf : ContDiffAt ℝ ∞ f x) (hh : ContDiffAt ℝ ∞ h x) :
    complexLaplacian u (fun y => f y - h y) x =
      complexLaplacian u f x - complexLaplacian u h x := by
  rw [complexLaplacian_eq_trace, complexHessian_sub_at hf hh, Matrix.mul_sub,
    Matrix.trace_sub, Complex.sub_re, complexLaplacian_eq_trace, complexLaplacian_eq_trace]

theorem IsSolution.logdet {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    Real.log (complexHessian u x).det.re = Real.log μ - u x := by
  rw [hu.2.2.2.1 x hx]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Real.log_mul (ne_of_gt hu.1) (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- The tangent inequality applied to two actual solutions of the same PDE. -/
theorem IsSolution.linearized_difference {n : ℕ} {μ : ℝ} {u v : E n → ℝ}
    (hu : IsSolution n μ u) (hv : IsSolution n μ v) {x : E n} (hx : x ∈ unitBall n) :
    -(u x - v x) ≤ complexLaplacian v (fun y => u y - v y) x := by
  have hxclosed : x ∈ closedUnitBall n := Metric.ball_subset_closedBall hx
  have huAt : ContDiffAt ℝ ∞ u x := hu.2.1.contDiffAt hxclosed
  have hvAt : ContDiffAt ℝ ∞ v x := hv.2.1.contDiffAt hxclosed
  have h := posDef_logdet_tangent (hv.2.2.1 x hx) (hu.2.2.1 x hx)
  rw [hu.logdet hx, hv.logdet hx] at h
  rw [complexLaplacian_eq_trace, complexHessian_sub_at huAt hvAt]
  linarith

theorem IsSolution.radial_linearized_difference {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {b : ℝ} (hb : 0 < b) (hμ : μ = radialCoefficient n b)
    {x : E n} (hx : x ∈ unitBall n) :
    -(u x - radialPotential n b x) ≤
      complexLaplacian (radialPotential n b) (fun y => u y - radialPotential n b y) x := by
  have hv : IsSolution n μ (radialPotential n b) := by
    simpa only [← hμ] using radial_isSolution n hb
  exact hu.linearized_difference hv hx

end KEBall
