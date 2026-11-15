import KEBall.DirichletUniformEllipticity
import KEBall.DirichletPoincare
import KEBall.MoserTrudingerSmoothGreen
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Energy of the linearized Dirichlet operator

The cofactor field converts the principal symbol into an energy
density. Green's identity and the ball Poincaré inequality give the
coercivity estimate for smooth zero-boundary variations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Gradient Matrix

namespace KEBall

/-- A positive definite matrix has adjugate equal to determinant times inverse. -/
theorem adjugate_eq_det_smul_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) : A.adjugate = A.det • A⁻¹ := by
  have h := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [A.nonsing_inv_apply h, smul_smul, h.mul_val_inv, one_smul]

/-- In interleaved coordinates the Wirtinger derivative is half the
conjugate of the real gradient. -/
theorem partialZ_eq_half_star_gradient {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) :
    (fun i => partialZ i (fun y => (h y : ℂ)) x) =
      (2 : ℂ)⁻¹ • star (complexCoord (∇ h x)) := by
  funext i
  have hg (w : E n) : fderiv ℝ h x w = inner ℝ (∇ h x) w := by
    exact (congrArg (fun T : E n →L[ℝ] ℝ => T w)
      (toDual_gradient (𝕜 := ℝ) (f := h) (x := x))).symm
  rw [partialZ_ofReal hh, hg, hg]
  simp only [Pi.star_apply, complexCoord, realDirection, imagDirection,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, Pi.smul_apply, smul_eq_mul,
    Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The energy density of the cofactor field is twice the determinant
times the linearized principal symbol evaluated on the gradient. -/
theorem cofactor_gradient_pairing_eq_principal_symbol {n : ℕ}
    {u h : E n → ℝ} {x : E n} (hA : (complexHessian u x).PosDef)
    (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ h x (cofactorRealField u h x) =
      2 * (complexHessian u x).det.re *
        complexLaplacian u (fun y => (inner ℝ (∇ h x) y) ^ 2 / 2) x := by
  let A := complexHessian u x
  let p : Fin n → ℂ := fun i => partialZ i (fun y => (h y : ℂ)) x
  let z := star (complexCoord (∇ h x))
  have hp : p = (2 : ℂ)⁻¹ • z := partialZ_eq_half_star_gradient hh
  have he :
      (∑ i : Fin n, p i * complexCoord (cofactorRealField u h x) i) =
        star p ⬝ᵥ (A.adjugate *ᵥ p) := by
    simp only [cofactorRealField, complexCoord_complexVectorReal, cofactorVectorField,
      partialBar_ofReal hh, Finset.mul_sum, dotProduct, Matrix.mulVec, p, A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hQ : star p ⬝ᵥ (A.adjugate *ᵥ p) =
      (A.det / 4) * (star z ⬝ᵥ (A⁻¹ *ᵥ z)) := by
    rw [hp, adjugate_eq_det_smul_inv hA, star_smul, Matrix.smul_mulVec, Matrix.mulVec_smul,
      smul_dotProduct, dotProduct_smul, dotProduct_smul]
    have ht : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
      change (starRingEnd ℂ) ((2 : ℂ)⁻¹) = _
      simp [starRingEnd_apply]
    rw [ht]
    simp only [smul_eq_mul]
    change (2 : ℂ)⁻¹ * (A.det * ((2 : ℂ)⁻¹ * (star z ⬝ᵥ (A⁻¹ *ᵥ z)))) = _
    ring
  rw [fderiv_eq_wirtinger hh]
  change 2 * (∑ i : Fin n, p i * complexCoord (cofactorRealField u h x) i).re = _
  rw [he, hQ, complexLaplacian_rankOne_quadratic]
  change 2 * ((A.det / 4) * (star z ⬝ᵥ (A⁻¹ *ᵥ z))).re =
    2 * A.det.re * ((star z ⬝ᵥ (A⁻¹ *ᵥ z)).re / 4)
  rw [posDef_det_eq_ofReal_re hA, ← Complex.ofReal_ofNat (n := 4), ← Complex.ofReal_div]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The determinant linearization is the log-determinant linearization
multiplied by the positive density. -/
theorem cofactorContraction_eq_det_mul_complexLaplacian {n : ℕ}
    {u h : E n → ℝ} {x : E n} (hA : (complexHessian u x).PosDef) :
    MoserTrudinger.cofactorContraction u h x =
      (complexHessian u x).det.re * complexLaplacian u h x := by
  let A := complexHessian u x
  have he : MoserTrudinger.cofactorContraction u h x =
      (A.adjugate * complexHessian h x).trace.re := by
    unfold MoserTrudinger.cofactorContraction
    congr 1
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Finset.sum_comm
  rw [he, adjugate_eq_det_smul_inv hA, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    posDef_det_eq_ofReal_re hA, complexLaplacian_eq_trace]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The negative determinant linearization controls the Dirichlet energy
and the squared (L^2) norm of each smooth zero-boundary variation. -/
theorem linearizedDet_energy_coercive {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {u h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hh0 : ∀ x ∈ unitSphere n, h x = 0)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    let energy := -(∫ x in unitBall n, h x * MoserTrudinger.cofactorContraction u h x ∂volume0 n)
    (a * l) * (∫ x in unitBall n, ‖fderiv ℝ h x‖ ^ 2 ∂volume0 n) ≤ energy ∧
      (a * l) * ((n : ℝ) ^ 2 * (∫ x in unitBall n, (h x) ^ 2 ∂volume0 n)) ≤ energy := by
  let P : E n → ℝ := fun x => fderiv ℝ h x (cofactorRealField u h x)
  let g : E n → ℝ := fun x => ‖fderiv ℝ h x‖ ^ 2
  have hD := (hh.fderiv_of_isOpen hU (by simp) (m := 0)).continuousOn
  have hP : ContinuousOn P U := hD.clm_apply
    (cofactorRealField_contDiffOn hU hu hh).continuousOn
  have hg : ContinuousOn g U := hD.norm.pow 2
  have hInt (r : E n → ℝ) (hr : ContinuousOn r U) :
      IntegrableOn r (unitBall n) (volume0 n) :=
    (hr.mono hSub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hPoint (x : E n) (hx : x ∈ unitBall n) : (2 * (a * l)) * g x ≤ P x := by
    have hAt := (hh.contDiffAt (hU.mem_nhds (hSub (ball_subset_closedBall hx)))).differentiableAt
      (by simp)
    have hN : ‖∇ h x‖ = ‖fderiv ℝ h x‖ := by
      rw [← toDual_gradient]
      exact ((InnerProductSpace.toDual ℝ (E n)).norm_map (∇ h x)).symm
    have hSym := hElliptic x hx (∇ h x)
    rw [hN] at hSym
    change (2 * (a * l)) * ‖fderiv ℝ h x‖ ^ 2 ≤ fderiv ℝ h x (cofactorRealField u h x)
    rw [cofactor_gradient_pairing_eq_principal_symbol (huP x hx) hAt]
    calc
      _ = (2 * a) * (l * ‖fderiv ℝ h x‖ ^ 2) := by ring
      _ ≤ (2 * (complexHessian u x).det.re) * (l * ‖fderiv ℝ h x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hDensity x hx) (by norm_num))
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hSym
        (mul_nonneg (by norm_num) (posDef_det_re_pos (huP x hx)).le)
  have hMono := setIntegral_mono_on ((hInt g hg).const_mul (2 * (a * l))) (hInt P hP)
    measurableSet_ball hPoint
  rw [integral_const_mul] at hMono
  rw [MoserTrudinger.integral_mul_cofactorContraction_eq_neg_half_pairing hn hU hSub hu hh huP hh0]
  change (a * l) * (∫ x in unitBall n, g x ∂volume0 n) ≤
      -(-(∫ x in unitBall n, P x ∂volume0 n) / 2) ∧
    (a * l) * ((n : ℝ) ^ 2 * (∫ x in unitBall n, (h x) ^ 2 ∂volume0 n)) ≤
      -(-(∫ x in unitBall n, P x ∂volume0 n) / 2)
  have hGrad : (a * l) * (∫ x in unitBall n, g x ∂volume0 n) ≤
      -(-(∫ x in unitBall n, P x ∂volume0 n) / 2) := by linarith only [hMono]
  exact ⟨hGrad, (mul_le_mul_of_nonneg_left
    (dirichlet_poincare_sq hn ⟨U, hU, hSub, hh⟩ hh0) (mul_nonneg ha.le hl.le)).trans hGrad⟩

end KEBall
