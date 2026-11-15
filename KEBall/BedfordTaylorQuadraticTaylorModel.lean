import PshLines.FirstPass.MongeAmpere
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Hessians of the quadratic models of a twice differentiable potential
-/

set_option autoImplicit false

open scoped ContDiff

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector complexHessian smoothDensity)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quadratic Taylor model with a prescribed center, value, gradient,
and second derivative. -/
noncomputable def quadraticTaylorModel (x : E) (c : ℝ) (L : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (y : E) : ℝ :=
  c + L (y - x) + A (y - x) (y - x) / 2

theorem contDiff_quadraticTaylorModel (x : E) (c : ℝ) (L : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) : ContDiff ℝ ∞ (quadraticTaylorModel x c L A) := by
  let h (y : E) := y - x
  have hh : ContDiff ℝ ∞ h := contDiff_id.sub contDiff_const
  exact (contDiff_const.add (L.contDiff.comp hh)).add
    (((A.contDiff.comp hh).clm_apply hh).div_const 2)

private theorem realHessian_bilinear_diag (A : E →L[ℝ] E →L[ℝ] ℝ) (y v w : E) :
    PshLines.realHessian (fun z => A z z) y v w = A v w + A w v := by
  have h : fderiv ℝ (fun z => A z z) = fun z => A.flip z + A z := by
    funext z
    have hD := (A.hasFDerivAt (x := z)).clm_apply (hasFDerivAt_id z)
    simpa only [id_eq, ContinuousLinearMap.comp_id, add_comm] using hD.fderiv
  rw [PshLines.realHessian_eq_fderiv, h]
  have hD : HasFDerivAt (fun z => A.flip z + A z) (A.flip + A) y :=
    A.flip.hasFDerivAt.add A.hasFDerivAt
  rw [hD.fderiv]
  simp only [add_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem realHessian_quadraticTaylorModel (x : E) (c : ℝ) (L : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (y v w : E) :
    PshLines.realHessian (quadraticTaylorModel x c L A) y v w = (A v w + A w v) / 2 := by
  let p (z : E) := c + L z + A z z / 2
  let B := ContinuousLinearMap.id ℝ E
  have hA : ContDiff ℝ 2 (fun z => A z z) := A.contDiff.clm_apply contDiff_id
  have hL : ContDiff ℝ 2 (fun z => c + L z) := contDiff_const.add L.contDiff
  have hp : ContDiff ℝ 2 p := hL.add (hA.div_const 2)
  have he : quadraticTaylorModel x c L A = fun z => p (-x + B z) := by
    funext z
    simp only [quadraticTaylorModel, p, B, ContinuousLinearMap.id_apply, neg_add_eq_sub]
  rw [he, PshLines.realHessian_comp_affine hp B (-x)]
  have hpEq : p = (fun z => c + L z) + (1 / 2 : ℝ) • (fun z => A z z) := by
    funext z
    simp only [p, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, one_mul, mul_comm]
  simp only [B, ContinuousLinearMap.id_apply, hpEq]
  have hAs : ContDiffAt ℝ 2 ((1 / 2 : ℝ) • (fun z => A z z)) (-x + y) :=
    (hA.const_smul (1 / 2 : ℝ)).contDiffAt
  rw [PshLines.realHessian_add hL.contDiffAt hAs,
    PshLines.realHessian_smul hA.contDiffAt, realHessian_bilinear_diag]
  have hzero : PshLines.realHessian (fun z => c + L z) (-x + y) v w = 0 := by
    have hD : fderiv ℝ (fun z => c + L z) = fun _ => L := by
      funext z
      exact (L.hasFDerivAt.const_add c).fderiv
    have hDD : fderiv ℝ (fun _ : E => L) (-x + y) = 0 :=
      (hasFDerivAt_const L (-x + y)).fderiv
    rw [PshLines.realHessian_eq_fderiv, hD, hDD, zero_apply, zero_apply]
  rw [hzero]
  ring

variable {n : ℕ}

/-- The complex Hessian convention applied to a real bilinear form. -/
noncomputable def complexHessianOfBilinear
    (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) : Matrix (Fin n) (Fin n) ℂ := fun j k =>
  ((A (coordinateVector j) (coordinateVector k) +
      A (Complex.I • coordinateVector j) (Complex.I • coordinateVector k) : ℝ) : ℂ) / 4 +
    Complex.I * ((A (coordinateVector j) (Complex.I • coordinateVector k) -
      A (Complex.I • coordinateVector j) (coordinateVector k) : ℝ) : ℂ) / 4

theorem complexHessian_eq_ofBilinear (u : ComplexModel n → ℝ) (x : ComplexModel n) :
    complexHessian u x = complexHessianOfBilinear (fderiv ℝ (fderiv ℝ u) x) := by
  funext j k
  simp only [complexHessian, complexHessianOfBilinear, PshLines.realHessian_eq_fderiv]

theorem complexHessian_quadraticTaylorModel (x : ComplexModel n) (c : ℝ)
    (L : ComplexModel n →L[ℝ] ℝ) (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (y : ComplexModel n) :
    complexHessian (quadraticTaylorModel x c L A) y =
      complexHessianOfBilinear ((1 / 2 : ℝ) • (A + A.flip)) := by
  funext j k
  simp only [complexHessian, complexHessianOfBilinear, realHessian_quadraticTaylorModel,
    smul_apply, add_apply, ContinuousLinearMap.flip_apply,
    smul_eq_mul, div_eq_mul_inv, one_mul, mul_comm]

theorem continuous_complexHessianOfBilinear :
    Continuous (complexHessianOfBilinear (n := n)) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro k
  unfold complexHessianOfBilinear
  have h (v w : ComplexModel n) : Continuous (fun A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ => A v w) :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp (ContinuousLinearMap.apply ℝ _ v).continuous
  fun_prop

end KEBall.BedfordTaylor
