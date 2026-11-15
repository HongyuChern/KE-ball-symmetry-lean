import KEBall.ComplexMaximum
import KEBall.EquationBasics

/-!
# The actual exponential weight in the P-function

UNCOMPILED DRAFT: the current environment has no Lean runtime. This file is
not imported into a production target and must pass the pinned Stage04
compiler before any declaration below is counted as formally verified.

The formulas start with the real Frechet derivative and the concrete
Wirtinger operators. Smoothness is local at the point under consideration.
No differentiated identity is accepted as an additional hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped ContDiff Topology BigOperators

namespace KEBall
open KEBallProbe

namespace AuxiliaryPDifferential

/-- Real chain rule with the numerical coefficient exposed. -/
theorem fderiv_exp_const_mul_apply {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (c : ℝ) (v : E n) :
    fderiv ℝ (fun y => Real.exp (c * u y)) x v =
      Real.exp (c * u x) * c * fderiv ℝ u x v := by
  have hd := (hu.hasFDerivAt.const_mul c).exp
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The exponential chain rule for any constant Wirtinger pair. -/
theorem dz_ofReal_exp_const_mul {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (c : ℝ) (a b : E n) :
    dz a b (fun y => (Real.exp (c * u y) : ℂ)) x =
      (c : ℂ) * (Real.exp (c * u x) : ℂ) *
        dz a b (fun y => (u y : ℂ)) x := by
  have hd : DifferentiableAt ℝ (fun y => Real.exp (c * u y)) x :=
    ((hu.hasFDerivAt.const_mul c).exp).differentiableAt
  simp only [dz, rd_ofReal hd, rd_ofReal hu,
    fderiv_exp_const_mul_apply hu]
  push_cast
  ring

/-- A local second chain rule. The first-derivative formula is used on a
neighbourhood before differentiating it; no pointwise substitution is made
under a derivative. -/
theorem dz_dz_ofReal_exp_const_mul {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (r : ℝ) (a b c d : E n) :
    dz a b (dz c d (fun y => (Real.exp (r * u y) : ℂ))) x =
      (Real.exp (r * u x) : ℂ) *
        ((r : ℂ) * dz a b (dz c d (fun y => (u y : ℂ))) x +
          (r : ℂ) ^ 2 * dz a b (fun y => (u y : ℂ)) x *
            dz c d (fun y => (u y : ℂ)) x) := by
  have huC : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have hE : ContDiffAt ℝ ∞ (fun y => (Real.exp (r * u y) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_const.mul hu).exp
  have hinner : dz c d (fun y => (Real.exp (r * u y) : ℂ)) =ᶠ[𝓝 x]
      (fun y => (r : ℂ) *
        ((Real.exp (r * u y) : ℂ) * dz c d (fun z => (u z : ℂ)) y)) := by
    filter_upwards [(hu.of_le (m := 1) (by simp)).eventually (by simp)] with y hy
    rw [dz_ofReal_exp_const_mul (hy.differentiableAt (by simp))]
    ring
  rw [LogDetAux.dz_congr_of_eventuallyEq hinner]
  change dz a b (fun y => (r : ℂ) *
    (((fun y => (Real.exp (r * u y) : ℂ)) *
      dz c d (fun y => (u y : ℂ))) y)) x = _
  rw [ComplexMaximumAux.dz_const_mul_differentiableAt
    ((hE.differentiableAt (by simp)).mul
      ((smoothAt_dz huC c d).differentiableAt (by simp)))]
  change (r : ℂ) * dz a b (fun y =>
    (Real.exp (r * u y) : ℂ) * dz c d (fun y => (u y : ℂ)) y) x = _
  rw [dz_mul_differentiableAt (hE.differentiableAt (by simp))
    ((smoothAt_dz huC c d).differentiableAt (by simp))]
  rw [dz_ofReal_exp_const_mul (hu.differentiableAt (by simp))]
  ring

/-- The actual complex Hessian of an exponential of the potential. -/
theorem complexHessian_exp_const_mul_entry {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (c : ℝ) (i j : Fin n) :
    complexHessian (fun y => Real.exp (c * u y)) x i j =
      (Real.exp (c * u x) : ℂ) *
        ((c : ℂ) * complexHessian u x i j +
          (c : ℂ) ^ 2 * partialZ i (fun y => (u y : ℂ)) x *
            partialBar j (fun y => (u y : ℂ)) x) := by
  exact dz_dz_ofReal_exp_const_mul hu c
    (realDirection i) (imagDirection i) (realDirection j) (-imagDirection j)

/-- Contraction uses the concrete inverse-Hessian coefficients. This identity
needs no PDE and no determinant hypothesis. -/
theorem complexLaplacian_exp_const_mul {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (c : ℝ) :
    complexLaplacian u (fun y => Real.exp (c * u y)) x =
      Real.exp (c * u x) *
        (c * complexLaplacian u u x + c ^ 2 * gradientNormSq u x) := by
  have hsum : (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
      complexHessian (fun y => Real.exp (c * u y)) x i j) =
      ((Real.exp (c * u x) * c : ℝ) : ℂ) *
        (∑ i : Fin n, ∑ j : Fin n,
          inverseCoefficient u x i j * complexHessian u x i j) +
      ((Real.exp (c * u x) * c ^ 2 : ℝ) : ℂ) *
        (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
          partialZ i (fun y => (u y : ℂ)) x *
          partialBar j (fun y => (u y : ℂ)) x) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n,
          (((Real.exp (c * u x) * c : ℝ) : ℂ) *
              (inverseCoefficient u x i j * complexHessian u x i j) +
            ((Real.exp (c * u x) * c ^ 2 : ℝ) : ℂ) *
              (inverseCoefficient u x i j *
                partialZ i (fun y => (u y : ℂ)) x *
                partialBar j (fun y => (u y : ℂ)) x)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [complexHessian_exp_const_mul_entry hu]
        push_cast
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold complexLaplacian gradientNormSq
  rw [hsum]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Identification with the exact frozen definition of the weight. -/
theorem expWeight_eq_exp_const_mul {n : ℕ} (u : E n → ℝ) :
    expWeight u = fun y => Real.exp (-((n + 1 : ℝ)⁻¹) * u y) := by
  funext y
  unfold expWeight
  congr 1
  ring

end AuxiliaryPDifferential

/-- Local smoothness of the actual weight. -/
theorem contDiffAt_expWeight {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) : ContDiffAt ℝ ∞ (expWeight u) x := by
  exact (hu.neg.div_const (n + 1 : ℝ)).exp

/-- The first derivative of the exact exponential weight. -/
theorem partialZ_expWeight {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    partialZ i (fun y => (expWeight u y : ℂ)) x =
      -((expWeight u x : ℂ) / (n + 1 : ℂ)) *
        partialZ i (fun y => (u y : ℂ)) x := by
  simp only [AuxiliaryPDifferential.expWeight_eq_exp_const_mul, partialZ]
  rw [AuxiliaryPDifferential.dz_ofReal_exp_const_mul hu]
  push_cast
  ring

/-- The conjugate Wirtinger derivative is calculated by the same real
chain rule, independently of a Hermitian-metric convention. -/
theorem partialBar_expWeight {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    partialBar i (fun y => (expWeight u y : ℂ)) x =
      -((expWeight u x : ℂ) / (n + 1 : ℂ)) *
        partialBar i (fun y => (u y : ℂ)) x := by
  simp only [AuxiliaryPDifferential.expWeight_eq_exp_const_mul, partialBar]
  rw [AuxiliaryPDifferential.dz_ofReal_exp_const_mul hu]
  push_cast
  ring

/-- The differential identity for E, derived from local smoothness and the
inverse-Hessian trace identity, before using the KE equation. -/
theorem complexLaplacian_expWeight {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x)
    (hdet : IsUnit (complexHessian u x).det) :
    complexLaplacian u (expWeight u) x =
      expWeight u x * (-(n : ℝ) / (n + 1 : ℝ) +
        gradientNormSq u x / (n + 1 : ℝ) ^ 2) := by
  simp only [AuxiliaryPDifferential.expWeight_eq_exp_const_mul]
  rw [AuxiliaryPDifferential.complexLaplacian_exp_const_mul hu,
    complexLaplacian_self_of_isUnit hdet]
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hk]

/-- Every original solution satisfies the exact exponential-weight identity
on the whole closed ball; nonsingularity there was proved from the original
PDE and continuity in Stage04. -/
theorem IsSolution.complexLaplacian_expWeight {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) :
    complexLaplacian u (expWeight u) x =
      expWeight u x * (-(n : ℝ) / (n + 1 : ℝ) +
        gradientNormSq u x / (n + 1 : ℝ) ^ 2) := by
  exact KEBall.complexLaplacian_expWeight (hu.2.1.contDiffAt hx)
    (hu.det_isUnit_closedBall hx)

end KEBall
