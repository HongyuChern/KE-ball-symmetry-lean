import Drafts.KEBall.AuxiliaryPDifferential
import KEBall.SecondGreen

/-!
# Product and logarithm rules for the actual complex Laplacian

UNCOMPILED DRAFT. No declaration in this file is counted as kernel verified.
The operators, metric coefficients and all derivatives are the frozen ones
in `KEBall.Domain`. The metric need not be positive definite for these
identities; positivity is needed only when using the quadratic form as a norm.

The logarithm identities are obtained by reversing the exponential chain
rule on the positive germ of the function. Every substitution inside a
second derivative is justified by a neighbourhood equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped ContDiff Topology BigOperators

namespace KEBall
open KEBallProbe

/-- The real contraction of the actual two differentials, using the inverse
Hessian of `u` and the manuscript's transposed inverse convention. -/
noncomputable def gradientPairing {n : ℕ} (u h k : E n → ℝ) (x : E n) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
    partialZ i (fun y => (h y : ℂ)) x *
    partialBar j (fun y => (k y : ℂ)) x).re

/-- Squared differential norm of a separate test function in the metric of
the potential. It agrees definitionally with the original `q` when `h = u`. -/
noncomputable def metricGradientNormSq {n : ℕ} (u h : E n → ℝ) (x : E n) : ℝ :=
  gradientPairing u h h x

theorem metricGradientNormSq_self {n : ℕ} (u : E n → ℝ) (x : E n) :
    metricGradientNormSq u u x = gradientNormSq u x := rfl

namespace ComplexProductLogAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem dz_add_differentiableAt {f g : X → ℂ} {x : X}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a b : X) :
    dz a b (fun y => f y + g y) x = dz a b f x + dz a b g x := by
  unfold dz rd
  rw [fderiv_fun_add hf hg]
  simp only [_root_.add_apply]
  ring

theorem dz_dz_mul_at {f g : X → ℂ} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (a b c d : X) :
    dz a b (dz c d (fun y => f y * g y)) x =
      f x * dz a b (dz c d g) x + g x * dz a b (dz c d f) x +
      dz a b f x * dz c d g x + dz a b g x * dz c d f x := by
  have hinner : dz c d (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => dz c d f y * g y + f y * dz c d g y) := by
    filter_upwards [(hf.of_le (m := 1) (by simp)).eventually (by simp),
      (hg.of_le (m := 1) (by simp)).eventually (by simp)] with y hyf hyg
    exact dz_mul_differentiableAt (hyf.differentiableAt (by simp))
      (hyg.differentiableAt (by simp)) c d
  rw [LogDetAux.dz_congr_of_eventuallyEq hinner]
  have hfirst : DifferentiableAt ℝ (fun y => dz c d f y * g y) x :=
    ((smoothAt_dz hf c d).differentiableAt (by simp)).mul
      (hg.differentiableAt (by simp))
  have hsecond : DifferentiableAt ℝ (fun y => f y * dz c d g y) x :=
    (hf.differentiableAt (by simp)).mul
      ((smoothAt_dz hg c d).differentiableAt (by simp))
  rw [dz_add_differentiableAt hfirst hsecond]
  rw [dz_mul_differentiableAt ((smoothAt_dz hf c d).differentiableAt (by simp))
    (hg.differentiableAt (by simp)),
    dz_mul_differentiableAt (hf.differentiableAt (by simp))
      ((smoothAt_dz hg c d).differentiableAt (by simp))]
  ring

/-- Germ equality remains valid after two actual Wirtinger derivatives. -/
theorem dz_dz_congr_of_eventuallyEq {f g : X → ℂ} {x : X}
    (heq : f =ᶠ[𝓝 x] g) (a b c d : X) :
    dz a b (dz c d f) x = dz a b (dz c d g) x := by
  have hinner : dz c d f =ᶠ[𝓝 x] dz c d g := by
    filter_upwards [heq.eventually_nhds] with y hy
    exact LogDetAux.dz_congr_of_eventuallyEq hy c d
  exact LogDetAux.dz_congr_of_eventuallyEq hinner a b

theorem ofReal_eq_exp_log_germ {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContinuousAt h x) (hx : 0 < h x) :
    (fun y => (h y : ℂ)) =ᶠ[𝓝 x]
      (fun y => (Real.exp (Real.log (h y)) : ℂ)) := by
  have hpos : ∀ᶠ y in 𝓝 x, 0 < h y :=
    hh.eventually (Ioi_mem_nhds hx)
  filter_upwards [hpos] with y hy
  rw [Real.exp_log hy]

/-- First logarithm rule, obtained from the actual exponential derivative. -/
theorem dz_ofReal_log {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (hx : 0 < h x) (a b : E n) :
    dz a b (fun y => (Real.log (h y) : ℂ)) x =
      dz a b (fun y => (h y : ℂ)) x / (h x : ℂ) := by
  have hlog : ContDiffAt ℝ ∞ (fun y => Real.log (h y)) x :=
    hh.log (ne_of_gt hx)
  have heq := ofReal_eq_exp_log_germ hh.continuousAt hx
  have hder : dz a b (fun y => (h y : ℂ)) x =
      (h x : ℂ) * dz a b (fun y => (Real.log (h y) : ℂ)) x := by
    calc
      _ = dz a b (fun y => (Real.exp (Real.log (h y)) : ℂ)) x :=
        LogDetAux.dz_congr_of_eventuallyEq heq a b
      _ = _ := by
        simpa only [one_mul, Complex.ofReal_one, Real.exp_log hx] using
          AuxiliaryPDifferential.dz_ofReal_exp_const_mul
            (hlog.differentiableAt (by simp)) 1 a b
  have hxc : (h x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  apply (eq_div_iff hxc).2
  calc
    _ = (h x : ℂ) * dz a b (fun y => (Real.log (h y) : ℂ)) x := mul_comm _ _
    _ = _ := hder.symm

/-- Second logarithm rule. The exp-log substitution is made on a
neighbourhood before applying both derivatives. -/
theorem dz_dz_ofReal_log {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (hx : 0 < h x) (a b c d : E n) :
    dz a b (dz c d (fun y => (Real.log (h y) : ℂ))) x =
      dz a b (dz c d (fun y => (h y : ℂ))) x / (h x : ℂ) -
      dz a b (fun y => (h y : ℂ)) x *
        dz c d (fun y => (h y : ℂ)) x / (h x : ℂ) ^ 2 := by
  have hlog : ContDiffAt ℝ ∞ (fun y => Real.log (h y)) x :=
    hh.log (ne_of_gt hx)
  have hxc : (h x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hsecond : dz a b (dz c d (fun y => (h y : ℂ))) x =
      (h x : ℂ) *
        (dz a b (dz c d (fun y => (Real.log (h y) : ℂ))) x +
          dz a b (fun y => (Real.log (h y) : ℂ)) x *
            dz c d (fun y => (Real.log (h y) : ℂ)) x) := by
    calc
      _ = dz a b (dz c d (fun y => (Real.exp (Real.log (h y)) : ℂ))) x :=
        dz_dz_congr_of_eventuallyEq (ofReal_eq_exp_log_germ hh.continuousAt hx)
          a b c d
      _ = _ := by
        simpa only [one_mul, Complex.ofReal_one, one_pow, Real.exp_log hx] using
          AuxiliaryPDifferential.dz_dz_ofReal_exp_const_mul hlog 1 a b c d
  rw [dz_ofReal_log hh hx a b, dz_ofReal_log hh hx c d] at hsecond
  calc
    _ = dz a b (dz c d (fun y => (h y : ℂ))) x / (h x : ℂ) -
        (dz a b (fun y => (h y : ℂ)) x / (h x : ℂ)) *
          (dz c d (fun y => (h y : ℂ)) x / (h x : ℂ)) := by
      apply (eq_sub_iff_add_eq).2
      apply (eq_div_iff hxc).2
      calc
        _ = (h x : ℂ) *
          (dz a b (dz c d (fun y => (Real.log (h y) : ℂ))) x +
            (dz a b (fun y => (h y : ℂ)) x / (h x : ℂ)) *
              (dz c d (fun y => (h y : ℂ)) x / (h x : ℂ))) := mul_comm _ _
        _ = _ := hsecond.symm
    _ = _ := by field_simp [hxc] <;> ring

end ComplexProductLogAux

theorem partialZ_ofReal_mul {n : ℕ} {h k : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (hk : DifferentiableAt ℝ k x) (i : Fin n) :
    partialZ i (fun y => ((h y * k y : ℝ) : ℂ)) x =
      partialZ i (fun y => (h y : ℂ)) x * (k x : ℂ) +
        (h x : ℂ) * partialZ i (fun y => (k y : ℂ)) x := by
  have hhC : DifferentiableAt ℝ (fun y => (h y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hh
  have hkC : DifferentiableAt ℝ (fun y => (k y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hk
  simpa only [partialZ, Complex.ofReal_mul] using
    dz_mul_differentiableAt hhC hkC (realDirection i) (imagDirection i)

theorem partialZ_const_add_const_mul {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (a b : ℝ) (i : Fin n) :
    partialZ i (fun y => ((a + b * h y : ℝ) : ℂ)) x =
      (b : ℂ) * partialZ i (fun y => (h y : ℂ)) x := by
  have hhC : DifferentiableAt ℝ (fun y => (h y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hh
  simp only [partialZ, Complex.ofReal_add, Complex.ofReal_mul]
  have hmul : DifferentiableAt ℝ (fun y => (b : ℂ) * (h y : ℂ)) x :=
    hhC.const_mul (b : ℂ)
  rw [ComplexProductLogAux.dz_add_differentiableAt
    (differentiableAt_const (a : ℂ)) hmul]
  rw [ComplexMaximumAux.dz_const_mul_differentiableAt hhC]
  simp [dz, rd]

theorem partialBar_const_add_const_mul {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (a b : ℝ) (i : Fin n) :
    partialBar i (fun y => ((a + b * h y : ℝ) : ℂ)) x =
      (b : ℂ) * partialBar i (fun y => (h y : ℂ)) x := by
  have hhC : DifferentiableAt ℝ (fun y => (h y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hh
  simp only [partialBar, Complex.ofReal_add, Complex.ofReal_mul]
  have hmul : DifferentiableAt ℝ (fun y => (b : ℂ) * (h y : ℂ)) x :=
    hhC.const_mul (b : ℂ)
  rw [ComplexProductLogAux.dz_add_differentiableAt
    (differentiableAt_const (a : ℂ)) hmul]
  rw [ComplexMaximumAux.dz_const_mul_differentiableAt hhC]
  simp [dz, rd]

theorem gradientPairing_symm {n : ℕ} {u h k : E n → ℝ} {x : E n}
    (hH : (complexHessian u x).IsHermitian)
    (hh : DifferentiableAt ℝ h x) (hk : DifferentiableAt ℝ k x) :
    gradientPairing u h k x = gradientPairing u k h x := by
  unfold gradientPairing inverseCoefficient
  simp_rw [partialBar_ofReal hh, partialBar_ofReal hk]
  exact hermitian_contraction_re_symm hH.inv
    (fun i => partialZ i (fun y => (h y : ℂ)) x)
    (fun i => partialZ i (fun y => (k y : ℂ)) x)

theorem gradientPairing_const_add_const_mul_left {n : ℕ} (u k : E n → ℝ)
    {h : E n → ℝ} {x : E n} (hh : DifferentiableAt ℝ h x) (a b : ℝ) :
    gradientPairing u (fun y => a + b * h y) k x = b * gradientPairing u h k x := by
  unfold gradientPairing
  simp_rw [partialZ_const_add_const_mul hh]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
      ((b : ℂ) * partialZ i (fun y => (h y : ℂ)) x) *
        partialBar j (fun y => (k y : ℂ)) x) =
      (b : ℂ) * (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        partialZ i (fun y => (h y : ℂ)) x * partialBar j (fun y => (k y : ℂ)) x) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem gradientPairing_const_add_const_mul_right {n : ℕ} (u h : E n → ℝ)
    {k : E n → ℝ} {x : E n} (hk : DifferentiableAt ℝ k x) (a b : ℝ) :
    gradientPairing u h (fun y => a + b * k y) x = b * gradientPairing u h k x := by
  unfold gradientPairing
  simp_rw [partialBar_const_add_const_mul hk]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
      partialZ i (fun y => (h y : ℂ)) x *
        ((b : ℂ) * partialBar j (fun y => (k y : ℂ)) x)) =
      (b : ℂ) * (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        partialZ i (fun y => (h y : ℂ)) x * partialBar j (fun y => (k y : ℂ)) x) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- An affine function of a test function contributes no zeroth-order term. -/
theorem complexLaplacian_const_add_const_mul {n : ℕ} (u : E n → ℝ)
    {h : E n → ℝ} {x : E n} (hh : ContDiffAt ℝ ∞ h x) (a b : ℝ) :
    complexLaplacian u (fun y => a + b * h y) x =
      b * complexLaplacian u h x := by
  have heq : (fun y => a + b * h y) =
      (fun y => a - (-b) * h y) := by funext y; ring
  rw [heq, complexLaplacian_sub_at u contDiffAt_const (contDiffAt_const.mul hh),
    complexLaplacian_const, complexLaplacian_const_mul_at u hh]
  ring

theorem complexHessian_mul_entry {n : ℕ} {h k : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (hk : ContDiffAt ℝ ∞ k x) (i j : Fin n) :
    complexHessian (fun y => h y * k y) x i j =
      (h x : ℂ) * complexHessian k x i j +
      (k x : ℂ) * complexHessian h x i j +
      partialZ i (fun y => (h y : ℂ)) x * partialBar j (fun y => (k y : ℂ)) x +
      partialZ i (fun y => (k y : ℂ)) x * partialBar j (fun y => (h y : ℂ)) x := by
  have hhC : ContDiffAt ℝ ∞ (fun y => (h y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hh
  have hkC : ContDiffAt ℝ ∞ (fun y => (k y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hk
  simpa only [complexHessian, partialZ, partialBar, Complex.ofReal_mul] using
    ComplexProductLogAux.dz_dz_mul_at hhC hkC
      (realDirection i) (imagDirection i) (realDirection j) (-imagDirection j)

/-- Product rule without any symmetry or positivity assumption on the
coefficient matrix. When the metric is Hermitian the two pairings agree. -/
theorem complexLaplacian_mul {n : ℕ} (u : E n → ℝ) {h k : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (hk : ContDiffAt ℝ ∞ k x) :
    complexLaplacian u (fun y => h y * k y) x =
      h x * complexLaplacian u k x + k x * complexLaplacian u h x +
      gradientPairing u h k x + gradientPairing u k h x := by
  have hsum : (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
      complexHessian (fun y => h y * k y) x i j) =
      (h x : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
        inverseCoefficient u x i j * complexHessian k x i j) +
      (k x : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
        inverseCoefficient u x i j * complexHessian h x i j) +
      (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        partialZ i (fun y => (h y : ℂ)) x * partialBar j (fun y => (k y : ℂ)) x) +
      (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        partialZ i (fun y => (k y : ℂ)) x * partialBar j (fun y => (h y : ℂ)) x) := by
    simp_rw [complexHessian_mul_entry hh hk]
    simp only [mul_add]
    simp_rw [show ∀ i j : Fin n,
      inverseCoefficient u x i j * ((h x : ℂ) * complexHessian k x i j) =
      (h x : ℂ) * (inverseCoefficient u x i j * complexHessian k x i j) by
        intros; ring]
    simp_rw [show ∀ i j : Fin n,
      inverseCoefficient u x i j * ((k x : ℂ) * complexHessian h x i j) =
      (k x : ℂ) * (inverseCoefficient u x i j * complexHessian h x i j) by
        intros; ring]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  unfold complexLaplacian gradientPairing
  rw [hsum]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem complexHessian_log_entry {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (hx : 0 < h x) (i j : Fin n) :
    complexHessian (fun y => Real.log (h y)) x i j =
      complexHessian h x i j / (h x : ℂ) -
        partialZ i (fun y => (h y : ℂ)) x *
          partialBar j (fun y => (h y : ℂ)) x / (h x : ℂ) ^ 2 := by
  exact ComplexProductLogAux.dz_dz_ofReal_log hh hx
    (realDirection i) (imagDirection i) (realDirection j) (-imagDirection j)

/-- The exact logarithmic Laplacian, including its gradient correction. -/
theorem complexLaplacian_log {n : ℕ} (u : E n → ℝ) {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (hx : 0 < h x) :
    complexLaplacian u (fun y => Real.log (h y)) x =
      complexLaplacian u h x / h x - metricGradientNormSq u h x / h x ^ 2 := by
  have hsum : (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
      complexHessian (fun y => Real.log (h y)) x i j) =
      (((h x)⁻¹ : ℝ) : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
        inverseCoefficient u x i j * complexHessian h x i j) -
      (((h x ^ 2)⁻¹ : ℝ) : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
        inverseCoefficient u x i j * partialZ i (fun y => (h y : ℂ)) x *
          partialBar j (fun y => (h y : ℂ)) x) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n,
          ((((h x)⁻¹ : ℝ) : ℂ) * (inverseCoefficient u x i j * complexHessian h x i j) -
            (((h x ^ 2)⁻¹ : ℝ) : ℂ) *
              (inverseCoefficient u x i j * partialZ i (fun y => (h y : ℂ)) x *
                partialBar j (fun y => (h y : ℂ)) x)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [complexHessian_log_entry hh hx]
        push_cast
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold complexLaplacian metricGradientNormSq gradientPairing
  rw [hsum]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem metricGradientNormSq_sub_const {n : ℕ} (u : E n → ℝ)
    {h : E n → ℝ} {x : E n} (hh : DifferentiableAt ℝ h x) (c : ℝ) :
    metricGradientNormSq u (fun y => h y - c) x = metricGradientNormSq u h x := by
  have heq : (fun y => h y - c) = (fun y => -c + 1 * h y) := by
    funext y
    ring
  unfold metricGradientNormSq
  rw [heq, gradientPairing_const_add_const_mul_left u _ hh (-c) 1,
    gradientPairing_const_add_const_mul_right u h hh (-c) 1]
  ring

/-- A useful shifted version: the gradient correction involves `h`, since
the constant shift has zero actual derivative. -/
theorem complexLaplacian_log_sub_const {n : ℕ} (u : E n → ℝ)
    {h : E n → ℝ} {x : E n} (hh : ContDiffAt ℝ ∞ h x)
    (c : ℝ) (hx : 0 < h x - c) :
    complexLaplacian u (fun y => Real.log (h y - c)) x =
      complexLaplacian u h x / (h x - c) -
        metricGradientNormSq u h x / (h x - c) ^ 2 := by
  rw [complexLaplacian_log u (hh.sub contDiffAt_const) hx,
    complexLaplacian_sub_at u hh contDiffAt_const, complexLaplacian_const,
    metricGradientNormSq_sub_const u (hh.differentiableAt (by simp)) c]
  simp only [sub_zero]

end KEBall
