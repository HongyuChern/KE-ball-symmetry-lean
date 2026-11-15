import KEBall.BedfordTaylorAffineHessian
import KEBall.BedfordTaylorMixedConvergence
import Mathlib.Analysis.Matrix.Order

/-!
# Positivity of the smooth second mixed Hessian
-/

set_option autoImplicit false

open Matrix MeasureTheory TopologicalSpace
open scoped ComplexOrder ContDiff Distributions MatrixOrder

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn)

private theorem mixedMinor_nonneg {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ A 0 0 * B 1 1 - A 1 0 * B 0 1 - A 0 1 * B 1 0 + A 1 1 * B 0 0 := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨T, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  let m (i j : Fin 2) : ℂ := S i 0 * T j 1 - S i 1 * T j 0
  have heq : (star S * S) 0 0 * (star T * T) 1 1 -
        (star S * S) 1 0 * (star T * T) 0 1 -
        (star S * S) 0 1 * (star T * T) 1 0 +
        (star S * S) 1 1 * (star T * T) 0 0 =
      ∑ i, ∑ j, star (m i j) * m i j := by
    simp only [m, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, star_sub, star_mul]
    ring
  rw [heq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => star_mul_self_nonneg _

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}

theorem smoothMixedHessianDensity_nonneg (hu : IsSmoothPshOn Ω u) (hp : IsSmoothPshOn Ω p)
    {x : ComplexModel n} (hx : x ∈ Ω) (v : Fin 2 → ComplexModel n) :
    0 ≤ smoothMixedHessianDensity u p v v x := by
  let A := Matrix.of fun i j : Fin 2 => classicalComplexHessianEntry u (v i) (v j) x
  let B := Matrix.of fun i j : Fin 2 => classicalComplexHessianEntry p (v i) (v j) x
  change 0 ≤ A 0 0 * B 1 1 - A 1 0 * B 0 1 - A 0 1 * B 1 0 + A 1 1 * B 0 0
  exact mixedMinor_nonneg (A := A) (B := B)
    (posSemidef_classicalComplexHessianEntry hu hx v) (posSemidef_classicalComplexHessianEntry hp hx v)

/-- On the diagonal, the second mixed Hessian of two smooth PSH potentials
induces a positive real distribution. -/
theorem positive_secondMixedHessian_of_isSmoothPshOn (hu : IsSmoothPshOn Ω u)
    (hp : IsSmoothPshOn Ω p) (v : Fin 2 → ComplexModel n) :
    PositiveDistribution (Distribution.mapCLM Complex.reCLM
      (secondMixedHessian (isLocallyBoundedPshOn_of_isSmoothPshOn hu)
        (isLocallyBoundedPshOn_of_isSmoothPshOn hp) v v)) := by
  intro φ hφ
  have hs := contDiffOn_smoothMixedHessianDensity hu.1 hp.1 v v
  have hI : Integrable (fun x => φ x • smoothMixedHessianDensity u p v v x) :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_of_contDiffOn hs)
  rw [Distribution.mapCLM_apply, secondMixedHessian_integral_of_isSmoothPshOn hu hp,
    ← Complex.reCLM.integral_comp_comm hI]
  apply integral_nonneg
  intro x
  change 0 ≤ Complex.reCLM (φ x • smoothMixedHessianDensity u p v v x)
  by_cases hx : x ∈ Ω
  · rw [Complex.reCLM_apply, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (hφ x) ((Complex.nonneg_iff.mp (smoothMixedHessianDensity_nonneg hu hp hx v)).1)
  · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
    simp [hzero]

end KEBall.BedfordTaylor
