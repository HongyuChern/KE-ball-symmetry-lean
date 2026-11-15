import KEBall.FiberEnergyGreen
import KEBall.FiberEnergyMixedHessian
import KEBall.BrezisMerleDiscMass

/-!
# The determinant expansion for the fiber curvature formula
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexOrder ContDiff Laplacian Matrix

namespace KEBall.MoserTrudinger

private theorem mixed_adjugate_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (p q r s : Fin n → ℂ) :
    (∑ j : Fin n, ∑ i : Fin n,
      ((2 : ℂ)⁻¹ * (r j - Complex.I * s j)) * A j i *
        ((2 : ℂ)⁻¹ * (p i + Complex.I * q i))) =
      (4 : ℂ)⁻¹ * ((∑ i : Fin n, ∑ j : Fin n, p i * (A j i * r j)) +
        (∑ i : Fin n, ∑ j : Fin n, q i * (A j i * s j)) +
        Complex.I * ((∑ i : Fin n, ∑ j : Fin n, q i * (A j i * r j)) -
          (∑ i : Fin n, ∑ j : Fin n, p i * (A j i * s j)))) := by
  simp only [mul_sub, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  nth_rw 1 [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(A j i * q i * s j) / 4) * hI

/-- Determinant of the total Hessian in terms of the fiber determinant,
the disc Laplacian, and the two disc-direction derivatives of the fiber. -/
theorem productComplexHessian_det_re {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : E n) (w : E 1)
    (hP : (complexHessian (fun y => u (y, w)) z).PosDef) :
    (productComplexHessian u z w).det.re =
      ((Δ (fun y => u (z, y)) w * (complexHessian (fun y => u (y, w)) z).det.re) -
        (cofactorGradientContraction (fun y => u (y, w))
          (fun y => discDirectionalDerivative u (realDirection 0) (y, w))
          (fun y => discDirectionalDerivative u (realDirection 0) (y, w)) z).re -
        (cofactorGradientContraction (fun y => u (y, w))
          (fun y => discDirectionalDerivative u (imagDirection 0) (y, w))
          (fun y => discDirectionalDerivative u (imagDirection 0) (y, w)) z).re +
        (cofactorGradientContraction (fun y => u (y, w))
          (fun y => discDirectionalDerivative u (imagDirection 0) (y, w))
          (fun y => discDirectionalDerivative u (realDirection 0) (y, w)) z).im -
        (cofactorGradientContraction (fun y => u (y, w))
          (fun y => discDirectionalDerivative u (realDirection 0) (y, w))
          (fun y => discDirectionalDerivative u (imagDirection 0) (y, w)) z).im) / 4 := by
  let A := complexHessian (fun y => u (y, w)) z
  let H := productComplexHessian u z w
  let R : E n → ℝ := fun y => discDirectionalDerivative u (realDirection 0) (y, w)
  let S : E n → ℝ := fun y => discDirectionalDerivative u (imagDirection 0) (y, w)
  let p (i : Fin n) := partialZ i (fun y => (R y : ℂ)) z
  let q (i : Fin n) := partialZ i (fun y => (S y : ℂ)) z
  let r (j : Fin n) := partialBar j (fun y => (R y : ℂ)) z
  let s (j : Fin n) := partialBar j (fun y => (S y : ℂ)) z
  have hA : H.toBlocks₁₁ = A := by
    ext i j
    exact productComplexHessian_fiber hu z w i j
  have hB (i : Fin n) : H.toBlocks₁₂ i 0 = (2 : ℂ)⁻¹ * (p i + Complex.I * q i) :=
    productComplexHessian_fiber_disc hu z w i
  have hC (j : Fin n) : H.toBlocks₂₁ 0 j = (2 : ℂ)⁻¹ * (r j - Complex.I * s j) :=
    productComplexHessian_disc_fiber hu z w j
  have hD : (H.toBlocks₂₂ 0 0).re = Δ (fun y => u (z, y)) w / 4 := by
    have h := productComplexHessian_disc hu z w 0 0
    change H.toBlocks₂₂ 0 0 = _ at h
    have hv : ContDiff ℝ ∞ (fun y => u (z, y)) := hu.comp (contDiff_const.prodMk contDiff_id)
    have hd := BrezisMerle.complexHessian_det_re_eq_laplacian_div_four (x := w) hv.contDiffAt
    rw [Matrix.det_fin_one] at hd
    rw [h, hd]
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hP.isUnit
  have heq := det_fromBlocks_disc H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂
    (by rw [hA]; exact hdet)
  rw [Matrix.fromBlocks_toBlocks, hA] at heq
  simp_rw [hB, hC] at heq
  rw [mixed_adjugate_sum] at heq
  change H.det.re = _
  rw [heq, posDef_det_eq_ofReal_re hP]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re, Complex.I_re, Complex.I_im, Complex.sub_im]
  rw [hD, show (4 : ℂ)⁻¹ = ((1 / 4 : ℝ) : ℂ) by norm_num]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  unfold cofactorGradientContraction cofactorVectorField
  simp only [Finset.mul_sum, p, q, r, s, R, S, A]
  ring

end KEBall.MoserTrudinger
