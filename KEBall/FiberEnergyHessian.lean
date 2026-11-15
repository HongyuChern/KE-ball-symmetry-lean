import KEBall.MoserTrudingerSmoothVariation
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The complex Hessian in the fiber and disc directions

The diagonal blocks are the Hessians of the restrictions to the two
factors. The block determinant identifies the mixed term that appears
when differentiating the fiber energy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ContDiff Matrix

namespace KEBall.MoserTrudinger

open KEBallProbe

private theorem rd_comp_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℂ}
    (hf : Differentiable ℝ f) (L : E →L[ℝ] F) (p : F) (v : E) :
    rd v (fun x => f (p + L x)) = fun x => rd (L v) f (p + L x) := by
  funext x
  have h := (hf (p + L x)).hasFDerivAt.comp x (L.hasFDerivAt.const_add p)
  change HasFDerivAt (fun x => f (p + L x)) _ x at h
  unfold rd
  rw [h.fderiv]
  rfl

theorem dz_comp_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℂ}
    (hf : Differentiable ℝ f) (L : E →L[ℝ] F) (p : F) (a b : E) :
    dz a b (fun x => f (p + L x)) = fun x => dz (L a) (L b) f (p + L x) := by
  funext x
  simp only [dz, rd_comp_affine hf L p]

theorem wirtingerHessian_comp_affine {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℂ}
    (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F) (p : F) (a b : ι → E) (x : E) (i j : ι) :
    wirtingerHessian a b (fun y => f (p + L y)) x i j =
      wirtingerHessian (fun k => L (a k)) (fun k => L (b k)) f (p + L x) i j := by
  have h (c d : F) : Differentiable ℝ (dz c d f) :=
    fun y => (smoothAt_dz hf.contDiffAt c d).differentiableAt (by simp)
  unfold wirtingerHessian
  rw [dz_comp_affine (hf.differentiable (by simp)) L p (a j) (-b j),
    dz_comp_affine (h _ _) L p]
  rw [map_neg]

/-- The real coordinate frame split into the fiber and base factors. -/
noncomputable def productRealDirection {n : ℕ} : Fin n ⊕ Fin 1 → E n × E 1 :=
  Sum.elim (fun i => (realDirection i, 0)) (fun i => (0, realDirection i))

/-- The imaginary coordinate frame split into the fiber and base factors. -/
noncomputable def productImagDirection {n : ℕ} : Fin n ⊕ Fin 1 → E n × E 1 :=
  Sum.elim (fun i => (imagDirection i, 0)) (fun i => (0, imagDirection i))

/-- The complex Hessian of a function on a fiber ball times a disc. -/
noncomputable def productComplexHessian {n : ℕ} (u : E n × E 1 → ℝ) (z : E n) (w : E 1) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
  wirtingerHessian productRealDirection productImagDirection (fun p => (u p : ℂ)) (z, w)

theorem productComplexHessian_fiber {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : E n) (w : E 1) (i j : Fin n) :
    productComplexHessian u z w (Sum.inl i) (Sum.inl j) =
      complexHessian (fun y => u (y, w)) z i j := by
  let L := ContinuousLinearMap.inl ℝ (E n) (E 1)
  have hc : ContDiff ℝ ∞ (fun p => (u p : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have he (x : E n) : ((0, w) : E n × E 1) + L x = (x, w) := by simp [L]
  have h := wirtingerHessian_comp_affine hc L (0, w) realDirection imagDirection z i j
  simp only [he] at h
  exact h.symm

theorem productComplexHessian_disc {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : E n) (w : E 1) (i j : Fin 1) :
    productComplexHessian u z w (Sum.inr i) (Sum.inr j) =
      complexHessian (fun y => u (z, y)) w i j := by
  let L := ContinuousLinearMap.inr ℝ (E n) (E 1)
  have hc : ContDiff ℝ ∞ (fun p => (u p : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have he (x : E 1) : ((z, 0) : E n × E 1) + L x = (z, x) := by simp [L]
  have h := wirtingerHessian_comp_affine hc L (z, 0) realDirection imagDirection w i j
  simp only [he] at h
  exact h.symm

/-- Expansion of the block determinant with a one-dimensional base. -/
theorem det_fromBlocks_disc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin n) ℂ)
    (D : Matrix (Fin 1) (Fin 1) ℂ) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D).det =
      A.det * D 0 0 -
        ∑ j : Fin n, ∑ i : Fin n, C 0 j * A.adjugate j i * B i 0 := by
  let : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_one, Matrix.invOf_eq_nonsing_inv, Matrix.sub_apply,
    mul_sub]
  congr 1
  have he : A.det • A⁻¹ = A.adjugate := by
    rw [A.nonsing_inv_apply hA, smul_smul, hA.mul_val_inv, one_smul]
  rw [← he]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  nth_rw 1 [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end KEBall.MoserTrudinger
