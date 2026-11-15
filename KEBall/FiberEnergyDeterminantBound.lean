import KEBall.FiberEnergyHessian
import KEBall.LogDetConcavity

/-!
# A determinant bound for a one-dimensional base block
-/

set_option autoImplicit false

open Filter
open scoped ComplexOrder Matrix Topology

namespace KEBall.MoserTrudinger

private theorem det_re_le_fiber_mul_base_of_posDef {n : ℕ}
    {H : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ} (hH : H.PosDef) :
    H.det.re ≤ H.toBlocks₁₁.det.re * (H.toBlocks₂₂ 0 0).re := by
  let A := H.toBlocks₁₁
  let b (i : Fin n) := H.toBlocks₁₂ i 0
  have hA : A.PosDef := hH.submatrix Sum.inl_injective
  have hUnit := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAdjEq : A.det • A⁻¹ = A.adjugate := by
    rw [A.nonsing_inv_apply hUnit, smul_smul, hUnit.mul_val_inv, one_smul]
  have hAdj : A.adjugate.PosSemidef := by
    rw [← hAdjEq]
    exact (hA.inv.smul hA.det_pos).posSemidef
  have hcross (j : Fin n) : H.toBlocks₂₁ 0 j = star (b j) := by
    change H (Sum.inr 0) (Sum.inl j) = star (H (Sum.inl j) (Sum.inr 0))
    exact (congrFun (congrFun hH.isHermitian.eq (Sum.inr 0)) (Sum.inl j)).symm
  have hsum :
      (∑ j : Fin n, ∑ i : Fin n, H.toBlocks₂₁ 0 j * A.adjugate j i * H.toBlocks₁₂ i 0) =
        star b ⬝ᵥ (A.adjugate *ᵥ b) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, hcross, b, mul_assoc]
  have hpos := (RCLike.nonneg_iff.mp (hAdj.dotProduct_mulVec_nonneg b)).1
  have hdet := det_fromBlocks_disc A H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂ hUnit
  change (Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂).det =
    A.det * H.toBlocks₂₂ 0 0 -
      ∑ j : Fin n, ∑ i : Fin n, H.toBlocks₂₁ 0 j * A.adjugate j i * H.toBlocks₁₂ i 0 at hdet
  rw [Matrix.fromBlocks_toBlocks, hsum] at hdet
  rw [hdet, posDef_det_eq_ofReal_re hA, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact sub_le_self _ hpos

/-- For a positive semidefinite complex Hessian, the determinant is at
most the fiber determinant times the base diagonal entry. -/
theorem det_re_le_fiber_mul_base {n : ℕ}
    {H : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ} (hH : H.PosSemidef) :
    H.det.re ≤ H.toBlocks₁₁.det.re * (H.toBlocks₂₂ 0 0).re := by
  let H' (t : ℝ) := H + (t : ℂ) • (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ)
  let f (t : ℝ) := (H' t).det.re
  let g (t : ℝ) := (H' t).toBlocks₁₁.det.re * ((H' t).toBlocks₂₂ 0 0).re
  have hH' : Continuous H' := continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hf : Continuous f := by unfold f; fun_prop
  have hg₁ : Continuous (fun t => (H' t).toBlocks₁₁) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply (Sum.inl j)).comp ((continuous_apply (Sum.inl i)).comp hH')
  have hg₂ : Continuous (fun t => (H' t).toBlocks₂₂ 0 0) :=
    (continuous_apply (Sum.inr 0)).comp ((continuous_apply (Sum.inr 0)).comp hH')
  have hg : Continuous g := by unfold g; fun_prop
  have h' (t : ℝ) (ht : 0 < t) : f t ≤ g t :=
    det_re_le_fiber_mul_base_of_posDef
      (Matrix.PosDef.posSemidef_add hH (Matrix.PosDef.one.smul (by exact_mod_cast ht)))
  have : NeBot (𝓝[Set.Ioi (0 : ℝ)] 0) := nhdsWithin_Ioi_neBot le_rfl
  have h := le_of_tendsto_of_tendsto (f := f) (g := g)
    (hf.continuousAt.continuousWithinAt : Tendsto f (𝓝[Set.Ioi 0] 0) (𝓝 (f 0)))
    (hg.continuousAt.continuousWithinAt : Tendsto g (𝓝[Set.Ioi 0] 0) (𝓝 (g 0)))
    (Filter.Eventually.mono self_mem_nhdsWithin h')
  simpa only [f, g, H', Complex.ofReal_zero, zero_smul, add_zero] using h

end KEBall.MoserTrudinger
