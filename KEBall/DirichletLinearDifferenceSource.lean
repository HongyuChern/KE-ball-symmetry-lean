import KEBall.DirichletBoundedBilinear

/-!
# The source in a variable-coefficient difference-quotient equation

The coefficient is frozen at x in the principal term.  Its difference
quotient is contracted with the Hessian at the translated endpoint.
The derivative bounds cancel the reciprocal step in both source terms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal

namespace KEBall

noncomputable def dirichletBoundedTranslate {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : BoundedContinuousFunction (E n) F) (z : E n) : BoundedContinuousFunction (E n) F :=
  f.compContinuous ⟨fun x => x + z, continuous_id.add_const z⟩

theorem dirichletBoundedTranslate_apply {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : BoundedContinuousFunction (E n) F) (z x : E n) :
    dirichletBoundedTranslate f z x = f (x + z) := rfl

theorem nnnorm_dirichletBoundedTranslate_le {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : BoundedContinuousFunction (E n) F) (z : E n) : ‖dirichletBoundedTranslate f z‖₊ ≤ ‖f‖₊ :=
  f.norm_compContinuous_le _

theorem holderWith_dirichletBoundedTranslate {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : BoundedContinuousFunction (E n) F} {K α : ℝ≥0}
    (hf : HolderWith K α (f : E n → F)) (z : E n) :
    HolderWith K α (dirichletBoundedTranslate f z : E n → F) := by
  intro x y
  change edist (f (x + z)) (f (y + z)) ≤ _
  simpa only [edist_add_right] using hf (x + z) (y + z)

noncomputable def dirichletLinearDifferenceSource {n : ℕ}
    (A : BoundedContinuousFunction (E n) (E n →L[ℝ] E n))
    (H : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ) (v : E n) (h : ℝ) :
    BoundedContinuousFunction (E n) ℝ :=
  dirichletBoundedDifferenceQuotient f v h -
    bilinearBoundedContinuousFunction (dirichletContractionCLM n)
      (dirichletBoundedDifferenceQuotient A v h) (dirichletBoundedTranslate H (h • v))

theorem dirichletLinearDifferenceSource_apply {n : ℕ}
    (A : BoundedContinuousFunction (E n) (E n →L[ℝ] E n))
    (H : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ) (v : E n) (h : ℝ) (x : E n) :
    dirichletLinearDifferenceSource A H f v h x = dirichletBoundedDifferenceQuotient f v h x -
      dirichletContractionCLM n (dirichletBoundedDifferenceQuotient A v h x) (H (x + h • v)) := rfl

theorem dirichlet_linear_difference_equation {n : ℕ}
    (A : BoundedContinuousFunction (E n) (E n →L[ℝ] E n))
    (H : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ) (v x : E n) (h : ℝ)
    (hx : dirichletContractionCLM n (A x) (H x) = f x)
    (hShift : dirichletContractionCLM n (A (x + h • v)) (H (x + h • v)) = f (x + h • v)) :
    dirichletContractionCLM n (A x) (dirichletBoundedDifferenceQuotient H v h x) =
      dirichletLinearDifferenceSource A H f v h x := by
  rw [dirichletLinearDifferenceSource_apply]
  simp only [dirichletBoundedDifferenceQuotient_apply, dirichletDifferenceQuotient,
    map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul, ← hx, ← hShift]
  ring

theorem exists_dirichlet_uniform_linear_difference_source_bounds {n : ℕ}
    (A : BoundedContinuousFunction (E n) (E n →L[ℝ] E n))
    (DA : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] E n))
    (H : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ)
    (Df : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (hA : ∀ x, HasFDerivAt (A : E n → E n →L[ℝ] E n) (DA x) x)
    (hf : ∀ x, HasFDerivAt (f : E n → ℝ) (Df x) x)
    {KA KH Kf α : ℝ≥0}
    (hDA : HolderWith KA α (DA : E n → E n →L[ℝ] E n →L[ℝ] E n))
    (hH : HolderWith KH α (H : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hDf : HolderWith Kf α (Df : E n → E n →L[ℝ] ℝ)) (v : E n) :
    ∃ B K : ℝ≥0, ∀ h : ℝ, h ≠ 0 →
      ‖dirichletLinearDifferenceSource A H f v h‖₊ ≤ B ∧
      HolderWith K α (dirichletLinearDifferenceSource A H f v h : E n → ℝ) := by
  let M := ‖DA‖₊ * ‖v‖₊
  let D := ‖Df‖₊ * ‖v‖₊
  let B := D + ‖dirichletContractionCLM n‖₊ * M * ‖H‖₊
  let K := Kf * ‖v‖₊ + ‖dirichletContractionCLM n‖₊ * (M * KH + ‖H‖₊ * (KA * ‖v‖₊))
  refine ⟨B, K, ?_⟩
  intro h hh
  have hqaNorm : ‖dirichletBoundedDifferenceQuotient A v h‖₊ ≤ M :=
    nnnorm_dirichletBoundedDifferenceQuotient_le hA v hh
  have hqfNorm : ‖dirichletBoundedDifferenceQuotient f v h‖₊ ≤ D :=
    nnnorm_dirichletBoundedDifferenceQuotient_le hf v hh
  have hProdNorm := nnnorm_dirichlet_bilinearBoundedContinuousFunction_le
    (dirichletContractionCLM n) (dirichletBoundedDifferenceQuotient A v h) (dirichletBoundedTranslate H (h • v))
  have hqAH := holderWith_dirichletDifferenceQuotient_of_holder_derivative hA hDA v hh
  have hqfH := holderWith_dirichletDifferenceQuotient_of_holder_derivative hf hDf v hh
  have hProdH := dirichlet_holderWith_bilinear (Mf := M) (Mg := ‖H‖₊)
    (dirichletContractionCLM n) hqAH
    (holderWith_dirichletBoundedTranslate hH (h • v))
    (fun x => (dirichletBoundedDifferenceQuotient A v h).norm_coe_le_norm x |>.trans hqaNorm)
    (fun x => by
      change ‖H (x + h • v)‖ ≤ ‖H‖
      exact H.norm_coe_le_norm (x + h • v))
  refine ⟨?_, ?_⟩
  · apply (nnnorm_sub_le _ _).trans
    apply add_le_add hqfNorm
    apply hProdNorm.trans
    gcongr
    exact nnnorm_dirichletBoundedTranslate_le H (h • v)
  · exact holderWith_sub hqfH hProdH

end KEBall
