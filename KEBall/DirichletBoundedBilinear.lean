import KEBall.DirichletDifferenceQuotientSchauder

/-! Bounded bilinear sources and their actual Holder constants. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal

namespace KEBall

theorem dirichlet_holderWith_bilinear {n : ℕ} {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (L : A →L[ℝ] B →L[ℝ] C) {f : E n → A} {g : E n → B}
    {Kf Kg Mf Mg α : ℝ≥0} (hf : HolderWith Kf α f) (hg : HolderWith Kg α g)
    (hfn : ∀ x, ‖f x‖ ≤ Mf) (hgn : ∀ x, ‖g x‖ ≤ Mg) :
    HolderWith (‖L‖₊ * (Mf * Kg + Mg * Kf)) α (fun x => L (f x) (g x)) := by
  apply holderOnWith_univ.mp
  apply dirichlet_holderOnWith_of_norm_sub_le
  intro x _ y _
  have hfd : ‖f x - f y‖ ≤ (Kf : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hf.dist_le x y
  have hgd : ‖g x - g y‖ ≤ (Kg : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hg.dist_le x y
  have hfx := hfn x
  have hgy := hgn y
  have he : L (f x) (g x) - L (f y) (g y) =
      L (f x) (g x - g y) + L (f x - f y) (g y) := by
    simp only [map_sub, sub_apply]
    abel
  rw [he]
  calc
    ‖L (f x) (g x - g y) + L (f x - f y) (g y)‖ ≤
        ‖L (f x) (g x - g y)‖ + ‖L (f x - f y) (g y)‖ := norm_add_le _ _
    _ ≤ ‖L‖ * ‖f x‖ * ‖g x - g y‖ + ‖L‖ * ‖f x - f y‖ * ‖g y‖ :=
      add_le_add (L.le_opNorm₂ _ _) (L.le_opNorm₂ _ _)
    _ ≤ ‖L‖ * Mf * ((Kg : ℝ) * ‖x - y‖ ^ (α : ℝ)) +
        ‖L‖ * ((Kf : ℝ) * ‖x - y‖ ^ (α : ℝ)) * Mg := by gcongr <;> assumption
    _ = ((‖L‖₊ * (Mf * Kg + Mg * Kf) : ℝ≥0) : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
      simp only [NNReal.coe_mul, NNReal.coe_add, coe_nnnorm]
      ring

theorem nnnorm_dirichlet_bilinearBoundedContinuousFunction_le {n : ℕ} {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (L : A →L[ℝ] B →L[ℝ] C)
    (f : BoundedContinuousFunction (E n) A) (g : BoundedContinuousFunction (E n) B) :
    ‖bilinearBoundedContinuousFunction L f g‖₊ ≤ ‖L‖₊ * ‖f‖₊ * ‖g‖₊ := by
  change ‖bilinearBoundedContinuousFunction L f g‖ ≤ ‖L‖ * ‖f‖ * ‖g‖
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  apply (L.le_opNorm₂ (f x) (g x)).trans
  gcongr
  · exact f.norm_coe_le_norm x
  · exact g.norm_coe_le_norm x

noncomputable def dirichletContractionRightLinearMap {n : ℕ} (A : E n →L[ℝ] E n) :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun H := dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) A H
  map_add' H J := by simp only [dirichletBilinearContraction, add_apply, Finset.sum_add_distrib]
  map_smul' c H := by
    simp only [dirichletBilinearContraction, smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

noncomputable def dirichletContractionCLM (n : ℕ) :
    (E n →L[ℝ] E n) →L[ℝ] (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ := by
  let L : (E n →L[ℝ] E n) →ₗ[ℝ] (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
    { toFun A := (dirichletContractionRightLinearMap A).toContinuousLinearMap
      map_add' A B := by
        ext H
        exact (dirichletBilinearContractionLinearMap
          (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) H).map_add A B
      map_smul' c A := by
        ext H
        exact (dirichletBilinearContractionLinearMap
          (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) H).map_smul c A }
  exact L.toContinuousLinearMap

theorem dirichletContractionCLM_apply {n : ℕ} (A : E n →L[ℝ] E n)
    (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    dirichletContractionCLM n A H =
      dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) A H := rfl

end KEBall
