import KEBall.DirichletClosedBallEllipticity
import KEBall.DirichletSchauderPositiveMatrix
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual averaged cofactor in a determinant difference

The segment average is a continuous linear operator.  The fundamental
theorem of calculus identifies its contraction with the exact determinant
difference.  Positivity is proved along the whole matrix segment and then
under the integral; no pointwise choice of a mean-value parameter is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder Matrix.Norms.Elementwise

namespace KEBall

open KEBallProbe

noncomputable def dirichletMeanCofactor {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) : E n →L[ℝ] E n :=
  ∫ t in (0 : ℝ)..1, dirichletCofactorOfMatrix (A + t • (B - A))

theorem continuous_dirichlet_cofactor_segment {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => dirichletCofactorOfMatrix (A + t • (B - A))) :=
  contDiff_dirichletCofactorOfMatrix.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))

theorem dirichlet_det_sub_eq_integral_cofactor {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    B.det.re - A.det.re =
      ∫ t in (0 : ℝ)..1, ((A + t • (B - A)).adjugate * (B - A)).trace.re := by
  let C (t : ℝ) := A + t • (B - A)
  have hC (t : ℝ) : HasDerivAt C (B - A) t := by
    simpa only [C, id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const (B - A)).const_add A
  have hD (t : ℝ) : HasDerivAt (fun s : ℝ => (C s).det.re)
      ((C t).adjugate * (B - A)).trace.re t := by
    have hd := (complex_det_differentiableAt (C t)).hasFDerivAt.comp_hasDerivAt t (hC t)
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa only [fderiv_real_complex_det, Function.comp_def, Complex.reCLM_apply] using h
  have hCont : Continuous (fun t : ℝ => ((C t).adjugate * (B - A)).trace.re) := by
    have hAdj : Continuous (fun t : ℝ => (C t).adjugate) :=
      contDiff_dirichlet_adjugate.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))
    exact Complex.continuous_re.comp (hAdj.mul continuous_const).matrix_trace
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)
    (hCont.intervalIntegrable 0 1)
  simpa only [C, one_smul, zero_smul, add_zero, add_sub_cancel] using h.symm

theorem dirichletBilinearContraction_meanCofactor {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (D : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hD : complexHessianOfRealBilinear D = B - A) :
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletMeanCofactor A B) D = B.det.re - A.det.re := by
  let L := (dirichletBilinearContractionLinearMap
    (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) D).toContinuousLinearMap
  have h := L.intervalIntegral_comp_comm (μ := volume)
    ((continuous_dirichlet_cofactor_segment A B).intervalIntegrable 0 1)
  change (∫ t in (0 : ℝ)..1, dirichletBilinearContraction
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletCofactorOfMatrix (A + t • (B - A))) D) =
    dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
      (dirichletMeanCofactor A B) D at h
  rw [← h, dirichlet_det_sub_eq_integral_cofactor]
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [hD] using! dirichletBilinearContraction_cofactor (A + t • (B - A)) D

theorem dirichlet_matrix_segment_posDef {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (A + t • (B - A)).PosDef := by
  have he : A + t • (B - A) = (1 - t) • A + t • B := by module
  rw [he]
  by_cases h1 : t = 1
  · simpa only [h1, sub_self, zero_smul, one_smul, zero_add] using hB
  · exact (hA.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))).add_posSemidef
      (hB.posSemidef.smul ht.1)

theorem inner_dirichletMeanCofactor {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (v z : E n) :
    inner ℝ (dirichletMeanCofactor A B v) z =
      ∫ t in (0 : ℝ)..1, inner ℝ (dirichletCofactorOfMatrix (A + t • (B - A)) v) z := by
  let L : (E n →L[ℝ] E n) →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ (E n) z).comp (ContinuousLinearMap.apply ℝ (E n) v)
  have hL (P : E n →L[ℝ] E n) : L P = inner ℝ (P v) z := by
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_comm]
  have h := L.intervalIntegral_comp_comm (μ := volume)
    ((continuous_dirichlet_cofactor_segment A B).intervalIntegrable 0 1)
  simpa only [hL, dirichletMeanCofactor] using h.symm

theorem dirichletMeanCofactor_pos {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {v : E n} (hv : v ≠ 0) :
    0 < inner ℝ (dirichletMeanCofactor A B v) v := by
  rw [inner_dirichletMeanCofactor]
  have hCont : Continuous (fun t : ℝ =>
      inner ℝ (dirichletCofactorOfMatrix (A + t • (B - A)) v) v) :=
    ((continuous_dirichlet_cofactor_segment A B).clm_apply continuous_const).inner continuous_const
  apply intervalIntegral.integral_pos zero_lt_one hCont.continuousOn
  · intro t ht
    exact (dirichletCofactorOfMatrix_pos (dirichlet_matrix_segment_posDef hA hB
      (Ioc_subset_Icc_self ht)) hv).le
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩,
      dirichletCofactorOfMatrix_pos (dirichlet_matrix_segment_posDef hA hB ⟨le_rfl, zero_le_one⟩) hv⟩

theorem dirichletMeanCofactor_symmetric {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (v z : E n) :
    inner ℝ (dirichletMeanCofactor A B v) z = inner ℝ (dirichletMeanCofactor A B z) v := by
  rw [inner_dirichletMeanCofactor, inner_dirichletMeanCofactor]
  apply intervalIntegral.integral_congr
  intro t ht
  exact dirichletCofactorOfMatrix_symmetric
    (dirichlet_matrix_segment_posDef hA hB (by simpa only [uIcc_of_le zero_le_one] using ht)).isHermitian
    v z

end KEBall
