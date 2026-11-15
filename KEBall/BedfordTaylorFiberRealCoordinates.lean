import KEBall.BedfordTaylorProductHessianBlocks
import KEBall.BedfordTaylorSmoothMatrixProduct
import KEBall.BedfordTaylorCoordinates

/-!
# Real coordinates for the Bedford–Taylor fiber curvature identity
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexOrder ContDiff Matrix

namespace KEBall.BedfordTaylor

open KEBallProbe MoserTrudinger
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

/-- The real product model with dilation in the fiber coordinates. -/
noncomputable def fiberDilationCoordinates (n : ℕ) (R : ℝ) :
    (E n × E 1) →L[ℝ] ComplexModel (n + 1) :=
  ((complexProductCoordinates n 1).symm.toContinuousLinearMap.restrictScalars ℝ).comp
    ((R • (complexCoordinates n).toContinuousLinearMap).prodMap
      (complexCoordinates 1).toContinuousLinearMap)

theorem fiberDilationCoordinates_apply (n : ℕ) (R : ℝ) (p : E n × E 1) :
    fiberDilationCoordinates n R p =
      (complexProductCoordinates n 1).symm (R • complexCoordinates n p.1, complexCoordinates 1 p.2) :=
  rfl

/-- Coordinate scale factors on the two blocks. -/
def fiberCoordinateScale {n : ℕ} (R : ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  Sum.elim (fun _ => R) (fun _ => 1)

private theorem fiberDilationCoordinates_realDirection {n : ℕ} (R : ℝ) (i : Fin n ⊕ Fin 1) :
    fiberDilationCoordinates n R (productRealDirection i) =
      fiberCoordinateScale R i • coordinateVector (finSumFinEquiv i) := by
  let e := complexProductCoordinates n 1
  let er : ComplexModel (n + 1) →L[ℝ] ComplexModel n × ComplexModel 1 :=
    e.toContinuousLinearMap.restrictScalars ℝ
  apply e.injective
  rw [fiberDilationCoordinates_apply, show (complexProductCoordinates n 1) = e from rfl, e.apply_symm_apply]
  rw [show e (fiberCoordinateScale R i • coordinateVector (finSumFinEquiv i)) =
    fiberCoordinateScale R i • e (coordinateVector (finSumFinEquiv i)) from er.map_smul _ _]
  cases i with
  | inl i =>
    rw [show e (coordinateVector (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin 1))) =
      (coordinateVector i, 0) from complexProductCoordinates_coordinateVector_inl i]
    simp only [productRealDirection, Sum.elim_inl, complexCoordinates_realDirection,
      fiberCoordinateScale, map_zero,
      Prod.smul_mk, smul_zero, coordinateVector]
  | inr i =>
    rw [show e (coordinateVector (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin 1))) =
      (0, coordinateVector i) from complexProductCoordinates_coordinateVector_inr i]
    simp only [productRealDirection, Sum.elim_inr, complexCoordinates_realDirection,
      fiberCoordinateScale, map_zero,
      smul_zero, one_smul, coordinateVector]

private theorem fiberDilationCoordinates_imagDirection {n : ℕ} (R : ℝ) (i : Fin n ⊕ Fin 1) :
    fiberDilationCoordinates n R (productImagDirection i) =
      Complex.I • (fiberCoordinateScale R i • coordinateVector (finSumFinEquiv i)) := by
  let e := complexProductCoordinates n 1
  let er : ComplexModel (n + 1) →L[ℝ] ComplexModel n × ComplexModel 1 :=
    e.toContinuousLinearMap.restrictScalars ℝ
  apply e.injective
  rw [fiberDilationCoordinates_apply, show (complexProductCoordinates n 1) = e from rfl, e.apply_symm_apply,
    map_smul]
  rw [show e (fiberCoordinateScale R i • coordinateVector (finSumFinEquiv i)) =
    fiberCoordinateScale R i • e (coordinateVector (finSumFinEquiv i)) from er.map_smul _ _]
  cases i with
  | inl i =>
    rw [show e (coordinateVector (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin 1))) =
      (coordinateVector i, 0) from complexProductCoordinates_coordinateVector_inl i]
    simp only [productImagDirection, Sum.elim_inl, complexCoordinates_imagDirection,
      fiberCoordinateScale, map_zero,
      Prod.smul_mk, smul_zero, coordinateVector]
    rw [smul_comm]
  | inr i =>
    rw [show e (coordinateVector (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin 1))) =
      (0, coordinateVector i) from complexProductCoordinates_coordinateVector_inr i]
    simp only [productImagDirection, Sum.elim_inr, complexCoordinates_imagDirection,
      fiberCoordinateScale, map_zero,
      Prod.smul_mk, smul_zero, one_smul, coordinateVector]

private theorem classicalComplexHessianEntry_real_smul {n : ℕ}
    {u : ComplexModel n → ℝ} {x : ComplexModel n}
    (hu : ContDiffAt ℝ ∞ u x) (a b : ComplexModel n) (s t : ℝ) :
    classicalComplexHessianEntry u (s • a) (t • b) x =
      (s : ℂ) * classicalComplexHessianEntry u a b x * (t : ℂ) := by
  rw [classicalComplexHessianEntry_eq_realHessian hu, classicalComplexHessianEntry_eq_realHessian hu]
  rw [show Complex.I • (s • a) = s • (Complex.I • a) from smul_comm _ _ _,
    show Complex.I • (t • b) = t • (Complex.I • b) from smul_comm _ _ _]
  simp only [PshLines.realHessian_smul_left, PshLines.realHessian_smul_right]
  push_cast
  ring

/-- The real product Hessian is obtained from the ambient Hessian by
multiplying each fiber row and column by the dilation factor. -/
theorem productComplexHessian_fiberDilationCoordinates {n : ℕ}
    {u : ComplexModel (n + 1) → ℝ} (hu : ContDiff ℝ ∞ u)
    (R : ℝ) (z : E n) (w : E 1) :
    MoserTrudinger.productComplexHessian (u ∘ fiberDilationCoordinates n R) z w =
      Matrix.diagonal (fun i : Fin n ⊕ Fin 1 => (fiberCoordinateScale R i : ℂ)) *
        complexProductHessian (n := n) (m := 1) u (fiberDilationCoordinates n R (z, w)) *
        Matrix.diagonal (fun i : Fin n ⊕ Fin 1 => (fiberCoordinateScale R i : ℂ)) := by
  let L := fiberDilationCoordinates n R
  let F (x : ComplexModel (n + 1)) := (u x : ℂ)
  have hF : ContDiff ℝ ∞ F := Complex.ofRealCLM.contDiff.comp hu
  have h₀ : (fun y : E n × E 1 => F (0 + L y)) = (fun y => F (L y)) :=
    funext fun y => by rw [zero_add]
  ext i j : 1
  change wirtingerHessian productRealDirection productImagDirection (fun y => F (L y)) (z, w) i j = _
  rw [← h₀, wirtingerHessian_comp_affine hF L 0]
  simp only [zero_add, fiberDilationCoordinates_realDirection, fiberDilationCoordinates_imagDirection,
    L, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change classicalComplexHessianEntry u
      (fiberCoordinateScale R i • coordinateVector (finSumFinEquiv i))
      (fiberCoordinateScale R j • coordinateVector (finSumFinEquiv j))
      (fiberDilationCoordinates n R (z, w)) = _
  rw [classicalComplexHessianEntry_real_smul hu.contDiffAt,
    classicalComplexHessianEntry_coordinate_eq hu.contDiffAt]
  rfl

/-- Each fiber Hessian is scaled by the square of the fiber radius. -/
theorem fiberComplexHessian_fiberDilationCoordinates {n : ℕ}
    {u : ComplexModel (n + 1) → ℝ} (hu : ContDiff ℝ ∞ u)
    (R : ℝ) (z : E n) (w : E 1) :
    KEBall.complexHessian (fun y => u (fiberDilationCoordinates n R (y, w))) z =
      ((R : ℂ) ^ 2) • modelHessian
        (fun y => u ((complexProductCoordinates n 1).symm (y, complexCoordinates 1 w)))
        (R • complexCoordinates n z) := by
  let L := fiberDilationCoordinates n R
  let e := complexProductCoordinates n 1
  have hSmooth : ContDiff ℝ ∞ (u ∘ L) := hu.comp L.contDiff
  have hBlock := complexProductHessian_fiber (n := n) (m := 1)
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (L (z, w))
  have hCoord : e (L (z, w)) = (R • complexCoordinates n z, complexCoordinates 1 w) :=
    e.apply_symm_apply _
  ext i j : 1
  have h := congrFun (congrFun (productComplexHessian_fiberDilationCoordinates hu R z w)
    (Sum.inl i : Fin n ⊕ Fin 1)) (Sum.inl j : Fin n ⊕ Fin 1)
  change MoserTrudinger.productComplexHessian (u ∘ L) z w (Sum.inl i) (Sum.inl j) = _ at h
  rw [MoserTrudinger.productComplexHessian_fiber hSmooth] at h
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, fiberCoordinateScale, Sum.elim_inl] at h
  have hB := congrFun (congrFun hBlock i) j
  rw [hCoord] at hB
  change complexProductHessian (n := n) (m := 1) u (L (z, w)) (Sum.inl i) (Sum.inl j) =
    modelHessian (fun y => u (e.symm (y, complexCoordinates 1 w))) (R • complexCoordinates n z) i j at hB
  rw [hB] at h
  calc
    _ = (R : ℂ) * modelHessian (fun y => u (e.symm (y, complexCoordinates 1 w)))
          (R • complexCoordinates n z) i j * (R : ℂ) := by
      simpa only [Function.comp_apply, L] using h
    _ = _ := by
      rw [Matrix.smul_apply, smul_eq_mul]
      dsimp only [e]
      ring

theorem productComplexHessian_det_fiberDilationCoordinates {n : ℕ}
    {u : ComplexModel (n + 1) → ℝ} (hu : ContDiff ℝ ∞ u) (R : ℝ) (z : E n) (w : E 1) :
    (MoserTrudinger.productComplexHessian (u ∘ fiberDilationCoordinates n R) z w).det.re =
      R ^ (2 * n) * (modelHessian u (fiberDilationCoordinates n R (z, w))).det.re := by
  have hprod : (∏ i : Fin n ⊕ Fin 1, (fiberCoordinateScale R i : ℂ)) = (R : ℂ) ^ n := by
    rw [Fintype.prod_sum_type]
    simp [fiberCoordinateScale]
  rw [productComplexHessian_fiberDilationCoordinates hu, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, hprod, complexProductHessian_det]
  have he (t : ℂ) : (R : ℂ) ^ n * t * (R : ℂ) ^ n = (R : ℂ) ^ (2 * n) * t := by
    rw [pow_mul]
    ring
  rw [he, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

end KEBall.BedfordTaylor
