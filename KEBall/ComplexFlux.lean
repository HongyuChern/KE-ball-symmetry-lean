import KEBall.BallGreenLocal
import KEBall.EquationCofactor
import KEBall.EquationBasics
import KEBall.RadialCoordinates

/-!
# The actual complex cofactor vector field and its real boundary flux

Complex coordinate fields are reconstructed in the fixed interleaved real
Euclidean basis. The real divergence is twice the real part of the Wirtinger
divergence. The cofactor field uses the manuscript's transposed adjugate entry.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall
open KEBallProbe

noncomputable def complexVectorReal {n : ℕ} (z : Fin n → ℂ) : E n :=
  ∑ i : Fin n, ((z i).re • realDirection i + (z i).im • imagDirection i)

@[simp] theorem complexVectorReal_realIndex {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    complexVectorReal z (realIndex i) = (z i).re := by
  simp [complexVectorReal, realDirection, imagDirection, Pi.single_apply]

@[simp] theorem complexVectorReal_imagIndex {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    complexVectorReal z (imagIndex i) = (z i).im := by
  simp [complexVectorReal, realDirection, imagDirection, Pi.single_apply]

theorem inner_complexVectorReal {n : ℕ} (x : E n) (z : Fin n → ℂ) :
    inner ℝ x (complexVectorReal z) =
      (∑ i : Fin n, star (complexCoord x i) * z i).re := by
  simp only [complexVectorReal, inner_sum, inner_add_right, real_inner_smul_right,
    realDirection, imagDirection, EuclideanSpace.inner_single_right, conj_trivial,
    one_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [complexCoord, Complex.mul_re, Complex.mul_im]
  ring

theorem complexVectorReal_contDiffOn {n : ℕ} {U : Set (E n)}
    {F : E n → Fin n → ℂ} (hF : ∀ i, ContDiffOn ℝ ∞ (fun x => F x i) U) :
    ContDiffOn ℝ ∞ (fun x => complexVectorReal (F x)) U := by
  unfold complexVectorReal
  apply ContDiffOn.sum
  intro i hi
  exact ((Complex.reCLM.contDiff.comp_contDiffOn (hF i)).smul contDiffOn_const).add
    ((Complex.imCLM.contDiff.comp_contDiffOn (hF i)).smul contDiffOn_const)

theorem euclideanDivergence_complexVectorReal {n : ℕ} {F : E n → Fin n → ℂ} {x : E n}
    (hF : ∀ i, DifferentiableAt ℝ (fun y => F y i) x) :
    euclideanDivergence (fun y => complexVectorReal (F y)) x =
      2 * (∑ i : Fin n, partialZ i (fun y => F y i) x).re := by
  have hre (i : Fin n) :
      fderiv ℝ (fun y => (F y i).re) x (realDirection i) =
        (rd (realDirection i) (fun y => F y i) x).re := by
    have h := Complex.reCLM.hasFDerivAt.comp x (hF i).hasFDerivAt
    change HasFDerivAt (fun y => (F y i).re) _ x at h
    rw [h.fderiv]
    rfl
  have him (i : Fin n) :
      fderiv ℝ (fun y => (F y i).im) x (imagDirection i) =
        (rd (imagDirection i) (fun y => F y i) x).im := by
    have h := Complex.imCLM.hasFDerivAt.comp x (hF i).hasFDerivAt
    change HasFDerivAt (fun y => (F y i).im) _ x at h
    rw [h.fderiv]
    rfl
  have hsum : (∑ i : Fin n,
      (fderiv ℝ (fun y => (F y i).re) x (realDirection i) +
       fderiv ℝ (fun y => (F y i).im) x (imagDirection i))) =
      2 * (∑ i : Fin n, partialZ i (fun y => F y i) x).re := by
    simp only [hre, him, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [partialZ, dz, Complex.mul_re, Complex.mul_im]
  unfold euclideanDivergence
  rw [← (interleavedEquiv n).sum_comp]
  simpa only [Fintype.sum_prod_type, Fin.sum_univ_two, interleavedEquiv_zero,
    interleavedEquiv_one, complexVectorReal_realIndex, complexVectorReal_imagIndex,
    EuclideanSpace.basisFun_apply, realDirection, imagDirection] using hsum

theorem matrixField_det_contDiffOn {n : ℕ} {U : Set (E n)}
    {A : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) U := by
  simp_rw [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ hσ
  exact contDiffOn_const.mul (contDiffOn_prod (fun i hi => hA (σ i) i))

theorem matrixField_adjugate_contDiffOn {n : ℕ} {U : Set (E n)}
    {A : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => (A x).adjugate i j) U := by
  simp_rw [Matrix.adjugate_apply]
  apply matrixField_det_contDiffOn
  intro r k
  by_cases hr : r = j
  · subst r
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simpa only [Matrix.updateRow_ne hr] using hA r k

noncomputable def cofactorVectorField {n : ℕ} (u h : E n → ℝ)
    (x : E n) (i : Fin n) : ℂ :=
  ∑ j : Fin n, (complexHessian u x).adjugate j i *
    partialBar j (fun y => (h y : ℂ)) x

noncomputable def cofactorRealField {n : ℕ} (u h : E n → ℝ) (x : E n) : E n :=
  complexVectorReal (cofactorVectorField u h x)

theorem cofactorVectorField_contDiffOn {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {u h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun x => cofactorVectorField u h x i) U := by
  unfold cofactorVectorField
  apply ContDiffOn.sum
  intro j hj
  apply (matrixField_adjugate_contDiffOn (complexHessian_contDiffOn hU hu) j i).mul
  exact smoothOn_dz hU (Complex.ofRealCLM.contDiff.comp_contDiffOn hh)
    (realDirection j) (-imagDirection j)

theorem cofactorRealField_contDiffOn {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {u h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U) :
    ContDiffOn ℝ ∞ (cofactorRealField u h) U :=
  complexVectorReal_contDiffOn (cofactorVectorField_contDiffOn hU hu hh)

theorem cofactorVectorField_differentiableAt {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hh : ContDiffAt ℝ ∞ h x) (i : Fin n) :
    DifferentiableAt ℝ (fun y => cofactorVectorField u h y i) x := by
  have huc : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have hhc : ContDiffAt ℝ ∞ (fun y => (h y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hh
  have hA (r s : Fin n) : DifferentiableAt ℝ (fun y => complexHessian u y r s) x :=
    (smoothAt_dz (smoothAt_dz huc (realDirection s) (-imagDirection s))
      (realDirection r) (imagDirection r)).differentiableAt (by simp)
  apply DifferentiableAt.fun_sum
  intro j hj
  exact (field_adjugate_differentiableAt hA j i).fun_mul
    ((smoothAt_dz hhc (realDirection j) (-imagDirection j)).differentiableAt (by simp))

theorem sum_partialZ_cofactorVectorField_of_piola {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hh : ContDiffAt ℝ ∞ h x)
    (hpiola : ∀ j : Fin n,
      (∑ i : Fin n, partialZ i (fun y => (complexHessian u y).adjugate j i) x) = 0) :
    (∑ i : Fin n, partialZ i (fun y => cofactorVectorField u h y i) x) =
      ∑ i : Fin n, ∑ j : Fin n,
        (complexHessian u x).adjugate j i * complexHessian h x i j := by
  have huc : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have hhc : ContDiffAt ℝ ∞ (fun y => (h y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hh
  have hA (r s : Fin n) : DifferentiableAt ℝ (fun y => complexHessian u y r s) x :=
    (smoothAt_dz (smoothAt_dz huc (realDirection s) (-imagDirection s))
      (realDirection r) (imagDirection r)).differentiableAt (by simp)
  have hC := field_adjugate_differentiableAt hA
  have hbar (j : Fin n) : DifferentiableAt ℝ (partialBar j (fun y => (h y : ℂ))) x :=
    (smoothAt_dz hhc (realDirection j) (-imagDirection j)).differentiableAt (by simp)
  have hprod (i : Fin n) : partialZ i (fun y => cofactorVectorField u h y i) x =
      ∑ j : Fin n,
        (partialZ i (fun y => (complexHessian u y).adjugate j i) x *
          partialBar j (fun y => (h y : ℂ)) x +
        (complexHessian u x).adjugate j i * complexHessian h x i j) := by
    change dz (realDirection i) (imagDirection i)
      (fun y => ∑ j : Fin n, (complexHessian u y).adjugate j i *
        partialBar j (fun z => (h z : ℂ)) y) x = _
    rw [dz_sum_differentiableAt
      (f := fun j y => (complexHessian u y).adjugate j i *
        partialBar j (fun z => (h z : ℂ)) y)
      (fun j => (hC j i).fun_mul (hbar j))]
    apply Finset.sum_congr rfl
    intro j hj
    exact dz_mul_differentiableAt (hC j i) (hbar j) (realDirection i) (imagDirection i)
  have hzero : (∑ i : Fin n, ∑ j : Fin n,
      partialZ i (fun y => (complexHessian u y).adjugate j i) x *
        partialBar j (fun y => (h y : ℂ)) x) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_mul, hpiola j, zero_mul]
  simp_rw [hprod, Finset.sum_add_distrib]
  rw [hzero, zero_add]

theorem cofactorRealField_divergence_of_piola {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hh : ContDiffAt ℝ ∞ h x)
    (hpiola : ∀ j : Fin n,
      (∑ i : Fin n, partialZ i (fun y => (complexHessian u y).adjugate j i) x) = 0) :
    euclideanDivergence (cofactorRealField u h) x =
      2 * (∑ i : Fin n, ∑ j : Fin n,
        (complexHessian u x).adjugate j i * complexHessian h x i j).re := by
  change euclideanDivergence (fun y => complexVectorReal (cofactorVectorField u h y)) x = _
  rw [euclideanDivergence_complexVectorReal
    (cofactorVectorField_differentiableAt hu hh),
    sum_partialZ_cofactorVectorField_of_piola hu hh hpiola]

theorem adjugate_contraction_eq_det_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hunit : IsUnit A.det) :
    (∑ i : Fin n, ∑ j : Fin n, A.adjugate j i * B i j) =
      A.det * (∑ i : Fin n, ∑ j : Fin n, A⁻¹ j i * B i j) := by
  have hA : A.det • A⁻¹ = A.adjugate := by
    rw [A.nonsing_inv_apply hunit, smul_smul, hunit.mul_val_inv, one_smul]
  rw [← hA]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem IsSolution.cofactorRealField_divergence {n : ℕ} {μ : ℝ} {u h : E n → ℝ}
    (hu : IsSolution n μ u) (hh : SmoothNear (closedUnitBall n) h)
    {x : E n} (hx : x ∈ unitBall n) :
    euclideanDivergence (cofactorRealField u h) x =
      2 * (complexHessian u x).det.re * complexLaplacian u h x := by
  have hxclosed : x ∈ closedUnitBall n := Metric.ball_subset_closedBall hx
  rw [cofactorRealField_divergence_of_piola (hu.2.1.contDiffAt hxclosed)
    (hh.contDiffAt hxclosed) (hu.cofactor_divergence hx),
    adjugate_contraction_eq_det_mul _ _ (hu.det_isUnit_closedBall hxclosed)]
  rw [hu.2.2.2.1 x hx]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    complexLaplacian, inverseCoefficient, mul_assoc]

/-- The pre-unitary-coordinate boundary flux of Lemma 2.1, on the actual
solution class and for every real test smooth near the closed ball. -/
theorem IsSolution.cofactorGreen {n : ℕ} (hn : 0 < n) {μ : ℝ} {u h : E n → ℝ}
    (hu : IsSolution n μ u) (hh : SmoothNear (closedUnitBall n) h) :
    (∫ x in unitBall n, complexLaplacian u h x * (complexHessian u x).det.re ∂volume0 n) =
      (n : ℝ) * ∫ θ : Sphere n,
        (∑ i : Fin n, ∑ j : Fin n,
          star (complexCoord θ.1 i) * (complexHessian u θ.1).adjugate j i *
            partialBar j (fun y => (h y : ℂ)) θ.1).re ∂sphere0 n := by
  have hdiv (x : E n) (hx : x ∈ unitBall n) := hu.cofactorRealField_divergence hh hx
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  obtain ⟨T, hT, hKT, hhT⟩ := hh
  have hF : ContDiffOn ℝ 1 (cofactorRealField u h) (U ∩ T) :=
    (cofactorRealField_contDiffOn (hU.inter hT) (huU.mono inter_subset_left)
      (hhT.mono inter_subset_right)).of_le (by simp)
  have hGreen := integral_unitBall_divergence_normalized_of_contDiffOn hn (hU.inter hT)
    (fun x hx => ⟨hKU hx, hKT hx⟩) hF
  have hvol : (∫ x in unitBall n, euclideanDivergence (cofactorRealField u h) x ∂volume0 n) =
      2 * (∫ x in unitBall n, complexLaplacian u h x * (complexHessian u x).det.re ∂volume0 n) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x hx
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hdiv x hx
  have hsurf :
      (∫ θ : Sphere n, inner ℝ θ.1 (cofactorRealField u h θ.1) ∂sphere0 n) =
      ∫ θ : Sphere n,
        (∑ i : Fin n, ∑ j : Fin n,
          star (complexCoord θ.1 i) * (complexHessian u θ.1).adjugate j i *
            partialBar j (fun y => (h y : ℂ)) θ.1).re ∂sphere0 n := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro θ
    change inner ℝ θ.1 (complexVectorReal (cofactorVectorField u h θ.1)) = _
    rw [inner_complexVectorReal]
    simp only [cofactorVectorField, Finset.mul_sum, mul_assoc]
  rw [hvol, hsurf] at hGreen
  linarith

#print axioms euclideanDivergence_complexVectorReal
#print axioms inner_complexVectorReal
#print axioms cofactorRealField_contDiffOn
#print axioms sum_partialZ_cofactorVectorField_of_piola
#print axioms IsSolution.cofactorRealField_divergence
#print axioms IsSolution.cofactorGreen

end KEBall
