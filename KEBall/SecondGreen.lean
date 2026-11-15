import KEBall.BoundaryConormal

/-!
# The second Green identity with the actual cofactor field

The two interior gradient terms cancel by the proved Hermitian adjugate.
No boundary condition is imposed on either test function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators ComplexOrder

namespace KEBall

theorem euclideanDivergence_smul {n : ℕ} {f : E n → ℝ} {V : E n → E n}
    {x : E n} (hf : DifferentiableAt ℝ f x) (hV : DifferentiableAt ℝ V x) :
    euclideanDivergence (fun y => f y • V y) x =
      f x * euclideanDivergence V x + fderiv ℝ f x (V x) := by
  have hc (i : Fin (2 * n)) : DifferentiableAt ℝ (fun y => V y i) x :=
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).differentiableAt.comp x hV
  have he (i : Fin (2 * n)) :
      fderiv ℝ (fun y : E n => (f y • V y) i) x
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) =
      f x * fderiv ℝ (fun y => V y i) x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) +
        V x i * fderiv ℝ f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) := by
    change fderiv ℝ (fun y => f y * V y i) x _ = _
    rw [fderiv_fun_mul hf (hc i)]
    simp
  have hre : (∑ i : Fin (2 * n),
      V x i • EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) = V x := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).sum_repr (V x)
  have hs : (∑ i : Fin (2 * n),
      V x i * fderiv ℝ f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) =
      fderiv ℝ f x (V x) := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg (fderiv ℝ f x) hre
  simp only [euclideanDivergence, he, Finset.sum_add_distrib, ← Finset.mul_sum, hs]

theorem euclideanDivergence_sub {n : ℕ} {V W : E n → E n} {x : E n}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    euclideanDivergence (fun y => V y - W y) x =
      euclideanDivergence V x - euclideanDivergence W x := by
  have he (i : Fin (2 * n)) :
      fderiv ℝ (fun y : E n => (V y - W y) i) x =
        fderiv ℝ (fun y => V y i) x - fderiv ℝ (fun y => W y i) x := by
    change fderiv ℝ (fun y => V y i - W y i) x = _
    exact fderiv_fun_sub
      ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).differentiableAt.comp x hV)
      ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).differentiableAt.comp x hW)
  simp only [euclideanDivergence, he, sub_apply, Finset.sum_sub_distrib]

theorem hermitian_contraction_re_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (p q : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, A j i * p i * star (q j)).re =
      (∑ i : Fin n, ∑ j : Fin n, A j i * q i * star (p j)).re := by
  have he : (∑ i : Fin n, ∑ j : Fin n, A j i * p i * star (q j)) =
      star (∑ i : Fin n, ∑ j : Fin n, A j i * q i * star (p j)) := by
    simp only [star_sum, star_mul, star_star]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hA.apply j i]
    ring
  rw [he, Complex.star_def, Complex.conj_re]

theorem cofactor_gradient_pairing_symm {n : ℕ} {u v h : E n → ℝ} {x : E n}
    (hH : (complexHessian u x).IsHermitian)
    (hv : DifferentiableAt ℝ v x) (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ v x (cofactorRealField u h x) =
      fderiv ℝ h x (cofactorRealField u v x) := by
  rw [fderiv_eq_wirtinger hv, fderiv_eq_wirtinger hh]
  simp only [cofactorRealField, complexCoord_complexVectorReal, cofactorVectorField,
    Finset.mul_sum, partialBar_ofReal hh, partialBar_ofReal hv]
  congr 1
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    hermitian_contraction_re_symm hH.adjugate
      (fun i => partialZ i (fun y => (v y : ℂ)) x)
      (fun i => partialZ i (fun y => (h y : ℂ)) x)

noncomputable def secondGreenField {n : ℕ} (u v h : E n → ℝ) (x : E n) : E n :=
  v x • cofactorRealField u h x - h x • cofactorRealField u v x

theorem secondGreenField_contDiffOn {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {u v h : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hv : ContDiffOn ℝ ∞ v U) (hh : ContDiffOn ℝ ∞ h U) :
    ContDiffOn ℝ ∞ (secondGreenField u v h) U :=
  (hv.smul (cofactorRealField_contDiffOn hU hu hh)).sub
    (hh.smul (cofactorRealField_contDiffOn hU hu hv))

theorem IsSolution.secondGreenField_divergence {n : ℕ} {μ : ℝ}
    {u v h : E n → ℝ} (hu : IsSolution n μ u)
    (hv : SmoothNear (closedUnitBall n) v) (hh : SmoothNear (closedUnitBall n) h)
    {x : E n} (hx : x ∈ unitBall n) :
    euclideanDivergence (secondGreenField u v h) x =
      2 * ((v x * complexLaplacian u h x - h x * complexLaplacian u v x) *
        (complexHessian u x).det.re) := by
  have hxc : x ∈ closedUnitBall n := Metric.ball_subset_closedBall hx
  have hud := hu.2.1.contDiffAt hxc
  have hvd := (hv.contDiffAt hxc).differentiableAt (by simp)
  have hhd := (hh.contDiffAt hxc).differentiableAt (by simp)
  have hFh : DifferentiableAt ℝ (cofactorRealField u h) x := by
    obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
    obtain ⟨T, hT, hKT, hhT⟩ := hh
    exact ((cofactorRealField_contDiffOn (hU.inter hT)
      (huU.mono inter_subset_left) (hhT.mono inter_subset_right)).contDiffAt
        ((hU.inter hT).mem_nhds ⟨hKU hxc, hKT hxc⟩)).differentiableAt (by simp)
  have hFv : DifferentiableAt ℝ (cofactorRealField u v) x := by
    obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
    obtain ⟨T, hT, hKT, hvT⟩ := hv
    exact ((cofactorRealField_contDiffOn (hU.inter hT)
      (huU.mono inter_subset_left) (hvT.mono inter_subset_right)).contDiffAt
        ((hU.inter hT).mem_nhds ⟨hKU hxc, hKT hxc⟩)).differentiableAt (by simp)
  change euclideanDivergence
    (fun y => v y • cofactorRealField u h y - h y • cofactorRealField u v y) x = _
  rw [euclideanDivergence_sub
    (V := fun y => v y • cofactorRealField u h y)
    (W := fun y => h y • cofactorRealField u v y) (hvd.smul hFh) (hhd.smul hFv),
    euclideanDivergence_smul hvd hFh, euclideanDivergence_smul hhd hFv,
    hu.cofactorRealField_divergence hh hx, hu.cofactorRealField_divergence hv hx,
    cofactor_gradient_pairing_symm (hu.2.2.1 x hx).isHermitian hvd hhd]
  ring

theorem IsSolution.inner_cofactorRealField_boundary {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u h : E n → ℝ} (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n)
    (hh : DifferentiableAt ℝ h x) :
    inner ℝ x (cofactorRealField u h x) =
      (1 / 2 : ℝ) * (boundarySlope u x ^ (n - 1) * conormalDerivative u h x) := by
  rw [cofactorRealField, inner_complexVectorReal]
  simpa only [cofactorVectorField, Finset.mul_sum, mul_assoc] using
    hu.boundary_cofactor_conormal hn hx hh

theorem IsSolution.secondGreen {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u v h : E n → ℝ} (hu : IsSolution n μ u)
    (hv : SmoothNear (closedUnitBall n) v) (hh : SmoothNear (closedUnitBall n) h) :
    (∫ x in unitBall n,
      (v x * complexLaplacian u h x - h x * complexLaplacian u v x) *
        (complexHessian u x).det.re ∂volume0 n) =
      (n : ℝ) / 2 * ∫ x : Sphere n, boundarySlope u x.1 ^ (n - 1) *
        (v x.1 * conormalDerivative u h x.1 - h x.1 * conormalDerivative u v x.1) ∂sphere0 n := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  obtain ⟨T, hT, hKT, hvT⟩ := hv
  obtain ⟨W, hW, hKW, hhW⟩ := hh
  have hsub : closedUnitBall n ⊆ U ∩ T ∩ W := fun x hx => ⟨⟨hKU hx, hKT hx⟩, hKW hx⟩
  have hVF : ContDiffOn ℝ 1 (secondGreenField u v h) (U ∩ T ∩ W) :=
    (secondGreenField_contDiffOn ((hU.inter hT).inter hW)
      (huU.mono (fun _ hx => hx.1.1)) (hvT.mono (fun _ hx => hx.1.2))
      (hhW.mono inter_subset_right)).of_le (by simp)
  have hG := integral_unitBall_divergence_normalized_of_contDiffOn (by omega)
    ((hU.inter hT).inter hW) hsub hVF
  have hvol : (∫ x in unitBall n, euclideanDivergence (secondGreenField u v h) x ∂volume0 n) =
      2 * ∫ x in unitBall n,
        (v x * complexLaplacian u h x - h x * complexLaplacian u v x) *
          (complexHessian u x).det.re ∂volume0 n := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x hx
    exact hu.secondGreenField_divergence ⟨T, hT, hKT, hvT⟩ ⟨W, hW, hKW, hhW⟩ hx
  have hsurf : (∫ x : Sphere n, inner ℝ x.1 (secondGreenField u v h x.1) ∂sphere0 n) =
      (1 / 2 : ℝ) * ∫ x : Sphere n, boundarySlope u x.1 ^ (n - 1) *
        (v x.1 * conormalDerivative u h x.1 - h x.1 * conormalDerivative u v x.1) ∂sphere0 n := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [secondGreenField, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      hu.inner_cofactorRealField_boundary hn x.2
        ((hhW.contDiffAt (hW.mem_nhds (hKW (Metric.sphere_subset_closedBall x.2)))).differentiableAt (by simp)),
      hu.inner_cofactorRealField_boundary hn x.2
        ((hvT.contDiffAt (hT.mem_nhds (hKT (Metric.sphere_subset_closedBall x.2)))).differentiableAt (by simp))]
    ring
  rw [hvol, hsurf] at hG
  nlinarith [hG]

#print axioms euclideanDivergence_smul
#print axioms cofactor_gradient_pairing_symm
#print axioms IsSolution.secondGreenField_divergence
#print axioms IsSolution.secondGreen

end KEBall
