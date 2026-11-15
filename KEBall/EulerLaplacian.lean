import KEBall.MetricConnection
import KEBall.EulerFlux

/-!
# The actual linearized equation of the Euler derivative

The Hessian of `Ru = Du(x)` is differentiated as a genuine Frechet
derivative. Third-derivative symmetry gives `H(Ru) = R(Hu) + 2 Hu`.
Jacobi's determinant formula and the original equation then imply
`L(Ru) = 2n - Ru`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall
open KEBallProbe

theorem eulerDerivative_contDiffOn {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (eulerDerivative u) U :=
  (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_id

theorem SmoothNear.eulerDerivative {n : ℕ} {u : E n → ℝ} {K : Set (E n)}
    (hu : SmoothNear K u) : SmoothNear K (KEBall.eulerDerivative u) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu
  exact ⟨U, hU, hKU, eulerDerivative_contDiffOn hU huU⟩

theorem fderiv_eulerDerivative {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v : E n) :
    fderiv ℝ (eulerDerivative u) x v = realHessian u x v x + fderiv ℝ u x v := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have h := hd.clm_apply (hasFDerivAt_id x)
  change HasFDerivAt (eulerDerivative u) _ x at h
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply, id_eq, realHessian]
  ring

theorem fderiv_firstDerivative_apply {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    fderiv ℝ (fun y => fderiv ℝ u y w) x v = realHessian u x v w := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have h := hd.clm_apply (hasFDerivAt_const w x)
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add, realHessian]

theorem realHessian_eulerDerivative {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U) (v w : E n) :
    realHessian (eulerDerivative u) x v w =
      realThirdDerivative u x x v w + 2 * realHessian u x v w := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hRuAt := (eulerDerivative_contDiffOn hU hu).contDiffAt (hU.mem_nhds hx)
  have heq : (fun y => fderiv ℝ (eulerDerivative u) y w) =ᶠ[𝓝 x]
      (fun y => realHessian u y w y + fderiv ℝ u y w) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_eulerDerivative (hu.contDiffAt (hU.mem_nhds hy)) w
  have hB := ((realHessian_contDiffAt huAt).differentiableAt (by simp)).hasFDerivAt
  have hBwy := (hB.clm_apply (hasFDerivAt_const w x)).clm_apply (hasFDerivAt_id x)
  change HasFDerivAt (fun y => realHessian u y w y) _ x at hBwy
  have hdu : DifferentiableAt ℝ (fun y => fderiv ℝ u y w) x :=
    ((huAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hsum := hBwy.add hdu.hasFDerivAt
  change HasFDerivAt (fun y => realHessian u y w y + fderiv ℝ u y w) _ x at hsum
  rw [← fderiv_firstDerivative_apply hRuAt, heq.fderiv_eq, hsum.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply, zero_apply, map_zero, zero_add, id_eq,
    fderiv_firstDerivative_apply huAt]
  change realHessian u x w v + realThirdDerivative u x v w x + realHessian u x v w = _
  rw [realThirdDerivative_symm23 hU hu hx v w x, realThirdDerivative_symm12 huAt v x w,
    realHessian_symm huAt w v]
  ring

theorem fderiv_complexHessian_entry {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (a : E n) (i j : Fin n) :
    fderiv ℝ (fun y => complexHessian u y i j) x a = (4 : ℂ)⁻¹ *
      ((realThirdDerivative u x a (realDirection i) (realDirection j) : ℝ) +
       (realThirdDerivative u x a (imagDirection i) (imagDirection j) : ℝ) +
       Complex.I * ((realThirdDerivative u x a (realDirection i) (imagDirection j) : ℝ) -
         (realThirdDerivative u x a (imagDirection i) (realDirection j) : ℝ))) := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have heq : (fun y => complexHessian u y i j) =ᶠ[𝓝 x] (fun y => (4 : ℂ)⁻¹ *
      ((realHessian u y (realDirection i) (realDirection j) : ℝ) +
       (realHessian u y (imagDirection i) (imagDirection j) : ℝ) +
       Complex.I * ((realHessian u y (realDirection i) (imagDirection j) : ℝ) -
         (realHessian u y (imagDirection i) (realDirection j) : ℝ)))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact complexHessian_real_entry (hu.contDiffAt (hU.mem_nhds hy)) i j
  have hbc (v w : E n) : DifferentiableAt ℝ
      (fun y => (realHessian u y v w : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((((realHessian_contDiffAt huAt).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const).differentiableAt (by simp))
  have hd (v w : E n) : fderiv ℝ (fun y => (realHessian u y v w : ℂ)) x a =
      (realThirdDerivative u x a v w : ℝ) := by
    have hb : DifferentiableAt ℝ (fun y => realHessian u y v w) x :=
      (((realHessian_contDiffAt huAt).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const).differentiableAt (by simp)
    have h := Complex.ofRealCLM.hasFDerivAt.comp x (hb.hasFDerivAt)
    change HasFDerivAt (fun y => (realHessian u y v w : ℂ)) _ x at h
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      fderiv_realHessian_apply huAt]
  rw [heq.fderiv_eq]
  have h1 := (hbc (realDirection i) (realDirection j)).hasFDerivAt.add
    (hbc (imagDirection i) (imagDirection j)).hasFDerivAt
  have h2 := (hbc (realDirection i) (imagDirection j)).hasFDerivAt.sub
    (hbc (imagDirection i) (realDirection j)).hasFDerivAt
  have hfull := (h1.add (h2.const_mul Complex.I)).const_mul ((4 : ℂ)⁻¹)
  change HasFDerivAt (fun y => (4 : ℂ)⁻¹ *
      ((realHessian u y (realDirection i) (realDirection j) : ℝ) +
       (realHessian u y (imagDirection i) (imagDirection j) : ℝ) +
       Complex.I * ((realHessian u y (realDirection i) (imagDirection j) : ℝ) -
         (realHessian u y (imagDirection i) (realDirection j) : ℝ)))) _ x at hfull
  rw [hfull.fderiv]
  simp only [smul_apply, add_apply, sub_apply, smul_eq_mul, hd]

theorem complexHessian_eulerDerivative {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (i j : Fin n) :
    complexHessian (eulerDerivative u) x i j =
      fderiv ℝ (fun y => complexHessian u y i j) x x + 2 * complexHessian u x i j := by
  rw [complexHessian_real_entry
    ((eulerDerivative_contDiffOn hU hu).contDiffAt (hU.mem_nhds hx)),
    fderiv_complexHessian_entry hU hu hx, complexHessian_real_entry (hu.contDiffAt (hU.mem_nhds hx))]
  simp only [realHessian_eulerDerivative hU hu hx]
  push_cast
  ring

theorem IsSolution.euler_hessian_contraction {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
      fderiv ℝ (fun y => complexHessian u y i j) x x) = -(eulerDerivative u x : ℂ) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hxU := hKU (Metric.ball_subset_closedBall hx)
  have huAt := huU.contDiffAt (hU.mem_nhds hxU)
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y => complexHessian u y i j) x :=
    ((complexHessian_contDiffOn hU huU i j).contDiffAt
      (hU.mem_nhds hxU)).differentiableAt (by simp)
  have heq : (fun y => (complexHessian u y).det) =ᶠ[𝓝 x]
      (fun y => (equationDensity μ u y : ℂ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    simpa only [equationDensity, Complex.ofReal_mul] using hu.2.2.2.1 y hy
  have hw : DifferentiableAt ℝ (equationDensity μ u) x :=
    ((equationDensity_contDiffOn μ huU).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hrd : rd x (fun y => (complexHessian u y).det) x =
      -(eulerDerivative u x : ℂ) * (complexHessian u x).det := by
    change fderiv ℝ (fun y => (complexHessian u y).det) x x = _
    rw [heq.fderiv_eq]
    change rd x (fun y => (equationDensity μ u y : ℂ)) x = _
    rw [rd_ofReal hw, eulerDerivative_equationDensity μ (huAt.differentiableAt (by simp)),
      hu.2.2.2.1 x hx]
    simp only [equationDensity]
    push_cast
    ring
  have hunit := hu.det_isUnit_closedBall (Metric.ball_subset_closedBall hx)
  have hc : (complexHessian u x).det *
      (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        fderiv ℝ (fun y => complexHessian u y i j) x x) =
      -(eulerDerivative u x : ℂ) * (complexHessian u x).det := by
    rw [show (complexHessian u x).det *
        (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
          fderiv ℝ (fun y => complexHessian u y i j) x x) =
        ∑ i : Fin n, ∑ j : Fin n, (complexHessian u x).adjugate j i *
          rd x (fun y => complexHessian u y i j) x by
      exact (adjugate_contraction_eq_det_mul (complexHessian u x)
        (fun i j => fderiv ℝ (fun y => complexHessian u y i j) x x) hunit).symm]
    rw [← rd_det_field hG x, hrd]
  apply mul_left_cancel₀ (isUnit_iff_ne_zero.mp hunit)
  simpa only [mul_comm] using hc

theorem IsSolution.complexLaplacian_eulerDerivative {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitBall n) :
    complexLaplacian u (eulerDerivative u) x = (2 * n : ℝ) - eulerDerivative u x := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  have hxU := hKU (Metric.ball_subset_closedBall hx)
  have hs : (∑ i : Fin n, ∑ j : Fin n,
      inverseCoefficient u x i j * complexHessian (eulerDerivative u) x i j) =
      (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        fderiv ℝ (fun y => complexHessian u y i j) x x) +
      2 * (∑ i : Fin n, ∑ j : Fin n,
        inverseCoefficient u x i j * complexHessian u x i j) := by
    simp only [complexHessian_eulerDerivative hU huU hxU, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [complexLaplacian, hs, hu.euler_hessian_contraction hx]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    show (2 : ℂ).re = 2 by rfl, show (2 : ℂ).im = 0 by rfl, zero_mul, sub_zero]
  change -eulerDerivative u x + 2 * complexLaplacian u u x = _
  rw [hu.complexLaplacian_self (Metric.ball_subset_closedBall hx)]
  ring

#print axioms realHessian_eulerDerivative
#print axioms fderiv_complexHessian_entry
#print axioms complexHessian_eulerDerivative
#print axioms IsSolution.euler_hessian_contraction
#print axioms IsSolution.complexLaplacian_eulerDerivative

end KEBall
