import Drafts.KEBall.HermitianTensorZero
import Drafts.KEBall.AuxiliaryPRegularity
import KEBall.Pohozaev
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The zero-integral equality consequence for the actual logarithmic flux

SOURCE_DRAFT_UNCOMPILED. No Lean kernel is available in this environment.
The final endpoints assume only the original IsSolution, the dimension
bound and the zero integral appearing in the frozen specification.
Continuity, integrability, positivity and full support are proved or
obtained from existing results for the actual functions and volume0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators
noncomputable section

namespace KEBall

/-- The coordinate definition of the actual complex Laplacian is smooth
where the potential and test are smooth and the Hessian is nonsingular. -/
theorem complexLaplacian_contDiffOn_of_det_ne_zero {n : ℕ} {U : Set (E n)}
    (hU : IsOpen U) {u h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hh : ContDiffOn ℝ ∞ h U)
    (hd : ∀ x ∈ U, (complexHessian u x).det ≠ 0) :
    ContDiffOn ℝ ∞ (complexLaplacian u h) U := by
  have hInv (i j : Fin n) :
      ContDiffOn ℝ ∞ (fun x => inverseCoefficient u x i j) U :=
    AuxiliaryPRegularity.matrixField_inverse_entry_contDiffOn
      (complexHessian_contDiffOn hU hu) hd j i
  have hsum : ContDiffOn ℝ ∞
      (fun x => ∑ i : Fin n, ∑ j : Fin n,
        inverseCoefficient u x i j * complexHessian h x i j) U := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (hInv i j).mul (complexHessian_contDiffOn hU hh i j)
  exact Complex.reCLM.contDiff.comp_contDiffOn hsum

/-- Nonsingularity extends to an actual open neighbourhood of the compact
closed ball, so the totalized inverse never introduces a local singularity. -/
theorem IsSolution.complexLaplacian_smoothNear {n : ℕ} {μ : ℝ}
    {u h : E n → ℝ} (hu : IsSolution n μ u)
    (hh : SmoothNear (closedUnitBall n) h) :
    SmoothNear (closedUnitBall n) (complexLaplacian u h) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  obtain ⟨V, hV, hKV, hhV⟩ := hh
  let S : Set (E n) := (U ∩ V) ∩ {x | (complexHessian u x).det ≠ 0}
  have huUV : ContDiffOn ℝ ∞ u (U ∩ V) := huU.mono inter_subset_left
  have hnz : IsOpen {z : ℂ | z ≠ 0} := by
    change IsOpen (({0} : Set ℂ)ᶜ)
    exact isClosed_singleton.isOpen_compl
  have hS : IsOpen S :=
    AuxiliaryPRegularity.isOpen_domain_preimage (hU.inter hV) hnz
      (matrixField_det_contDiffOn
        (complexHessian_contDiffOn (hU.inter hV) huUV)).continuousOn
  have hKS : closedUnitBall n ⊆ S := by
    intro x hx
    exact ⟨⟨hKU hx, hKV hx⟩,
      isUnit_iff_ne_zero.mp (hu.det_isUnit_closedBall hx)⟩
  refine ⟨S, hS, hKS, ?_⟩
  exact complexLaplacian_contDiffOn_of_det_ne_zero hS
    (huU.mono (fun _ hx => hx.1.1))
    (hhV.mono (fun _ hx => hx.1.2)) (fun _ hx => hx.2)

/-- The exact weighted integrand of the Green formula is smooth near the
closed ball. This is an assertion about det(Hess u).re, not a new density. -/
theorem IsSolution.weightedComplexLaplacian_smoothNear {n : ℕ} {μ : ℝ}
    {u h : E n → ℝ} (hu : IsSolution n μ u)
    (hh : SmoothNear (closedUnitBall n) h) :
    SmoothNear (closedUnitBall n)
      (fun x => complexLaplacian u h x * (complexHessian u x).det.re) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  obtain ⟨V, hV, hKV, hLV⟩ := hu.complexLaplacian_smoothNear hh
  refine ⟨U ∩ V, hU.inter hV, fun x hx => ⟨hKU hx, hKV hx⟩, ?_⟩
  have hdU : ContDiffOn ℝ ∞ (fun x => (complexHessian u x).det.re) U :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU huU))
  exact (hLV.mono inter_subset_right).mul (hdU.mono inter_subset_left)

/-- Integrability is a consequence of near-closed-ball smoothness and
compactness for the actual normalized Euclidean volume. -/
theorem IsSolution.weightedComplexLaplacian_integrableOn {n : ℕ} {μ : ℝ}
    {u h : E n → ℝ} (hu : IsSolution n μ u)
    (hh : SmoothNear (closedUnitBall n) h) :
    IntegrableOn
      (fun x => complexLaplacian u h x * (complexHessian u x).det.re)
      (unitBall n) (volume0 n) := by
  obtain ⟨U, _, hKU, hU⟩ := hu.weightedComplexLaplacian_smoothNear hh
  exact integrableOn_unitBall_of_contDiffOn hKU hU

/-- The PDE and positive parameter give a strictly positive real density
throughout the closed ball. -/
theorem IsSolution.det_re_pos_closedBall {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) :
    0 < (complexHessian u x).det.re := by
  rw [hu.det_eq_on_closedBall hx]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using mul_pos hu.1 (Real.exp_pos (-u x))

/-- Open-set full support upgrades almost-everywhere zero to pointwise
zero. The ambient measure, not its restriction, has the full-support instance. -/
theorem unitBall_eq_zero_of_integral_eq_zero {n : ℕ} {f : E n → ℝ}
    (hf : ContinuousOn f (unitBall n))
    (hfi : IntegrableOn f (unitBall n) (volume0 n))
    (hnonneg : ∀ x ∈ unitBall n, 0 ≤ f x)
    (hzero : (∫ x in unitBall n, f x ∂volume0 n) = 0) :
    ∀ x ∈ unitBall n, f x = 0 := by
  have hnonnegAE : 0 ≤ᵐ[(volume0 n).restrict (unitBall n)] f :=
    ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet hnonneg
  have hzeroAE : f =ᵐ[(volume0 n).restrict (unitBall n)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonnegAE hfi).mp hzero
  exact Measure.eqOn_open_of_ae_eq hzeroAE Metric.isOpen_ball hf continuousOn_const

/-- The exact zero integral in Proposition 3.1 forces the actual LW to
vanish at every interior point. No continuity or integrability premise is added. -/
theorem IsSolution.auxiliaryW_laplacian_eq_zero_of_integral_eq_zero {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    (hzero : (∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
      (complexHessian u x).det.re ∂volume0 n) = 0) :
    ∀ x ∈ unitBall n, complexLaplacian u (auxiliaryW u) x = 0 := by
  have hW := hu.auxiliaryW_smoothNear hn
  have hs := hu.weightedComplexLaplacian_smoothNear hW
  have hc : ContinuousOn
      (fun x => complexLaplacian u (auxiliaryW u) x *
        (complexHessian u x).det.re) (unitBall n) := by
    intro x hx
    exact (hs.contDiffAt (Metric.ball_subset_closedBall hx)).continuousAt.continuousWithinAt
  have hi := hu.weightedComplexLaplacian_integrableOn hW
  have hnonneg (x : E n) (hx : x ∈ unitBall n) :
      0 ≤ complexLaplacian u (auxiliaryW u) x * (complexHessian u x).det.re :=
    mul_nonneg (hu.auxiliaryW_laplacian_nonneg hn hx)
      (hu.det_re_pos_closedBall (Metric.ball_subset_closedBall hx)).le
  have hz := unitBall_eq_zero_of_integral_eq_zero hc hi hnonneg hzero
  intro x hx
  exact (mul_eq_zero.mp (hz x hx)).resolve_right
    (ne_of_gt (hu.det_re_pos_closedBall (Metric.ball_subset_closedBall hx)))

/-- The complete equality consequence, with exactly the coordinates and
complex coefficient in the fourth conjunct of LogarithmicFluxStatement. -/
theorem IsSolution.logarithmicFlux_equality_consequence {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    (hzero : (∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
      (complexHessian u x).det.re ∂volume0 n) = 0) :
    ∀ x ∈ unitBall n, ∀ i j : Fin n,
      covariantHessian20 u x i j = (n + 1 : ℂ)⁻¹ *
        partialZ i (fun y => (u y : ℂ)) x * partialZ j (fun y => (u y : ℂ)) x := by
  intro x hx i j
  exact hu.auxiliaryW_zero_forces_hessian_identity hn hx
    (hu.auxiliaryW_laplacian_eq_zero_of_integral_eq_zero hn hzero x hx) i j

#print axioms IsSolution.complexLaplacian_smoothNear
#print axioms IsSolution.weightedComplexLaplacian_integrableOn
#print axioms unitBall_eq_zero_of_integral_eq_zero
#print axioms IsSolution.auxiliaryW_laplacian_eq_zero_of_integral_eq_zero
#print axioms IsSolution.logarithmicFlux_equality_consequence

end KEBall
