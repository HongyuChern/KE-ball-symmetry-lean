import Drafts.KEBall.AuxiliaryPPositivity
import Drafts.KEBall.AuxiliaryPDifferential
import KEBall.ComplexFlux

/-!
# Closed-ball neighbourhood regularity of q, P and W

SOURCE_DRAFT_UNCOMPILED: this file has not passed the pinned Lean kernel.
All regularity conclusions below concern the actual frozen definitions.
The determinant and adjugate are smooth polynomial expressions; their quotient
represents the actual inverse wherever the determinant is nonzero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall
open KEBallProbe

namespace AuxiliaryPRegularity

/-- Relative continuity on an open domain gives an open restricted preimage. -/
theorem isOpen_domain_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {U : Set X} {V : Set Y} {f : X → Y}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContinuousOn f U) :
    IsOpen (U ∩ f ⁻¹' V) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hfAt : ContinuousAt f x :=
    (hf x hx.1).continuousAt (hU.mem_nhds hx.1)
  filter_upwards [hU.mem_nhds hx.1,
    hfAt.tendsto.eventually (hV.mem_nhds hx.2)] with y hyU hyV
  exact ⟨hyU, hyV⟩

/-- The existing nonsingular-inverse identity fixes the transpose convention
before any differentiation or smoothness argument. -/
theorem inverse_entry_eq_adjugate_div_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hd : A.det ≠ 0) (i j : Fin n) :
    A⁻¹ i j = A.adjugate i j / A.det := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hd
  have hA : A.det • A⁻¹ = A.adjugate := by
    rw [A.nonsing_inv_apply hunit, smul_smul, hunit.mul_val_inv, one_smul]
  have he := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ => B i j) hA
  apply (eq_div_iff hd).mpr
  simpa only [Matrix.smul_apply, smul_eq_mul, mul_comm] using he

/-- Each entry of the actual matrix inverse is smooth on a set on which the
actual determinant does not vanish. No inverse regularity is postulated. -/
theorem matrixField_inverse_entry_contDiffOn {n : ℕ} {U : Set (E n)}
    {A : E n → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hd : ∀ x ∈ U, (A x).det ≠ 0) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => (A x)⁻¹ i j) U := by
  have hquot : ContDiffOn ℝ ∞
      (fun x => (A x).adjugate i j / (A x).det) U := by
    simpa +instances only [div_eq_mul_inv, Pi.inv_apply] using!
      (matrixField_adjugate_contDiffOn hA i j).mul
        ((matrixField_det_contDiffOn hA).inv hd)
  apply hquot.congr
  intro x hx
  first
  | exact inverse_entry_eq_adjugate_div_det (A x) (hd x hx) i j
  | exact (inverse_entry_eq_adjugate_div_det (A x) (hd x hx) i j).symm

end AuxiliaryPRegularity

/-- Coordinate proof of q-smoothness, valid on any open nonsingular domain. -/
theorem gradientNormSq_contDiffOn_of_det_ne_zero {n : ℕ} {U : Set (E n)}
    (hU : IsOpen U) {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hd : ∀ x ∈ U, (complexHessian u x).det ≠ 0) :
    ContDiffOn ℝ ∞ (gradientNormSq u) U := by
  have huC : ContDiffOn ℝ ∞ (fun y => (u y : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hu
  have hInv (i j : Fin n) :
      ContDiffOn ℝ ∞ (fun x => inverseCoefficient u x i j) U :=
    AuxiliaryPRegularity.matrixField_inverse_entry_contDiffOn
      (complexHessian_contDiffOn hU hu) hd j i
  have hsum : ContDiffOn ℝ ∞
      (fun x => ∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        partialZ i (fun y => (u y : ℂ)) x *
        partialBar j (fun y => (u y : ℂ)) x) U := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact ((hInv i j).mul
      (smoothOn_dz hU huC (realDirection i) (imagDirection i))).mul
      (smoothOn_dz hU huC (realDirection j) (-imagDirection j))
  exact Complex.reCLM.contDiff.comp_contDiffOn hsum

/-- A genuine open neighbourhood is constructed by removing determinant zeros
from the open neighbourhood in the original solution definition. -/
theorem IsSolution.gradientNormSq_smoothNear {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    SmoothNear (closedUnitBall n) (gradientNormSq u) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  let V : Set (E n) := U ∩ {x | (complexHessian u x).det ≠ 0}
  have hnz : IsOpen {z : ℂ | z ≠ 0} := by
    change IsOpen (({0} : Set ℂ)ᶜ)
    exact isClosed_singleton.isOpen_compl
  have hV : IsOpen V :=
    AuxiliaryPRegularity.isOpen_domain_preimage hU hnz
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU huU)).continuousOn
  have hKV : closedUnitBall n ⊆ V := by
    intro x hx
    exact ⟨hKU hx, isUnit_iff_ne_zero.mp (hu.det_isUnit_closedBall hx)⟩
  refine ⟨V, hV, hKV, ?_⟩
  exact gradientNormSq_contDiffOn_of_det_ne_zero hV
    (huU.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)

theorem IsSolution.gradientNormSq_contDiffAt_closedBall {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) : ContDiffAt ℝ ∞ (gradientNormSq u) x :=
  hu.gradientNormSq_smoothNear.contDiffAt hx

/-- The actual P is smooth near the closed ball, rather than merely smooth
on its interior. The ambient total potential need not be globally smooth. -/
theorem IsSolution.auxiliaryP_smoothNear {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    SmoothNear (closedUnitBall n) (auxiliaryP u) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  obtain ⟨V, hV, hKV, hqV⟩ := hu.gradientNormSq_smoothNear
  refine ⟨U ∩ V, hU.inter hV, fun x hx => ⟨hKU hx, hKV hx⟩, ?_⟩
  have huUV : ContDiffOn ℝ ∞ u (U ∩ V) := huU.mono inter_subset_left
  have hqUV : ContDiffOn ℝ ∞ (gradientNormSq u) (U ∩ V) :=
    hqV.mono inter_subset_right
  have hE : ContDiffOn ℝ ∞ (expWeight u) (U ∩ V) :=
    (huUV.neg.div_const (n + 1 : ℝ)).exp
  exact hE.mul (contDiffOn_const.add (hqUV.div_const (n + 1 : ℝ)))

theorem IsSolution.auxiliaryP_contDiffAt_closedBall {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) : ContDiffAt ℝ ∞ (auxiliaryP u) x :=
  hu.auxiliaryP_smoothNear.contDiffAt hx

/-- Compactness upgrades pointwise positivity to a genuine uniform positive
gap for the fixed solution. No uniformity across different solutions is asserted. -/
theorem IsSolution.auxiliaryP_uniform_gap {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closedUnitBall n, δ ≤ auxiliaryP u x - 1 := by
  have hPcont : ContinuousOn (auxiliaryP u) (closedUnitBall n) :=
    fun x hx => (hu.auxiliaryP_contDiffAt_closedBall hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun x => auxiliaryP u x - 1) (closedUnitBall n) :=
    hPcont.sub continuousOn_const
  have hnonempty : (closedUnitBall n).Nonempty :=
    ⟨0, by simp [closedUnitBall]⟩
  obtain ⟨p, hp, hpmin⟩ :=
    (isCompact_closedBall (0 : E n) 1).exists_isMinOn hnonempty hcont
  exact ⟨auxiliaryP u p - 1, hu.auxiliaryP_sub_one_pos_closedBall hn hp,
    fun x hx => hpmin hx⟩

/-- The logarithm is formed on a real open neighbourhood on which P-1>0.
This is the regularity required for the actual boundary Green formula. -/
theorem IsSolution.auxiliaryW_smoothNear {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) :
    SmoothNear (closedUnitBall n) (auxiliaryW u) := by
  obtain ⟨U, hU, hKU, hPU⟩ := hu.auxiliaryP_smoothNear
  let V : Set (E n) := U ∩ {x | 1 < auxiliaryP u x}
  have hV : IsOpen V :=
    AuxiliaryPRegularity.isOpen_domain_preimage hU isOpen_Ioi hPU.continuousOn
  have hKV : closedUnitBall n ⊆ V := by
    intro x hx
    exact ⟨hKU hx, hu.auxiliaryP_gt_one_closedBall hn hx⟩
  refine ⟨V, hV, hKV, ?_⟩
  have hPV : ContDiffOn ℝ ∞ (auxiliaryP u) V := hPU.mono (fun _ hx => hx.1)
  exact (hPV.sub contDiffOn_const).log
    (fun x hx => ne_of_gt (sub_pos.mpr hx.2))

theorem IsSolution.auxiliaryW_contDiffAt_closedBall {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ closedUnitBall n) : ContDiffAt ℝ ∞ (auxiliaryW u) x :=
  (hu.auxiliaryW_smoothNear hn).contDiffAt hx

#print axioms IsSolution.gradientNormSq_smoothNear
#print axioms IsSolution.auxiliaryP_smoothNear
#print axioms IsSolution.auxiliaryP_uniform_gap
#print axioms IsSolution.auxiliaryW_smoothNear

end KEBall
