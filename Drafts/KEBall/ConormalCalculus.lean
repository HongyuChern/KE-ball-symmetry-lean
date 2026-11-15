import Drafts.KEBall.AuxiliaryPRegularity
import KEBall.HorizontalPower
import KEBall.BoundaryMass

/-!
# The actual conormal as a directional derivative and its first-order rules

SOURCE_DRAFT_UNCOMPILED: no declaration is claimed to have passed Lean.
The conormal is the frozen operator of `KEBall.Specification`.  Its vector
representation is proved from the actual horizontal projection, not assumed.
The boundary identity for q is differentiated only in sphere-tangent
 directions; no normal derivative of a sphere-only identity is taken.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff BigOperators RealInnerProductSpace

namespace KEBall

/-- On the sphere the frozen conormal is a genuine first-order directional
operator. This identity does not require differentiability because every
`fderiv` is a continuous linear map, including its totalized value. -/
theorem conormalDerivative_eq_fderiv_direction {n : ℕ} (u h : E n → ℝ)
    {x : E n} (hx : x ∈ unitSphere n) :
    conormalDerivative u h x = fderiv ℝ h x
      (x - (2 * boundarySlope u x)⁻¹ • horizontalGradient (boundarySlope u) x) := by
  have hi : inner ℝ (horizontalGradient (boundarySlope u) x)
      (horizontalGradient h x) =
      fderiv ℝ h x (horizontalGradient (boundarySlope u) x) := by
    rw [real_inner_comm]
    exact inner_horizontalGradient h
      (horizontalGradient_inner_normal _ hx) (horizontalGradient_inner_hopf _ hx)
  simp only [conormalDerivative, hi, map_sub, map_smul, smul_eq_mul, div_eq_mul_inv]
  ring

theorem conormalDerivative_mul {n : ℕ} (u : E n → ℝ) {h k : E n → ℝ}
    {x : E n} (hx : x ∈ unitSphere n)
    (hh : DifferentiableAt ℝ h x) (hk : DifferentiableAt ℝ k x) :
    conormalDerivative u (fun y => h y * k y) x =
      h x * conormalDerivative u k x + k x * conormalDerivative u h x := by
  simp only [conormalDerivative_eq_fderiv_direction u _ hx,
    fderiv_fun_mul hh hk, _root_.add_apply, smul_apply, smul_eq_mul]

theorem conormalDerivative_const_add_const_mul {n : ℕ} (u : E n → ℝ)
    {h : E n → ℝ} {x : E n} (hx : x ∈ unitSphere n)
    (hh : DifferentiableAt ℝ h x) (a c : ℝ) :
    conormalDerivative u (fun y => a + c * h y) x =
      c * conormalDerivative u h x := by
  rw [conormalDerivative_eq_fderiv_direction u _ hx,
    conormalDerivative_eq_fderiv_direction u h hx,
    ((hh.hasFDerivAt.const_mul c).const_add a).fderiv]
  simp only [smul_apply, smul_eq_mul]

theorem conormalDerivative_sub_const {n : ℕ} (u : E n → ℝ)
    {h : E n → ℝ} {x : E n} (hx : x ∈ unitSphere n)
    (hh : DifferentiableAt ℝ h x) (c : ℝ) :
    conormalDerivative u (fun y => h y - c) x = conormalDerivative u h x := by
  rw [conormalDerivative_eq_fderiv_direction u _ hx,
    conormalDerivative_eq_fderiv_direction u h hx,
    (hh.hasFDerivAt.sub_const c).fderiv]

theorem conormalDerivative_log {n : ℕ} (u : E n → ℝ)
    {h : E n → ℝ} {x : E n} (hx : x ∈ unitSphere n)
    (hh : DifferentiableAt ℝ h x) (hne : h x ≠ 0) :
    conormalDerivative u (fun y => Real.log (h y)) x =
      conormalDerivative u h x / h x := by
  rw [conormalDerivative_eq_fderiv_direction u _ hx,
    conormalDerivative_eq_fderiv_direction u h hx,
    (hh.hasFDerivAt.log hne).fderiv]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem conormalDerivative_expWeight {n : ℕ} {u : E n → ℝ}
    {x : E n} (hx : x ∈ unitSphere n) (hu : DifferentiableAt ℝ u x) :
    conormalDerivative u (expWeight u) x =
      -(expWeight u x / (n + 1 : ℝ)) * conormalDerivative u u x := by
  rw [conormalDerivative_eq_fderiv_direction u _ hx,
    conormalDerivative_eq_fderiv_direction u u hx]
  rw [AuxiliaryPDifferential.expWeight_eq_exp_const_mul]
  rw [AuxiliaryPDifferential.fderiv_exp_const_mul_apply hu]
  ring

/-- The boundary value of the weight and the actual conormal self-derivative
fix its complete conormal derivative. -/
theorem IsSolution.conormalDerivative_expWeight_on_sphere {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    conormalDerivative u (expWeight u) x = -2 * boundarySlope u x / (n + 1 : ℝ) := by
  have hud := (hu.2.1.contDiffAt
    (Metric.sphere_subset_closedBall hx)).differentiableAt (by simp)
  rw [conormalDerivative_expWeight hx hud,
    sphere_conormal_self hu.2.1 hu.2.2.2.2 hx]
  have hE : expWeight u x = 1 := by
    simp [expWeight, hu.2.2.2.2 x hx]
  rw [hE]
  ring

/-- First-order product rule for the actual P. No formula for the normal
or conormal derivative of q is assumed in this identity. -/
theorem IsSolution.conormalDerivative_auxiliaryP_on_sphere {n : ℕ} {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    conormalDerivative u (auxiliaryP u) x =
      conormalDerivative u (gradientNormSq u) x / (n + 1 : ℝ) -
        2 * boundarySlope u x / (n + 1 : ℝ) *
          (1 + gradientNormSq u x / (n + 1 : ℝ)) := by
  have hux := hu.2.1.contDiffAt (Metric.sphere_subset_closedBall hx)
  have hqx := hu.gradientNormSq_contDiffAt_closedBall
    (Metric.sphere_subset_closedBall hx)
  have hE := (contDiffAt_expWeight hux).differentiableAt (by simp)
  have hq := hqx.differentiableAt (by simp)
  have hP : auxiliaryP u = fun y => expWeight u y *
      (1 + (n + 1 : ℝ)⁻¹ * gradientNormSq u y) := by
    funext y
    simp only [auxiliaryP, div_eq_mul_inv]
    ring
  have hfactor : DifferentiableAt ℝ
      (fun y => 1 + (n + 1 : ℝ)⁻¹ * gradientNormSq u y) x := by
    exact (differentiableAt_const (c := (1 : ℝ))).add (hq.const_mul (n + 1 : ℝ)⁻¹)
  rw [hP, conormalDerivative_mul u hx hE hfactor,
    conormalDerivative_const_add_const_mul u hx hq,
    hu.conormalDerivative_expWeight_on_sphere hx]
  have hEx : expWeight u x = 1 := by
    simp [expWeight, hu.2.2.2.2 x hx]
  rw [hEx]
  ring

/-- The actual W = log(P-1) obeys its conormal logarithm rule. -/
theorem IsSolution.conormalDerivative_auxiliaryW {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitSphere n) :
    conormalDerivative u (auxiliaryW u) x =
      conormalDerivative u (auxiliaryP u) x / (auxiliaryP u x - 1) := by
  have hP := (hu.auxiliaryP_smoothNear.contDiffAt
    (Metric.sphere_subset_closedBall hx)).differentiableAt (by simp)
  have hne : auxiliaryP u x - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hu.auxiliaryP_gt_one_closedBall hn
      (Metric.sphere_subset_closedBall hx)))
  unfold auxiliaryW
  rw [conormalDerivative_log u hx (hP.sub_const 1) hne,
    conormalDerivative_sub_const u hx hP]

namespace ConormalCalculus

/-- Smooth sphere restrictions have the same horizontal gradient.
The proof uses a tangent vector and the existing great-circle theorem. -/
theorem horizontalGradient_eq_of_eqOn_sphere {n : ℕ} {h k : E n → ℝ}
    (hh : SmoothNear (closedUnitBall n) h)
    (hk : SmoothNear (closedUnitBall n) k)
    (heq : Set.EqOn h k (unitSphere n)) {x : E n}
    (hx : x ∈ unitSphere n) : horizontalGradient h x = horizontalGradient k x := by
  have hsub : SmoothNear (closedUnitBall n) (fun y => h y - k y) := by
    obtain ⟨U, hU, hKU, hhU⟩ := hh
    obtain ⟨V, hV, hKV, hkV⟩ := hk
    exact ⟨U ∩ V, hU.inter hV, (fun y hy => ⟨hKU hy, hKV hy⟩),
      (hhU.mono Set.inter_subset_left).sub (hkV.mono Set.inter_subset_right)⟩
  let v : E n := horizontalGradient h x - horizontalGradient k x
  have hnormal : inner ℝ x v = 0 := by
    simp only [v, inner_sub_right, horizontalGradient_inner_normal _ hx, sub_self]
  have hhopf : inner ℝ (J x) v = 0 := by
    simp only [v, inner_sub_right, horizontalGradient_inner_hopf _ hx, sub_self]
  have hzero : ∀ y ∈ unitSphere n, h y - k y = 0 := by
    intro y hy
    exact sub_eq_zero.mpr (heq hy)
  have hd := sphere_tangent_deriv_zero hsub hzero hx hnormal
  have hhd := (hh.contDiffAt (Metric.sphere_subset_closedBall hx)).differentiableAt (by simp)
  have hkd := (hk.contDiffAt (Metric.sphere_subset_closedBall hx)).differentiableAt (by simp)
  rw [fderiv_fun_sub hhd hkd] at hd
  have hi : inner ℝ v v = 0 := by
    change inner ℝ (horizontalGradient h x - horizontalGradient k x) v = 0
    rw [inner_sub_left, inner_horizontalGradient h hnormal hhopf,
      inner_horizontalGradient k hnormal hhopf]
    exact hd
  have hn : ‖v‖ = 0 := by
    rw [real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg v]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem euclideanGradient_const_mul {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (c : ℝ) :
    euclideanGradient (fun y => c * h y) x = c • euclideanGradient h x := by
  have hd := (hh.hasFDerivAt.const_mul c).fderiv
  simp only [euclideanGradient, hd, smul_apply, smul_eq_mul,
    Finset.smul_sum, smul_smul]

theorem horizontalGradient_const_mul {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : DifferentiableAt ℝ h x) (c : ℝ) :
    horizontalGradient (fun y => c * h y) x = c • horizontalGradient h x := by
  simp only [horizontalGradient, euclideanGradient_const_mul hh c,
    real_inner_smul_left, smul_sub, smul_smul]

end ConormalCalculus

/-- The boundary q-value may be differentiated horizontally, because the
horizontal vector lies in the sphere tangent space. This does not assert
any neighbourhood equality and gives no normal derivative of q. -/
theorem IsSolution.horizontalGradient_gradientNormSq_on_sphere {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitSphere n) :
    horizontalGradient (gradientNormSq u) x =
      ((n + 1 : ℝ) * boundarySlope u x ^ n / μ) •
        horizontalGradient (boundarySlope u) x := by
  have ht := hu.2.1.boundarySlope
  have hp : SmoothNear (closedUnitBall n)
      (fun y => μ⁻¹ * boundarySlope u y ^ (n + 1)) := by
    obtain ⟨U, hU, hKU, htU⟩ := ht
    exact ⟨U, hU, hKU, contDiffOn_const.mul (htU.pow (n + 1))⟩
  have heq : Set.EqOn (gradientNormSq u)
      (fun y => μ⁻¹ * boundarySlope u y ^ (n + 1)) (unitSphere n) := by
    intro y hy
    rw [hu.gradientNormSq_on_sphere hn hy]
    ring
  rw [ConormalCalculus.horizontalGradient_eq_of_eqOn_sphere
    hu.gradientNormSq_smoothNear hp heq hx]
  have htd := (ht.contDiffAt (Metric.sphere_subset_closedBall hx)).differentiableAt (by simp)
  change horizontalGradient (fun y => μ⁻¹ * (boundarySlope u ^ (n + 1)) y) x = _
  rw [ConormalCalculus.horizontalGradient_const_mul (htd.pow (n + 1)) μ⁻¹]
  change μ⁻¹ • horizontalGradient (fun y => boundarySlope u y ^ (n + 1)) x = _
  rw [horizontalGradient_pow htd (n + 1), smul_smul]
  congr 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

/-- Actual q-conormal expressed using its separately computed ambient normal
 derivative. The horizontal correction is discharged from the original
 solution hypotheses, not supplied as an algebraic input. -/
theorem IsSolution.conormalDerivative_gradientNormSq_on_sphere {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitSphere n) :
    conormalDerivative u (gradientNormSq u) x =
      fderiv ℝ (gradientNormSq u) x x -
        (n + 1 : ℝ) * boundarySlope u x ^ (n - 1) *
          ‖horizontalGradient (boundarySlope u) x‖ ^ 2 / (2 * μ) := by
  rw [conormalDerivative, hu.horizontalGradient_gradientNormSq_on_sphere hn hx,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  have ht : boundarySlope u x ≠ 0 := ne_of_gt (hu.boundarySlope_pos hn hx)
  have hμ : μ ≠ 0 := ne_of_gt hu.1
  have hp : boundarySlope u x ^ n =
      boundarySlope u x ^ (n - 1) * boundarySlope u x := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  field_simp [ht, hμ]
  <;> ring

#print axioms conormalDerivative_eq_fderiv_direction
#print axioms conormalDerivative_mul
#print axioms conormalDerivative_log
#print axioms IsSolution.conormalDerivative_auxiliaryP_on_sphere
#print axioms IsSolution.conormalDerivative_auxiliaryW
#print axioms IsSolution.horizontalGradient_gradientNormSq_on_sphere
#print axioms IsSolution.conormalDerivative_gradientNormSq_on_sphere

end KEBall
