import KEBall.ComplexMaximum
import KEBall.ScalarBranches

/-!
# Stable radial comparison and the lower boundary slope

A strict positive barrier is obtained from the actual radial Jacobi function.
The comparison is proved by an attained positive maximum of the quotient on
the closed ball and the local complex Laplacian sign. The boundary estimate
uses the actual Frechet derivative in the inward tangent-cone direction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped ContDiff BigOperators Topology

namespace KEBall

noncomputable def radialStabilityMargin (n : ℕ) (b : ℝ) : ℝ :=
  ((n : ℝ) - b) / (1 + b)

noncomputable def radialComparisonBarrier (n : ℕ) (b : ℝ) (x : E n) : ℝ :=
  radialJacobi n b x - radialStabilityMargin n b

theorem radialStabilityMargin_pos {n : ℕ} {b : ℝ}
    (hb : 0 < b) (hbn : b < (n : ℝ)) : 0 < radialStabilityMargin n b := by
  exact div_pos (sub_pos.mpr hbn) (by linarith)

theorem smooth_radialComparisonBarrier (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (radialComparisonBarrier n b) :=
  (smooth_radialJacobi n hb).sub contDiff_const

/-- A uniform positive lower bound on the closed ball. -/
theorem radialComparisonBarrier_lower {n : ℕ} {b : ℝ} (hb : 0 < b)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    radialStabilityMargin n b ≤ radialComparisonBarrier n b x := by
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hx
  have hs : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hd : 0 < 1 + b * ‖x‖ ^ 2 := radial_denominator_pos hb (sq_nonneg ‖x‖)
  have h1 : 0 < 1 + b := by linarith
  have h : 2 * ((n : ℝ) - b) / (1 + b) ≤
      2 * ((n : ℝ) - b * ‖x‖ ^ 2) / (1 + b * ‖x‖ ^ 2) := by
    apply (div_le_div_iff₀ h1 hd).mpr
    have hp : 0 ≤ b * (n + 1 : ℝ) * (1 - ‖x‖ ^ 2) :=
      mul_nonneg (mul_nonneg hb.le (by positivity)) (sub_nonneg.mpr hs)
    nlinarith
  have h' : 2 * radialStabilityMargin n b ≤ radialJacobi n b x := by
    simpa only [radialStabilityMargin, radialJacobi, radialJacobiProfile,
      mul_div_assoc] using h
  change radialStabilityMargin n b ≤ radialJacobi n b x - radialStabilityMargin n b
  linarith

theorem radialComparisonBarrier_pos {n : ℕ} {b : ℝ}
    (hb : 0 < b) (hbn : b < (n : ℝ)) {x : E n} (hx : x ∈ closedUnitBall n) :
    0 < radialComparisonBarrier n b x :=
  (radialStabilityMargin_pos hb hbn).trans_le (radialComparisonBarrier_lower hb hx)

/-- The strict supersolution identity is computed from the already proved
Jacobi equation and the actual Laplacian of a constant. -/
theorem radialComparisonBarrier_equation (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E n) :
    complexLaplacian (radialPotential n b) (radialComparisonBarrier n b) x +
      radialComparisonBarrier n b x = -radialStabilityMargin n b := by
  change complexLaplacian (radialPotential n b)
    (fun y => radialJacobi n b y - radialStabilityMargin n b) x +
      (radialJacobi n b x - radialStabilityMargin n b) = _
  rw [complexLaplacian_sub_at _ (smooth_radialJacobi n hb).contDiffAt contDiffAt_const,
    complexLaplacian_const, sub_zero]
  linarith [radialJacobi_equation n hb x]

/-- Every solution with the stable radial coefficient lies below that radial
solution throughout the closed ball. The maximum argument is carried out here. -/
theorem IsSolution.le_stable_radial {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {b : ℝ} (hb : 0 < b) (hbn : b < (n : ℝ))
    (hμ : μ = radialCoefficient n b) :
    ∀ x ∈ closedUnitBall n, u x ≤ radialPotential n b x := by
  let v := radialPotential n b
  let w : E n → ℝ := fun y => u y - v y
  let η := radialComparisonBarrier n b
  have hwAt (y : E n) (hy : y ∈ closedUnitBall n) : ContDiffAt ℝ ∞ w y :=
    (hu.2.1.contDiffAt hy).sub (smooth_radialPotential n hb).contDiffAt
  have hηAt (y : E n) : ContDiffAt ℝ ∞ η y :=
    (smooth_radialComparisonBarrier n hb).contDiffAt
  have hηpos (y : E n) (hy : y ∈ closedUnitBall n) : 0 < η y :=
    radialComparisonBarrier_pos hb hbn hy
  have hwcont : ContinuousOn w (closedUnitBall n) :=
    fun y hy => (hwAt y hy).continuousAt.continuousWithinAt
  have hηcont : ContinuousOn η (closedUnitBall n) :=
    (smooth_radialComparisonBarrier n hb).continuous.continuousOn
  have hquot : ContinuousOn (fun y => w y / η y) (closedUnitBall n) :=
    hwcont.div hηcont (fun y hy => ne_of_gt (hηpos y hy))
  intro p hp
  by_contra hup
  have hwp : 0 < w p := sub_pos.mpr (lt_of_not_ge hup)
  have hnonempty : (closedUnitBall n).Nonempty := by
    exact ⟨0, by simp [closedUnitBall]⟩
  obtain ⟨q, hq, hqmax⟩ := (isCompact_closedBall (0 : E n) 1).exists_isMaxOn hnonempty hquot
  let c := w q / η q
  have hc : 0 < c := (div_pos hwp (hηpos p hp)).trans_le (hqmax hp)
  have hqint : q ∈ unitBall n := by
    by_contra hqnot
    have hqnorm : ‖q‖ ≤ 1 := by
      simpa [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hq
    have hqnorm' : ¬ ‖q‖ < 1 := by
      simpa [unitBall, Metric.mem_ball, dist_zero_right] using hqnot
    have hqsphere : q ∈ unitSphere n := by
      simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using
        le_antisymm hqnorm (le_of_not_gt hqnorm')
    have hwq : w q = 0 := by
      dsimp [w, v]
      rw [hu.2.2.2.2 q hqsphere, radial_boundary_zero n hb hqsphere, sub_self]
    have : c = 0 := by simp [c, hwq]
    linarith
  let h : E n → ℝ := fun y => w y - c * η y
  have hcontact : h q = 0 := by
    dsimp [h, c]
    rw [div_mul_cancel₀ _ (ne_of_gt (hηpos q hq)), sub_self]
  have hmax : IsLocalMax h q := by
    have hmaxOn : IsMaxOn h (closedUnitBall n) q := by
      intro y hy
      change h y ≤ h q
      rw [hcontact]
      exact sub_nonpos.mpr ((div_le_iff₀ (hηpos y hy)).mp (hqmax hy))
    exact hmaxOn.isLocalMax
      (mem_of_superset (Metric.isOpen_ball.mem_nhds hqint) Metric.ball_subset_closedBall)
  have hhAt : ContDiffAt ℝ ∞ h q :=
    (hwAt q hq).sub (contDiffAt_const.mul (hηAt q))
  have hLnonpos : complexLaplacian v h q ≤ 0 :=
    complexLaplacian_nonpos_of_isLocalMax (radial_complexHessian_posDef n hb q) hhAt hmax
  have hLh : complexLaplacian v h q =
      complexLaplacian v w q - c * complexLaplacian v η q := by
    change complexLaplacian v (fun y => w y - c * η y) q = _
    rw [complexLaplacian_sub_at _ (hwAt q hq) (contDiffAt_const.mul (hηAt q)),
      complexLaplacian_const_mul_at _ (hηAt q)]
  have hlin : -w q ≤ complexLaplacian v w q := hu.radial_linearized_difference hb hμ hqint
  have hbar : complexLaplacian v η q + η q = -radialStabilityMargin n b :=
    radialComparisonBarrier_equation n hb q
  have hbarc := congrArg (fun r : ℝ => c * r) hbar
  have hpositive := mul_pos hc (radialStabilityMargin_pos hb hbn)
  change w q - c * η q = 0 at hcontact
  nlinarith

/-- At a shared boundary value, ordering on the closed ball reverses the
outward derivative order. This is the tangent-cone derivative theorem. -/
theorem boundarySlope_ge_of_le {n : ℕ} {f g : E n → ℝ} {x : E n}
    (hx : x ∈ unitSphere n) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hfg : ∀ y ∈ closedUnitBall n, f y ≤ g y) (heq : f x = g x) :
    boundarySlope g x ≤ boundarySlope f x := by
  have hxclosed : x ∈ closedUnitBall n := Metric.sphere_subset_closedBall hx
  have hmax : IsMaxOn (fun y => f y - g y) (closedUnitBall n) x := by
    intro y hy
    change f y - g y ≤ f x - g x
    rw [heq, sub_self]
    exact sub_nonpos.mpr (hfg y hy)
  have hneg : -x ∈ posTangentConeAt (closedUnitBall n) x := by
    have hsegment : segment ℝ x (0 : E n) ⊆ closedUnitBall n :=
      (convex_closedBall (0 : E n) 1).segment_subset hxclosed (by simp)
    simpa only [zero_sub] using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hdf : HasFDerivWithinAt (fun y => f y - g y)
      (fderiv ℝ f x - fderiv ℝ g x) (closedUnitBall n) x :=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).hasFDerivWithinAt
  have h := hmax.localize.hasFDerivWithinAt_nonpos hdf hneg
  simp only [sub_apply, map_neg] at h
  dsimp [boundarySlope]
  linarith

theorem IsSolution.boundarySlope_ge_stable_radial {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {b : ℝ} (hb : 0 < b) (hbn : b < (n : ℝ))
    (hμ : μ = radialCoefficient n b) {x : E n} (hx : x ∈ unitSphere n) :
    radialBoundaryParameter n b ≤ boundarySlope u x := by
  have hxclosed : x ∈ closedUnitBall n := Metric.sphere_subset_closedBall hx
  have h := boundarySlope_ge_of_le hx
    ((hu.2.1.contDiffAt hxclosed).differentiableAt (by simp))
    ((smooth_radialPotential n hb).differentiable (by simp) x)
    (hu.le_stable_radial hb hbn hμ)
    (by rw [hu.2.2.2.2 x hx, radial_boundary_zero n hb hx])
  rw [radial_boundarySlope n hb hx] at h
  exact h

/-- The lower scalar root determines an actual stable radial solution, so
its value bounds the actual boundary slope of every solution. -/
theorem IsSolution.boundarySlope_ge_lower_root {n : ℕ} {μ a : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) (ha : 0 < a) (han : a < (n : ℝ))
    (hFa : boundaryPolynomial n a = μ) {x : E n} (hx : x ∈ unitSphere n) :
    a ≤ boundarySlope u x := by
  have hak : a < (n + 1 : ℝ) := by linarith
  let b := a / ((n + 1 : ℝ) - a)
  have hb : 0 < b := div_pos ha (sub_pos.mpr hak)
  have hbn : b < (n : ℝ) := by
    dsimp [b]
    apply (div_lt_iff₀ (sub_pos.mpr hak)).mpr
    have hp : 0 < (n + 1 : ℝ) * ((n : ℝ) - a) :=
      mul_pos (by positivity) (sub_pos.mpr han)
    nlinarith
  have hparam : radialBoundaryParameter n b = a := radialBoundaryParameter_inverse n ⟨ha, hak⟩
  have hμ : μ = radialCoefficient n b := by
    rw [radialCoefficient_eq_boundaryPolynomial n hb, hparam]
    exact hFa.symm
  simpa only [hparam] using hu.boundarySlope_ge_stable_radial hb hbn hμ hx

/-- Lemma 2.2 exactly as frozen in `Specification.lean`. -/
theorem lowerSlopeStatement : LowerSlopeStatement := by
  intro n _ μ a u hu _ ha han hFa x hx
  exact hu.boundarySlope_ge_lower_root ha han hFa hx

end KEBall
