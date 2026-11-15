import KEBall.BedfordTaylorWeightedCollar
import KEBall.BedfordTaylorProductFiberMass

/-!
# Finite energy and constant mass of fibers with a quadratic collar
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn isSmoothPshOn_norm_sq
  smoothMeasure_norm_sq)

theorem ae_mem_domain_topMeasure {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) :
    ∀ᵐ x ∂topMeasure hu, x ∈ Ω := by
  rw [ae_iff]
  exact topMeasure_compl hu

/-- A bounded potential is integrable against any finite Bedford–Taylor
measure on the same domain. -/
theorem integrable_topMeasure_of_bounded {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) (hFin : topMeasure hv univ < ⊤)
    {C : ℝ} (hC : ∀ x ∈ Ω, ‖u x‖ ≤ C) : Integrable u (topMeasure hv) := by
  let : IsFiniteMeasure (topMeasure hv) := ⟨hFin⟩
  have hdom := ae_mem_domain_topMeasure hv
  have hm : AEMeasurable u ((topMeasure hv).restrict Ω) :=
    aemeasurable_restrict_of_measurable_subtype Ω.isOpen.measurableSet
      (measurable_subtype_of_locallyBoundedPsh hu)
  rw [Measure.restrict_eq_self_of_ae_mem hdom] at hm
  exact Integrable.of_bound hm.aestronglyMeasurable C (hdom.mono hC)

/-- The mass of a bounded ball potential with exterior quadratic coefficient
A agrees with the mass of that quadratic on the whole ball. -/
theorem topMeasure_univ_eq_of_quadratic_collar {n : ℕ} {r R A d : ℝ}
    {u : ComplexModel n → ℝ} (hr : r < R) (hA : 0 < A)
    (hu : IsLocallyBoundedPshOn (ballDomain 0 R) u)
    (hEq : ∀ z ∈ ball (0 : ComplexModel n) R, r < ‖z‖ → u z = A * ‖z‖ ^ 2 + d) :
    topMeasure hu univ = ENNReal.ofReal (A ^ n) *
      (ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) *
        (volume : Measure (ComplexModel n)) (ball 0 R)) := by
  let U : Opens (ComplexModel n) := ballDomain 0 R
  let b (z : ComplexModel n) := A * ‖z‖ ^ 2 + d
  let hq := isSmoothPshOn_norm_sq U
  have hb : IsLocallyBoundedPshOn U b :=
    locallyBoundedPsh_add_const (locallyBoundedPsh_const_mul
      (isLocallyBoundedPshOn_of_isSmoothPshOn hq) hA) d
  have he : EqOn u b ((U : Set (ComplexModel n)) \ closedBall 0 r) := by
    intro z hz
    exact hEq z hz.1 (lt_of_not_ge (fun h => hz.2 (mem_closedBall_zero_iff.mpr h)))
  rw [topMeasure_total_eq_of_eq_off_compact hu hb (isCompact_closedBall _ _)
    (closedBall_subset_ball hr) he]
  change topMeasure (locallyBoundedPsh_add_const (locallyBoundedPsh_const_mul
    (isLocallyBoundedPshOn_of_isSmoothPshOn hq) hA) d) univ = _
  rw [topMeasure_add_const (locallyBoundedPsh_const_mul (isLocallyBoundedPshOn_of_isSmoothPshOn hq) hA),
    topMeasure_const_mul (isLocallyBoundedPshOn_of_isSmoothPshOn hq) hA, topMeasure_eq_smoothMeasure hq,
    smoothMeasure_norm_sq, Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply_univ]
  rfl

theorem topMeasure_univ_lt_top_of_quadratic_collar {n : ℕ} {r R A d : ℝ}
    {u : ComplexModel n → ℝ} (hr : r < R) (hA : 0 < A)
    (hu : IsLocallyBoundedPshOn (ballDomain 0 R) u)
    (hEq : ∀ z ∈ ball (0 : ComplexModel n) R, r < ‖z‖ → u z = A * ‖z‖ ^ 2 + d) :
    topMeasure hu univ < ⊤ := by
  rw [topMeasure_univ_eq_of_quadratic_collar hr hA hu hEq]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)

/-- The fiber pairing changes by the subtracted constant times the fiber mass. -/
theorem integral_topMeasure_sub_const {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (c : ℝ)
    (hFin : topMeasure hu univ < ⊤) (hInt : Integrable u (topMeasure hu)) :
    (∫ z, u z + -c ∂topMeasure (locallyBoundedPsh_add_const hu (-c))) =
      (∫ z, u z ∂topMeasure hu) - c * (topMeasure hu univ).toReal := by
  let : IsFiniteMeasure (topMeasure hu) := ⟨hFin⟩
  rw [topMeasure_add_const hu (-c)]
  change (∫ z, u z - c ∂topMeasure hu) = _
  rw [integral_sub hInt (integrable_const c), integral_const, measureReal_def, smul_eq_mul, mul_comm _ c]

/-- In a fixed ball, convergence of the common quadratic collar coefficients
allows the weighted Bedford–Taylor convergence on the entire ball. -/
theorem tendsto_integral_topMeasure_of_quadratic_collar {n : ℕ}
    {r R A D : ℝ} (hr : r < R) (hA : 0 < A)
    {u : ComplexModel n → ℝ} {q : ℕ → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn (ballDomain 0 R) u)
    (hq : ∀ j, IsLocallyBoundedPshOn (ballDomain 0 R) (q j))
    (huEq : ∀ z ∈ ball (0 : ComplexModel n) R, r < ‖z‖ → u z = A * ‖z‖ ^ 2 + D)
    {a d : ℕ → ℝ} (ha : ∀ j, 0 < a j) (haLim : Tendsto a atTop (𝓝 A))
    (hdLim : Tendsto d atTop (𝓝 D))
    (hqEq : ∀ j z, z ∈ ball (0 : ComplexModel n) R → r < ‖z‖ → q j z = a j * ‖z‖ ^ 2 + d j)
    (hanti : ∀ z ∈ ball (0 : ComplexModel n) R, Antitone (fun j => q j z))
    (hlim : ∀ z ∈ ball (0 : ComplexModel n) R, Tendsto (fun j => q j z) atTop (𝓝 (u z)))
    {C : ℝ} (huC : ∀ z ∈ ball (0 : ComplexModel n) R, ‖u z‖ ≤ C)
    (hqC : ∀ j z, z ∈ ball (0 : ComplexModel n) R → ‖q j z‖ ≤ C) :
    Tendsto (fun j => ∫ z, q j z ∂topMeasure (hq j)) atTop
      (𝓝 (∫ z, u z ∂topMeasure hu)) := by
  let U : Opens (ComplexModel n) := ballDomain 0 R
  let b (z : ComplexModel n) := A * ‖z‖ ^ 2 + D
  let k (j : ℕ) := a j / A
  let t (j : ℕ) := d j - k j * D
  have hb : IsLocallyBoundedPshOn U b :=
    locallyBoundedPsh_add_const (locallyBoundedPsh_const_mul
      (isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_norm_sq U)) hA) D
  have hbC (z : ComplexModel n) (hz : z ∈ U) : ‖b z‖ ≤ A * R ^ 2 + ‖D‖ := by
    have hzR := mem_ball_zero_iff.mp hz
    have hz2 := pow_le_pow_left₀ (norm_nonneg z) hzR.le 2
    exact (norm_add_le _ _).trans (by
      rw [norm_mul, Real.norm_of_nonneg hA.le, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      gcongr)
  have hbMass := topMeasure_univ_lt_top_of_quadratic_collar hr hA hb (fun _ _ _ => rfl)
  have hk : ∀ j, 0 < k j := fun j => div_pos (ha j) hA
  have hkLim : Tendsto k atTop (𝓝 1) := by
    simpa only [k, div_self hA.ne'] using haLim.div_const A
  have htLim : Tendsto t atTop (𝓝 0) := by
    simpa only [t, one_mul, sub_self] using hdLim.sub (hkLim.mul_const D)
  have huE : EqOn u b ((U : Set (ComplexModel n)) \ closedBall 0 r) := fun z hz =>
    huEq z hz.1 (lt_of_not_ge (fun h => hz.2 (mem_closedBall_zero_iff.mpr h)))
  have hqE (j : ℕ) : EqOn (q j) (fun z => k j * b z + t j)
      ((U : Set (ComplexModel n)) \ closedBall 0 r) := by
    intro z hz
    rw [hqEq j z hz.1 (lt_of_not_ge (fun h => hz.2 (mem_closedBall_zero_iff.mpr h)))]
    dsimp only [k, b, t]
    field_simp [hA.ne']
    ring
  exact tendsto_integral_topMeasure_of_decreasing_of_affine_collar hu hb hq
    (isCompact_closedBall _ _) (closedBall_subset_ball hr) huE hk hkLim htLim hqE hanti hlim
    ⟨hbMass⟩ (integrable_topMeasure_of_bounded hb hb hbMass hbC)
    (integrable_topMeasure_of_bounded hu hu (topMeasure_univ_lt_top_of_quadratic_collar hr hA hu huEq) huC)
    (fun j => integrable_topMeasure_of_bounded (hq j) (hq j)
      (topMeasure_univ_lt_top_of_quadratic_collar hr (ha j) (hq j) (hqEq j)) (hqC j))

end KEBall.BedfordTaylor
