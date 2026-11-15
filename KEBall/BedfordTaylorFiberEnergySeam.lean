import KEBall.BedfordTaylorFiberEnergyLimit

/-!
# Separating the true fiber energy from the exterior quadratic
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn isSmoothPshOn_norm_sq)

/-- The weighted top measure ignores the sphere on which the potential
vanishes, even if the top measure itself charges the sphere. -/
theorem integral_topMeasure_eq_inner_add_collar {n : ℕ} {r R : ℝ}
    {p b : ComplexModel n → ℝ} (hr : r < R)
    (hp : IsLocallyBoundedPshOn (ballDomain 0 R) p)
    (hb : IsLocallyBoundedPshOn (ballDomain 0 R) b)
    (hEq : EqOn p b (ball (0 : ComplexModel n) R \ closedBall 0 r))
    (hZero : ∀ z, ‖z‖ = r → p z = 0)
    (hInt : Integrable p (topMeasure hp)) :
    (∫ z, p z ∂topMeasure hp) =
      (∫ z, p z ∂topMeasure
        (IsLocallyBoundedPshOn.mono hp (show ballDomain (0 : ComplexModel n) r ≤ ballDomain 0 R from
          fun _ hz => ball_subset_ball hr.le hz))) +
      ∫ z in (closedBall (0 : ComplexModel n) r)ᶜ, b z ∂topMeasure hb := by
  let K := closedBall (0 : ComplexModel n) r
  let B := ball (0 : ComplexModel n) r
  let hSub : ballDomain (0 : ComplexModel n) r ≤ ballDomain 0 R := fun _ hz => ball_subset_ball hr.le hz
  have hClosed : (∫ z in K, p z ∂topMeasure hp) = ∫ z in B, p z ∂topMeasure hp := by
    rw [← integral_indicator measurableSet_closedBall, ← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ B
    · rw [indicator_of_mem hz, indicator_of_mem (show z ∈ K from ball_subset_closedBall hz)]
    · rw [indicator_of_notMem hz]
      by_cases hK : z ∈ K
      · rw [indicator_of_mem hK, hZero z
          ((mem_closedBall_zero_iff.mp hK).antisymm (le_of_not_gt (fun h => hz (mem_ball_zero_iff.mpr h))))]
      · rw [indicator_of_notMem hK]
  have hOut : (∫ z in Kᶜ, p z ∂topMeasure hp) = ∫ z in Kᶜ, b z ∂topMeasure hb := by
    rw [topMeasure_restrict_compl_eq_of_eq_off_compact hp hb (isCompact_closedBall _ _) hEq]
    apply integral_congr_ae
    filter_upwards [ae_mono (Measure.restrict_le_self (s := Kᶜ)) (ae_mem_domain_topMeasure hb),
      ae_restrict_mem (μ := topMeasure hb) measurableSet_closedBall.compl] with z hz hK
    exact hEq ⟨hz, hK⟩
  rw [← integral_add_compl measurableSet_closedBall hInt, hClosed, hOut]
  change (∫ z, p z ∂(topMeasure hp).restrict (ball (0 : ComplexModel n) r)) + _ = _
  have hμ : (topMeasure hp).restrict (ball (0 : ComplexModel n) r) =
      topMeasure (IsLocallyBoundedPshOn.mono hp hSub) := topMeasure_restrict hp hSub
  rw [hμ]

set_option maxHeartbeats 750000 in
/-- The extension to radius two changes the fiber energy by a constant
independent of the base point. -/
theorem bedfordTaylorFiberEnergy_productFiberExtension_eq_add_const {n : ℕ}
    {A : ℝ} (hA : 0 < A) {v : ComplexModel (n + 1) → ℝ}
    (hv : IsLocallyBoundedPshOn (complexProductBall n 1) v)
    (hvLower : ∀ x ∈ complexProductBall n 1, A * productFiberQuadratic n 1 x ≤ v x)
    (hp : IsLocallyBoundedPshOn (complexProductCylinder n 1)
      (gluedMax (complexProductBall n 1 : Set (ComplexModel (n + 1))) v
        (fun x => A * productFiberQuadratic n 1 x))) :
    ∃ C : ℝ, ∀ w ∈ unitBall 1,
      bedfordTaylorFiberEnergy
        (IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)) w =
        bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w + C := by
  classical
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let P := complexProductBall n 1
  let p := gluedMax (P : Set (ComplexModel (n + 1))) v
    (fun x => A * productFiberQuadratic n 1 x)
  let B₂ : Opens (ComplexModel n) := ballDomain 0 2
  let B₁ : Opens (ComplexModel n) := ballDomain 0 1
  let b (z : ComplexModel n) := A * ‖z‖ ^ 2 + -A
  have hb : IsLocallyBoundedPshOn B₂ b :=
    locallyBoundedPsh_add_const (locallyBoundedPsh_const_mul
      (isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_norm_sq B₂)) hA) (-A)
  refine ⟨(∫ z in (closedBall (0 : ComplexModel n) 1)ᶜ, b z ∂topMeasure hb) / (n + 1 : ℝ), ?_⟩
  intro w hw
  have hw' : ‖complexCoordinates 1 w‖ < 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_ball_zero_iff.mp hw
  let u := complexFiberSlice p (c w)
  let v' := complexFiberSlice v (c w)
  let hp₃ := IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 3 le_rfl)
  let hp₂ := IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)
  let hu₃ := locallyBoundedPsh_complexFiberSlice hp₃ hw'
  let hu₂ := locallyBoundedPsh_complexFiberSlice hp₂ hw'
  let hv₁ := locallyBoundedPsh_complexFiberSlice (R := 1) (ρ := 1) hv hw'
  let h₁₂ : B₁ ≤ B₂ := fun _ hz => ball_subset_ball (by norm_num) hz
  have hExt (z : ComplexModel n) (hz : 1 ≤ ‖z‖) : u z = b z := by
    have hMem : e (e.symm (z, c w)) = (z, c w) := e.apply_symm_apply _
    have hnot : e.symm (z, c w) ∉ (P : Set (ComplexModel (n + 1))) := by
      intro h
      have hlt := (mem_complexProductBall.mp h).1
      change ‖(e (e.symm (z, c w))).1‖ < 1 at hlt
      rw [hMem] at hlt
      exact (not_lt_of_ge hz) hlt
    change p (e.symm (z, c w)) = b z
    simp only [p, gluedMax, if_neg hnot, productFiberQuadratic, ← show e = complexProductCoordinates n 1 from rfl,
      e.apply_symm_apply, b]
    ring
  have hIn : EqOn u v' B₁ := by
    intro z hz
    have hMem : e (e.symm (z, c w)) = (z, c w) := e.apply_symm_apply _
    have hzP : e.symm (z, c w) ∈ P := by
      apply mem_complexProductBall.mpr
      change ‖(e (e.symm (z, c w))).1‖ < 1 ∧ ‖(e (e.symm (z, c w))).2‖ < 1
      rw [hMem]
      exact ⟨mem_ball_zero_iff.mp hz, hw'⟩
    change p (e.symm (z, c w)) = v (e.symm (z, c w))
    simp only [p, gluedMax, if_pos (show e.symm (z, c w) ∈ (P : Set (ComplexModel (n + 1))) from hzP),
      max_eq_left (hvLower _ hzP)]
  have hFin := topMeasure_univ_lt_top_of_quadratic_collar (by norm_num : (1 : ℝ) < 2)
    hA hu₂ (fun z _ h => hExt z h.le)
  obtain ⟨M, _, hM⟩ := hu₃.exists_compact_abs_bound (isCompact_closedBall (0 : ComplexModel n) 2)
    (closedBall_subset_ball (by norm_num : (2 : ℝ) < 3))
  have hInt : Integrable u (topMeasure hu₂) :=
    integrable_topMeasure_of_bounded hu₂ hu₂ hFin
      (fun z hz => by simpa only [Real.norm_eq_abs] using hM z (ball_subset_closedBall hz))
  have h := integral_topMeasure_eq_inner_add_collar (by norm_num : (1 : ℝ) < 2) hu₂ hb
    (fun z hz => hExt z (le_of_lt (lt_of_not_ge (fun h => hz.2 (mem_closedBall_zero_iff.mpr h)))))
    (fun z hz => by
      change u z = 0
      rw [hExt z hz.ge]
      change A * ‖z‖ ^ 2 + -A = 0
      rw [hz]
      ring) hInt
  have hMu : topMeasure (IsLocallyBoundedPshOn.mono hu₂ h₁₂) = topMeasure hv₁ :=
    topMeasure_congr _ hv₁ hIn
  rw [hMu] at h
  have hInInt : (∫ z, u z ∂topMeasure hv₁) = ∫ z, v' z ∂topMeasure hv₁ :=
    integral_congr_ae ((ae_mem_domain_topMeasure hv₁).mono hIn)
  rw [hInInt] at h
  simp only [bedfordTaylorFiberEnergy, dif_pos hw']
  rw [h, add_div]

end KEBall.BedfordTaylor
