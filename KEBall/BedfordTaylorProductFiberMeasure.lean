import KEBall.BedfordTaylorProductFiberBoundaryMeasure

/-!
# The top measure of the cylinder extension
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn smoothDensity smoothMeasure)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

/-- A quadratic depending only on the fiber has zero ambient top measure. -/
theorem topMeasure_const_mul_productFiberQuadratic_eq_zero {n : ℕ}
    {A : ℝ} (hA : 0 < A) :
    topMeasure (locallyBoundedPsh_const_mul (locallyBoundedPsh_productFiberQuadratic n 1) hA) = 0 := by
  let Ω := complexProductCylinder n 1
  let e := complexProductCoordinates n 1
  let L : ComplexModel (n + 1) →L[ℝ] ComplexModel n :=
    (ContinuousLinearMap.fst ℝ (ComplexModel n) (ComplexModel 1)).comp
      (e.toContinuousLinearMap.restrictScalars ℝ)
  let f (z : ComplexModel n) := A * (‖z‖ ^ 2 - 1)
  let b (x : ComplexModel (n + 1)) := A * productFiberQuadratic n 1 x
  have hb : IsLocallyBoundedPshOn Ω b :=
    locallyBoundedPsh_const_mul (locallyBoundedPsh_productFiberQuadratic n 1) hA
  have hf : ContDiff ℝ ∞ f :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)
  have hbC : ContDiff ℝ ∞ b := hf.comp L.contDiff
  have hbS : IsSmoothPshOn Ω b :=
    PshLines.FirstPass.MongeAmpere.isSmoothPshOn_of_psh hbC.contDiffOn hb.1
  have h2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hBase (x y : ComplexModel (n + 1)) (hy : (e y).1 = 0) :
      PshLines.realHessian b x y y ≤ (0 : ℝ) * ‖y‖ ^ 2 := by
    have h := PshLines.realHessian_comp_affine (hf.of_le h2) L 0 x y y
    have heq : (fun z => f (0 + L z)) = b := funext fun z => by
      rw [zero_add]
      rfl
    rw [heq, zero_add] at h
    change PshLines.realHessian b x y y = PshLines.realHessian f (L x) (L y) (L y) at h
    rw [h, show L y = 0 from hy, PshLines.realHessian_zero_right, zero_mul]
  have hzero (x : ComplexModel (n + 1)) (hx : x ∈ Ω) : (modelHessian b x).det.re = 0 := by
    have hP := hbS.2.2 x hx
    have h := complexHessian_det_re_le_fiber_mul_of_base_bound (hbC.of_le h2) hP (hBase x)
    rw [zero_div, mul_zero] at h
    exact h.antisymm (RCLike.nonneg_iff.mp hP.det_nonneg).1
  change topMeasure hb = 0
  rw [topMeasure_eq_smoothMeasure hbS, smoothMeasure]
  have he : (fun z => ENNReal.ofReal (smoothDensity b z)) =ᵐ[volume.restrict (Ω : Set (ComplexModel (n + 1)))] 0 := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    simp only [smoothDensity, hzero x hx, mul_zero, ENNReal.ofReal_zero, Pi.zero_apply]
  rw [withDensity_congr_ae he, withDensity_zero]

set_option maxHeartbeats 850000 in
/-- The cylindrical extension has the same top measure as the
envelope on the product ball, viewed as ambient measures. -/
theorem exists_topMeasure_productFiberExtension_eq {n : ℕ} {R : ℝ}
    (hR : 0 < R) (hR₁ : R < 1)
    {u v : ComplexModel (n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n 1) v)
    (hvf : ∀ x ∈ complexProductBall n 1, v x ≤ (ball (0 : ComplexModel (n + 1)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + 1) → ℝ, IsLocallyBoundedPshOn (complexProductBall n 1) w →
      (∀ x ∈ complexProductBall n 1, w x ≤ (ball (0 : ComplexModel (n + 1)) R).indicator u x) →
        ∀ x ∈ complexProductBall n 1, w x ≤ v x)
    {A : ℝ} (hA : 0 < A)
    (hvLower : ∀ x ∈ complexProductBall n 1, A * productFiberQuadratic n 1 x ≤ v x) :
    let p := gluedMax (complexProductBall n 1 : Set (ComplexModel (n + 1))) v
      (fun x => A * productFiberQuadratic n 1 x)
    ∃ hp : IsLocallyBoundedPshOn (complexProductCylinder n 1) p, topMeasure hp = topMeasure hv := by
  classical
  let e := complexProductCoordinates n 1
  let P := complexProductBall n 1
  let Ω := complexProductCylinder n 1
  let b (x : ComplexModel (n + 1)) := A * productFiberQuadratic n 1 x
  let p := gluedMax (P : Set (ComplexModel (n + 1))) v b
  have hv₀ (x : ComplexModel (n + 1)) (hx : x ∈ P) : v x ≤ 0 := (hvf x hx).trans (by
    by_cases hxR : x ∈ ball 0 R
    · simpa only [indicator_of_mem hxR] using hu₀ x hxR
    · simp only [indicator_of_notMem hxR, le_refl])
  have hp : IsLocallyBoundedPshOn Ω p := locallyBoundedPsh_gluedMax_productFiberQuadratic hv hv₀ hA hvLower
  have hb : IsLocallyBoundedPshOn Ω b :=
    locallyBoundedPsh_const_mul (locallyBoundedPsh_productFiberQuadratic n 1) hA
  refine ⟨hp, ?_⟩
  have hPΩ : P ≤ Ω := fun _ hx => mem_complexProductCylinder.mpr (mem_complexProductBall.mp hx).2
  have hInside : (topMeasure hp).restrict (P : Set (ComplexModel (n + 1))) = topMeasure hv := by
    rw [topMeasure_restrict hp hPΩ]
    exact topMeasure_congr _ hv fun x hx =>
      (gluedMax_eq_max hx).trans (max_eq_left (hvLower x hx))
  let X : Opens (ComplexModel (n + 1)) :=
    ⟨(Ω : Set (ComplexModel (n + 1))) ∩ {x | 1 < ‖(e x).1‖},
      Ω.isOpen.inter (isOpen_lt continuous_const e.continuous.fst.norm)⟩
  have hXΩ : X ≤ Ω := inter_subset_left
  have hExt : topMeasure hp (X : Set (ComplexModel (n + 1))) = 0 := by
    have hEq : EqOn p b X := by
      intro x hx
      have hlt : 1 < ‖(e x).1‖ := hx.2
      have hxP : x ∉ (P : Set (ComplexModel (n + 1))) := fun h =>
        (not_lt_of_ge hlt.le) (mem_complexProductBall.mp h).1
      simp only [p, gluedMax, if_neg hxP]
    have h := (topMeasure_restrict hp hXΩ).trans (topMeasure_congr
      (IsLocallyBoundedPshOn.mono hp hXΩ) (IsLocallyBoundedPshOn.mono hb hXΩ) hEq)
    rw [← topMeasure_restrict hb hXΩ, topMeasure_const_mul_productFiberQuadratic_eq_zero hA,
      Measure.restrict_zero] at h
    simpa [Measure.restrict_apply_univ] using
      congrArg (fun μ : Measure (ComplexModel (n + 1)) => μ univ) h
  let S := e ⁻¹' (sphere 0 1 ×ˢ ball 0 1)
  let r (j : ℕ) := 1 - 1 / ((j : ℝ) + 1)
  let K (j : ℕ) := e ⁻¹' (sphere 0 1 ×ˢ closedBall 0 (r j))
  have hr (j : ℕ) : r j < 1 := sub_lt_self 1 (by positivity)
  have hS : S ⊆ ⋃ j, K j := by
    intro x hx
    have hw : ‖(e x).2‖ < 1 := mem_ball_zero_iff.mp hx.2
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hw)
    exact mem_iUnion.mpr ⟨j, hx.1, mem_closedBall_zero_iff.mpr (by dsimp [r]; linarith)⟩
  have hSphere : topMeasure hp S = 0 := by
    apply le_antisymm ((measure_mono hS).trans_eq ?_) bot_le
    apply measure_iUnion_null_iff.mpr
    intro j
    obtain ⟨h, hz⟩ := topMeasure_productFiberExtension_sphere_eq_zero
      hR hR₁ hu hu₀ huBoundary hv hvf hgreatest hA hvLower (hr j)
    exact hz
  have hOutside : (P : Set (ComplexModel (n + 1)))ᶜ ⊆
      ((Ω : Set (ComplexModel (n + 1)))ᶜ ∪ (X : Set (ComplexModel (n + 1)))) ∪ S := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · have hbase : ‖(e x).2‖ < 1 := mem_complexProductCylinder.mp hxΩ
      have hfib : 1 ≤ ‖(e x).1‖ := le_of_not_gt (fun h => hx (mem_complexProductBall.mpr ⟨h, hbase⟩))
      rcases hfib.eq_or_lt with h | h
      · exact Or.inr ⟨mem_sphere_zero_iff_norm.mpr h.symm, mem_ball_zero_iff.mpr hbase⟩
      · exact Or.inl (Or.inr ⟨hxΩ, h⟩)
    · exact Or.inl (Or.inl hxΩ)
  have hNull : topMeasure hp ((P : Set (ComplexModel (n + 1)))ᶜ) = 0 := by
    apply le_antisymm ((measure_mono hOutside).trans ((measure_union_le _ _).trans ?_)) bot_le
    rw [hSphere, add_zero]
    exact (measure_union_le _ _).trans_eq (by rw [topMeasure_compl hp, hExt, add_zero]; rfl)
  have hAE : ∀ᵐ x ∂topMeasure hp, x ∈ (P : Set (ComplexModel (n + 1))) := by rwa [ae_iff]
  exact (Measure.restrict_eq_self_of_ae_mem hAE).symm.trans hInside

end KEBall.BedfordTaylor
