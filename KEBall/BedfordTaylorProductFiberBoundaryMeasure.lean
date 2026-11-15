import KEBall.BedfordTaylorCompactMassLimit
import KEBall.BedfordTaylorProductBoundaryMassBound

/-!
# No top Monge–Ampère mass on the fiber sphere
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn RelativelyCompactIn)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

set_option maxHeartbeats 1200000 in
/-- The top measure of the quadratic extension of a product obstacle
envelope assigns zero mass to its fiber sphere over compact base balls. -/
theorem topMeasure_productFiberExtension_sphere_eq_zero {n : ℕ} {R : ℝ}
    (hR : 0 < R) (hR₁ : R < 1)
    {u v : ComplexModel (n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n 1) v)
    (hvf : ∀ x ∈ complexProductBall n 1, v x ≤ (ball (0 : ComplexModel (n + 1)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + 1) → ℝ, IsLocallyBoundedPshOn (complexProductBall n 1) w →
      (∀ x ∈ complexProductBall n 1, w x ≤ (ball (0 : ComplexModel (n + 1)) R).indicator u x) →
        ∀ x ∈ complexProductBall n 1, w x ≤ v x)
    {A : ℝ} (hA : 0 < A)
    (hvLower : ∀ x ∈ complexProductBall n 1, A * productFiberQuadratic n 1 x ≤ v x)
    {r₀ : ℝ} (hr₀ : r₀ < 1) :
    let e := complexProductCoordinates n 1
    let p := gluedMax (complexProductBall n 1 : Set (ComplexModel (n + 1))) v
      (fun x => A * productFiberQuadratic n 1 x)
    ∃ hp : IsLocallyBoundedPshOn (complexProductCylinder n 1) p,
      topMeasure hp (e ⁻¹' (sphere 0 1 ×ˢ closedBall 0 r₀)) = 0 := by
  let e := complexProductCoordinates n 1
  let Ω := complexProductCylinder n 1
  let p := gluedMax (complexProductBall n 1 : Set (ComplexModel (n + 1))) v
    (fun x => A * productFiberQuadratic n 1 x)
  have hv₀ (x : ComplexModel (n + 1)) (hx : x ∈ complexProductBall n 1) : v x ≤ 0 :=
    (hvf x hx).trans (by
      by_cases hxR : x ∈ ball 0 R
      · simpa only [indicator_of_mem hxR] using hu₀ x hxR
      · simp only [indicator_of_notMem hxR, le_refl])
  have hp : IsLocallyBoundedPshOn Ω p := locallyBoundedPsh_gluedMax_productFiberQuadratic hv hv₀ hA hvLower
  refine ⟨hp, ?_⟩
  let b := (r₀ + 1) / 2
  let r := (b + 1) / 2
  let δ := (1 - r) / 2
  have hb : r₀ < b := by dsimp [b]; linarith
  have hb₁ : b < 1 := by dsimp [b]; linarith
  have hr : b < r := by dsimp [r]; linarith
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hrδ : r + δ < 1 := by dsimp [δ]; linarith
  let K := e ⁻¹' (sphere 0 1 ×ˢ closedBall 0 r₀)
  let L := e ⁻¹' (closedBall 0 2 ×ˢ closedBall 0 b)
  have hK : IsCompact K := e.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_sphere (0 : ComplexModel n) 1).prod (isCompact_closedBall (0 : ComplexModel 1) r₀))
  have hL : IsCompact L := e.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_closedBall (0 : ComplexModel n) 2).prod (isCompact_closedBall (0 : ComplexModel 1) b))
  have hLΩ : L ⊆ Ω := fun _ hx =>
    mem_complexProductCylinder.mpr ((mem_closedBall_zero_iff.mp hx.2).trans_lt hb₁)
  obtain ⟨U, hU, hLU, hclU, hcompactU⟩ := exists_open_between_and_isCompact_closure hL Ω.isOpen hLΩ
  let W : Opens (ComplexModel (n + 1)) := ⟨U, hU⟩
  have hWΩ : W ≤ Ω := subset_closure.trans hclU
  have hrel : RelativelyCompactIn W Ω := ⟨hcompactU, hclU⟩
  obtain ⟨q, s, hs, K', _, _, hballs, hq, hqSmooth, hformula, C, hC, hD⟩ :=
    exists_productEnvelope_fiber_regularization hR hR₁ hδ hrδ hu hu₀ huBoundary hv hvf hgreatest hA hvLower hrel
  let T := ball (0 : ComplexModel 1) b
  let B := ball (0 : ComplexModel n) 2
  let M := ENNReal.ofReal (A ^ n) * (volume : Measure (ComplexModel n)) B
  let N := (volume : Measure (ComplexModel 1)) T * M
  let a : ℝ := ((n + 1).factorial : ℝ) / Real.pi ^ (n + 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hN : N < ⊤ := ENNReal.mul_lt_top
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall _ _).measure_lt_top)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall _ _).measure_lt_top))
  let η (j : ℕ) : ℝ := s / ((j : ℝ) + 1)
  have hη : Tendsto η atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop s
  have hSmall (ε : ℝ) (hε : 0 < ε) : ∀ᶠ j in atTop,
      η j < ε ∧ η j < 1 / 2 ∧ η j < r - b :=
    (hη.eventually_lt_const hε).and
      ((hη.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).and (hη.eventually_lt_const (sub_pos.mpr hr)))
  have hest (ε : ℝ) (hε : 0 < ε) :
      topMeasure (IsLocallyBoundedPshOn.mono hp hWΩ) K ≤
        ENNReal.ofReal (a * (C * (2 * ε) / 2)) * N := by
    let Z := {z : ComplexModel n | 1 - ε < ‖z‖} ∩ B
    have hZ : IsOpen Z := (isOpen_lt continuous_const continuous_norm).inter isOpen_ball
    let V : Opens (ComplexModel (n + 1)) :=
      ⟨e ⁻¹' (Z ×ˢ T), (hZ.prod isOpen_ball).preimage e.continuous⟩
    have hVW : V ≤ W := fun _ hx =>
      hLU ⟨ball_subset_closedBall hx.1.2, ball_subset_closedBall hx.2⟩
    have hKV : K ⊆ V := by
      intro x hx
      have hz : ‖(e x).1‖ = 1 := mem_sphere_zero_iff_norm.mp hx.1
      exact ⟨⟨by change 1 - ε < ‖(e x).1‖; linarith,
        mem_ball_zero_iff.mpr (by linarith)⟩, closedBall_subset_ball hb hx.2⟩
    have hqLB (j : ℕ) := isLocallyBoundedPshOn_of_isSmoothPshOn (hq.1 j)
    apply topMeasure_apply_compact_le_of_decreasing _ hqLB hq.2.1 hq.2.2 hVW hK hKV
    filter_upwards [hSmall ε hε] with j hj
    have hMass (w : ComplexModel 1) (hw : w ∈ T) :
        (∫⁻ z in Z, ENNReal.ofReal (modelHessian (fun y => q j (e.symm (y, w))) z).det.re) ≤ M := by
      apply (lintegral_mono' (Measure.restrict_mono (inter_subset_right : Z ⊆ B) le_rfl) le_rfl).trans
      apply (lintegral_fiber_det_eq_of_quadratic_collar (n := n) (m := 1) (hqSmooth j)
        (hq.1 j) (r := 3 / 2) (R := 2) (A := A)
        (d := A * (productFiberKernelSecondMoment n 1 s hs j - 1)) (by norm_num) hA
        (fun z hz => hLU (by
          change e (e.symm (z, w)) ∈ closedBall 0 2 ×ˢ closedBall 0 b
          rw [e.apply_symm_apply]
          exact ⟨ball_subset_closedBall hz, ball_subset_closedBall hw⟩)) ?_).le
      intro z hz hzr
      let x := e.symm (z, w)
      have hxW : x ∈ W := hLU (by
        change e (e.symm (z, w)) ∈ closedBall 0 2 ×ˢ closedBall 0 b
        rw [e.apply_symm_apply]
        exact ⟨ball_subset_closedBall hz, ball_subset_closedBall hw⟩)
      have hx : 1 + η j ≤ ‖(e x).1‖ := by
        rw [show e x = (z, w) from e.apply_symm_apply _]
        linarith only [hj.2.1, hzr]
      have he := translationPairing_gluedMax_fiberQuadratic_eq (v := v) (A := A) hs j
        (hballs x hxW) hx
      have hqEq : q j x = translationPairing volume (K'.indicator p)
          (Regularization.HolomorphicPullback.explicitRadialKernel s hs j) x := congrFun (hformula j) x
      change translationPairing volume (K'.indicator p)
        (Regularization.HolomorphicPullback.explicitRadialKernel s hs j) x = _ at he
      change q j x = _
      rw [hqEq.trans he]
      simp only [productFiberQuadratic, show (complexProductCoordinates n 1) x = (z, w) from
        e.apply_symm_apply _, mul_add]
      ring
    apply topMeasure_preimage_prod_le_of_fiber_mass (hqSmooth j) (hq.1 j) hZ.measurableSet
      measurableSet_ball hVW (by positivity : 0 ≤ C * (2 * ε)) ?_ hMass
    intro x hx y hy
    have hxT : ‖(e x).2‖ < b := mem_ball_zero_iff.mp hx.2
    have hxD : fiberBoundaryDistance n 1 x ≤ ε := max_le (by
      have h : 1 - ε < ‖(e x).1‖ := hx.1.1
      linarith) hε.le
    have hxB : ‖(e x).2‖ + η j ≤ r := by linarith only [hxT, hj.2.2]
    exact (hD j x (hVW hx) hxB y hy).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hxD, hj.1]) hC) (sq_nonneg _))
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hε₀ (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hTend : Tendsto (fun k => ENNReal.ofReal (a * (C * (2 * ε k) / 2)) * N)
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_toReal hN.ne]
    simp_rw [← ENNReal.ofReal_mul (show 0 ≤ a * (C * (2 * ε _) / 2) by positivity)]
    have hReal : Tendsto (fun k => a * (C * (2 * ε k) / 2) * N.toReal) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_div, zero_mul] using
        (((((hε.const_mul 2).const_mul C).div_const 2).const_mul a).mul_const N.toReal)
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hReal
  have hzero := le_of_tendsto_of_tendsto tendsto_const_nhds hTend
    (Eventually.of_forall fun k => hest (ε k) (hε₀ k))
  have hKW : K ⊆ W := fun _ hx => hLU ⟨(sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))) hx.1,
    closedBall_subset_closedBall hb.le hx.2⟩
  change topMeasure hp K = 0
  rw [← topMeasure_restrict hp hWΩ] at hzero
  rw [Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKW] at hzero
  exact le_antisymm hzero bot_le

end KEBall.BedfordTaylor
