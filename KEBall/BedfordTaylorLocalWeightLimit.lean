import KEBall.BedfordTaylorBallBarrier
import KEBall.BedfordTaylorBoundaryWeightLimit
import KEBall.BedfordTaylorMixedLocality

/-!
# Joint weighted convergence for tests supported in an inner ball

Local modification by a smooth maximum reduces this convergence to
the common-boundary case. The modifications agree exactly with the
original potentials on an open neighborhood of the test support.
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}
  {u' p' : ℕ → ComplexModel n → ℝ}

private theorem isSmoothPshOn_mono {V : Opens (ComplexModel n)}
    (hu : IsSmoothPshOn Ω u) (hV : V ≤ Ω) : IsSmoothPshOn V u :=
  ⟨hu.1.mono hV, hu.2.1.mono hV, fun _ hx => hu.2.2 _ (hV hx)⟩

theorem tendsto_smoothMax_left {f : ℕ → ℝ} {x : ℝ} (b : ℝ)
    (h : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun j => smoothMax (f j) b) atTop (𝓝 (smoothMax x b)) :=
  (contDiff_smoothMax.continuous.tendsto (x, b)).comp (h.prodMk_nhds tendsto_const_nhds)

theorem isLocallyBoundedPshOn_smoothMax_of_decreasing
    (hu : IsLocallyBoundedPshOn Ω u) {b : ComplexModel n → ℝ} (hb : IsSmoothPshOn Ω b)
    (hseq : ∀ j, IsSmoothPshOn Ω (u' j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x))) :
    IsLocallyBoundedPshOn Ω (fun x => smoothMax (u x) (b x)) := by
  let f := fun j x => smoothMax (u' j x) (b x)
  have hf (j : ℕ) : IsSmoothPshOn Ω (f j) := isSmoothPshOn_smoothMax (hseq j) hb
  have hantiE (x : ComplexModel n) (hx : x ∈ Ω) : Antitone (fun j => (f j x : EReal)) :=
    fun _ _ hj => EReal.coe_le_coe_iff.mpr (monotone_smoothMax_left (b x) (hanti x hx hj))
  have hpsh : PlurisubharmonicOn (fun x => ⨅ j, (f j x : EReal)) Ω :=
    DiscPshOn.plurisubharmonicOn_iInf_of_antitone Ω.isOpen (fun j => (hf j).2.1.discPshOn) hantiE
  have hEq (x : ComplexModel n) (hx : x ∈ Ω) :
      (⨅ j, (f j x : EReal)) = (smoothMax (u x) (b x) : EReal) :=
    tendsto_nhds_unique (tendsto_atTop_iInf (hantiE x hx))
      (EReal.tendsto_coe.mpr (tendsto_smoothMax_left (b x) (hlim x hx)))
  refine ⟨fun x hx => (hpsh x hx).congr ?_, ?_⟩
  · filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact hEq y hy
  · intro x hx
    obtain ⟨V, hVo, hxV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure
      isCompact_singleton Ω.isOpen (singleton_subset_iff.mpr hx)
    obtain ⟨Cu, _, hCu⟩ := hu.exists_compact_abs_bound hVc hVΩ
    obtain ⟨Cb, _, hCb⟩ := (isLocallyBoundedPshOn_of_isSmoothPshOn hb).exists_compact_abs_bound hVc hVΩ
    let S := Icc (-Cu) Cu ×ˢ Icc (-Cb) Cb
    have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
    obtain ⟨C, hC⟩ := (hS.image contDiff_smoothMax.continuous.abs).bddAbove
    exact ⟨⟨V, hVo⟩, hxV (mem_singleton x), subset_closure.trans hVΩ, C,
      fun y hy => hC ⟨(u y, b y),
        ⟨abs_le.mp (hCu y (subset_closure hy)), abs_le.mp (hCb y (subset_closure hy))⟩, rfl⟩⟩

private theorem weightedLeviDistribution_extendTest_congr
    {V W : Opens (ComplexModel n)} {uV pV : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (huV : IsLocallyBoundedPshOn V uV) (hpV : IsLocallyBoundedPshOn V pV)
    (hWΩ : W ≤ Ω) (hWV : W ≤ V) (huEq : EqOn u uV W) (hpEq : EqOn p pV W)
    (v : ComplexModel n) (φ : 𝓓(W, ℝ)) :
    weightedLeviDistribution hu hp v (extendTest hWΩ φ) =
      weightedLeviDistribution huV hpV v (extendTest hWV φ) := by
  rw [weightedLeviDistribution_extendTest, weightedLeviDistribution_extendTest]
  exact congrArg (fun T : 𝓓'(W, ℝ) => T φ)
    (weightedLeviDistribution_congr _ _ _ _ huEq hpEq v)

set_option maxHeartbeats 750000 in
/-- Joint test convergence for a test supported in a ball with a larger
closed concentric ball still inside the domain. -/
theorem tendsto_weightedLeviDistribution_of_tsupport_subset_ball
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hu' : ∀ j, IsSmoothPshOn Ω (u' j)) (hp' : ∀ j, IsSmoothPshOn Ω (p' j))
    (huanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hulim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x)))
    (hpanti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    (z : ComplexModel n) {r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hr : r₀ < r)
    (hB : closedBall z r ⊆ Ω) (v : ComplexModel n) (φ : 𝓓(Ω, ℝ))
    (hφ : tsupport φ ⊆ ball z r₀) :
    Tendsto (fun j => weightedLeviDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j))
      (isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)) v φ) atTop
      (𝓝 (weightedLeviDistribution hu hp v φ)) := by
  let V := ballDomain z r
  let W := ballDomain z r₀
  have hVΩ : V ≤ Ω := ball_subset_closedBall.trans hB
  have hWV : W ≤ V := ball_subset_ball hr.le
  have hWΩ : W ≤ Ω := hWV.trans hVΩ
  let ψ : 𝓓(W, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
  have hφeq : extendTest hWΩ ψ = φ := TestFunction.ext fun _ => rfl
  let huL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j)
  let hpL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)
  obtain ⟨Cu, hCu, huB⟩ := exists_compact_abs_bound_of_antitone hu huL huanti hulim
    (isCompact_closedBall z r) hB
  obtain ⟨Cp, _, hpB⟩ := exists_compact_abs_bound_of_antitone hp hpL hpanti hplim
    (isCompact_closedBall z r) hB
  let C := max Cu Cp
  have hC : 0 ≤ C := hCu.trans (le_max_left _ _)
  have huC (j : ℕ) (x : ComplexModel n) (hx : x ∈ V) : |u' j x| ≤ C :=
    (huB j x (ball_subset_closedBall hx)).trans (le_max_left _ _)
  have hpC (j : ℕ) (x : ComplexModel n) (hx : x ∈ V) : |p' j x| ≤ C :=
    (hpB j x (ball_subset_closedBall hx)).trans (le_max_right _ _)
  obtain ⟨b, hb, hbInner, K, hK, hKV, hbOuter⟩ := exists_quadratic_boundary_barrier z hr₀ hr hC
  let uV := fun x => smoothMax (u x) (b x)
  let pV := fun x => smoothMax (p x) (b x)
  let uV' := fun j x => smoothMax (u' j x) (b x)
  let pV' := fun j x => smoothMax (p' j x) (b x)
  have huVS (j : ℕ) : IsSmoothPshOn V (uV' j) :=
    isSmoothPshOn_smoothMax (isSmoothPshOn_mono (hu' j) hVΩ) hb
  have hpVS (j : ℕ) : IsSmoothPshOn V (pV' j) :=
    isSmoothPshOn_smoothMax (isSmoothPshOn_mono (hp' j) hVΩ) hb
  have huV : IsLocallyBoundedPshOn V uV :=
    isLocallyBoundedPshOn_smoothMax_of_decreasing (IsLocallyBoundedPshOn.mono hu hVΩ)
      hb (fun j => isSmoothPshOn_mono (hu' j) hVΩ)
      (fun x hx => huanti x (hVΩ hx)) (fun x hx => hulim x (hVΩ hx))
  have hpV : IsLocallyBoundedPshOn V pV :=
    isLocallyBoundedPshOn_smoothMax_of_decreasing (IsLocallyBoundedPshOn.mono hp hVΩ)
      hb (fun j => isSmoothPshOn_mono (hp' j) hVΩ)
      (fun x hx => hpanti x (hVΩ hx)) (fun x hx => hplim x (hVΩ hx))
  have huLim (x : ComplexModel n) (hx : x ∈ V) : Tendsto (fun j => uV' j x) atTop (𝓝 (uV x)) :=
    tendsto_smoothMax_left (b x) (hulim x (hVΩ hx))
  have hpLim (x : ComplexModel n) (hx : x ∈ V) : Tendsto (fun j => pV' j x) atTop (𝓝 (pV x)) :=
    tendsto_smoothMax_left (b x) (hplim x (hVΩ hx))
  have hOutside (j m : ℕ) : EqOn (uV' j) (pV' m) ((V : Set (ComplexModel n)) \ K) := by
    intro x hx
    have hxB := hbOuter x hx
    change smoothMax (u' j x) (b x) = smoothMax (p' m x) (b x)
    rw [smoothMax_eq_right (by linarith [(abs_le.mp (huC j x hx.1)).2]),
      smoothMax_eq_right (by linarith [(abs_le.mp (hpC m x hx.1)).2])]
  have huInside (j : ℕ) : EqOn (u' j) (uV' j) W := by
    intro x hx
    have hxB := hbInner x (ball_subset_closedBall hx)
    exact (smoothMax_eq_left (by linarith [(abs_le.mp (huC j x (hWV hx))).1])).symm
  have hpInside (j : ℕ) : EqOn (p' j) (pV' j) W := by
    intro x hx
    have hxB := hbInner x (ball_subset_closedBall hx)
    exact (smoothMax_eq_left (by linarith [(abs_le.mp (hpC j x (hWV hx))).1])).symm
  have huEq : EqOn u uV W := fun x hx =>
    tendsto_nhds_unique (hulim x (hWΩ hx))
      ((huLim x (hWV hx)).congr' (Eventually.of_forall fun j => (huInside j hx).symm))
  have hpEq : EqOn p pV W := fun x hx =>
    tendsto_nhds_unique (hplim x (hWΩ hx))
      ((hpLim x (hWV hx)).congr' (Eventually.of_forall fun j => (hpInside j hx).symm))
  have h := tendsto_weightedLeviDistribution_of_eq_off_compact huV hpV huVS hpVS
    (fun x hx _ _ hj => monotone_smoothMax_left (b x) (huanti x (hVΩ hx) hj)) huLim
    (fun x hx _ _ hj => monotone_smoothMax_left (b x) (hpanti x (hVΩ hx) hj)) hpLim
    hK hKV hOutside v (extendTest hWV ψ)
  rw [← hφeq, weightedLeviDistribution_extendTest_congr hu hp huV hpV hWΩ hWV huEq hpEq]
  exact h.congr' (Eventually.of_forall fun j =>
    (weightedLeviDistribution_extendTest_congr (huL j) (hpL j)
      (isLocallyBoundedPshOn_of_isSmoothPshOn (huVS j))
      (isLocallyBoundedPshOn_of_isSmoothPshOn (hpVS j)) hWΩ hWV
      (huInside j) (hpInside j) v ψ).symm)

end KEBall.BedfordTaylor
