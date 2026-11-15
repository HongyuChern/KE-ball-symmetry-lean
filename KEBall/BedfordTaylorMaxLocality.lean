import KEBall.BedfordTaylorNonsmoothWeights

/-!
# Locality of the bounded Monge–Ampère operator under maxima
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

theorem locallyBoundedPsh_max (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) :
    IsLocallyBoundedPshOn Ω (fun x => max (u x) (v x)) := by
  refine ⟨?_, ?_⟩
  · have he : (fun x => ((max (u x) (v x) : ℝ) : EReal)) =
        (fun x => max (u x : EReal) (v x : EReal)) := by
      funext x
      by_cases h : u x ≤ v x
      · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
      · have hl := le_of_not_ge h
        rw [max_eq_left hl, max_eq_left (EReal.coe_le_coe_iff.mpr hl)]
    rw [he]
    exact hu.1.max hv.1
  · intro x hx
    obtain ⟨U, hxU, hUΩ, M, hM⟩ := hu.2 x hx
    obtain ⟨V, hxV, hVΩ, N, hN⟩ := hv.2 x hx
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, inf_le_left.trans hUΩ, max M N, fun y hy => ?_⟩
    have hm := abs_le.mp (hM y hy.1)
    have hn := abs_le.mp (hN y hy.2)
    exact abs_le.mpr ⟨(neg_le_neg (le_max_left M N)).trans (hm.1.trans (le_max_left _ _)),
      max_le (hm.2.trans (le_max_left _ _)) (hn.2.trans (le_max_right _ _))⟩

private theorem integral_test_mul_sub {p : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    (hp : IsLocallyBoundedPshOn Ω p) (φ : 𝓓(Ω, ℝ)) :
    (∫ x, φ x * (u x - v x) ∂topMeasure hp) =
      (∫ x, φ x * u x ∂topMeasure hp) - ∫ x, φ x * v x ∂topMeasure hp := by
  let μ := diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => p) (fun _ => hp)) id
  let : μ.Regular := diagonalMeasure_regular _ _
  simp only [integral_topMeasure_map, mul_sub]
  simpa only [mul_sub] using congrArg (fun a : ℝ => (Real.pi ^ n)⁻¹ * a)
    (integral_sub (integrable_test_mul_psh hu μ φ) (integrable_test_mul_psh hv μ φ))

private theorem integral_max_eq_of_smooth (hu : IsSmoothPshOn Ω u)
    (hv : IsSmoothPshOn Ω v)
    (φ : 𝓓(Ω, ℝ)) :
    (∫ x, φ x * (max (u x) (v x) - v x) ∂topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu)) =
      ∫ x, φ x * (max (u x) (v x) - v x) ∂topMeasure
        (locallyBoundedPsh_max (isLocallyBoundedPshOn_of_isSmoothPshOn hu)
          (isLocallyBoundedPshOn_of_isSmoothPshOn hv)) := by
  let G : Opens (ComplexModel n) := ⟨{x ∈ Ω | v x < u x}, by
    have he : {x ∈ Ω | v x < u x} = (Ω : Set (ComplexModel n)) ∩ (u - v) ⁻¹' Ioi 0 := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi, Pi.sub_apply, sub_pos]
      rfl
    rw [he]
    exact (hu.1.continuousOn.sub hv.1.continuousOn).isOpen_inter_preimage Ω.isOpen isOpen_Ioi⟩
  have hG : G ≤ Ω := fun _ hx => hx.1
  let f := fun x => φ x * (max (u x) (v x) - v x)
  have hzero : ∀ x ∉ G, f x = 0 := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · have huc : u x ≤ v x := le_of_not_gt fun h => hx ⟨hxΩ, h⟩
      simp only [f, max_eq_right huc, sub_self, mul_zero]
    · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hxΩ (φ.tsupport_subset hs))
      simp only [f, hφ, zero_mul]
  have hEq : EqOn u (fun x => max (u x) (v x)) G := by
    intro x hx
    have h : v x < u x := hx.2
    exact (max_eq_left h.le).symm
  change (∫ x, f x ∂_) = ∫ x, f x ∂_
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ :=
      topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu)) hzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ :=
      topMeasure (locallyBoundedPsh_max (isLocallyBoundedPshOn_of_isSmoothPshOn hu)
          (isLocallyBoundedPshOn_of_isSmoothPshOn hv))) hzero,
    topMeasure_restrict _ hG, topMeasure_restrict _ hG,
    topMeasure_congr _ _ hEq]

/-- After weighting by the nonnegative gap between the maximum and the second
potential, the first potential and the maximum agree on compact tests. -/
theorem integral_weighted_topMeasure_max_eq (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) (φ : 𝓓(Ω, ℝ)) :
    (∫ x, φ x * (max (u x) (v x) - v x) ∂topMeasure hu) =
      ∫ x, φ x * (max (u x) (v x) - v x) ∂topMeasure (locallyBoundedPsh_max hu hv) := by
  obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let W : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hrel : RelativelyCompactIn W Ω := ⟨hVc, hVΩ⟩
  have hWΩ : W ≤ Ω := subset_closure.trans hVΩ
  let ψ : 𝓓(W, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩
  let f := fun x => ψ x * (max (u x) (v x) - v x)
  have hzero : ∀ x ∉ W, f x = 0 := fun x hx => by
    have hφ : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (ψ.tsupport_subset hs))
    simp only [f, hφ, zero_mul]
  change (∫ x, f x ∂topMeasure hu) = ∫ x, f x ∂topMeasure (locallyBoundedPsh_max hu hv)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := topMeasure hu) hzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := topMeasure (locallyBoundedPsh_max hu hv)) hzero,
    topMeasure_restrict _ hWΩ, topMeasure_restrict _ hWΩ]
  let huW := IsLocallyBoundedPshOn.mono hu hWΩ
  let hvW := IsLocallyBoundedPshOn.mono hv hWΩ
  obtain ⟨p, hp⟩ := exists_decreasingMollifierApproximation hu hrel
  obtain ⟨q, hq⟩ := exists_decreasingMollifierApproximation hv hrel
  let hpL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp.1 j)
  let hqL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hq.1 j)
  let r (j : ℕ) (x : ComplexModel n) := max (p j x) (q j x)
  let hrL := fun j => locallyBoundedPsh_max (hpL j) (hqL j)
  let hr := locallyBoundedPsh_max huW hvW
  have hrAnti (x : ComplexModel n) (hx : x ∈ W) : Antitone (fun j => r j x) :=
    fun _ _ hj => max_le_max (hp.2.1 x hx hj) (hq.2.1 x hx hj)
  have hrLim (x : ComplexModel n) (hx : x ∈ W) :
      Tendsto (fun j => r j x) atTop (𝓝 (max (u x) (v x))) :=
    (hp.2.2 x hx).max (hq.2.2 x hx)
  have h₁ := (tendsto_weightedTopMeasure_of_decreasing hr huW hrL hpL
    hrAnti hp.2.1 hrLim hp.2.2 ψ).sub
    (tendsto_weightedTopMeasure_of_decreasing hvW huW hqL hpL
      hq.2.1 hp.2.1 hq.2.2 hp.2.2 ψ)
  have h₂ := (tendsto_weightedTopMeasure_of_decreasing hr hr hrL hrL
    hrAnti hrAnti hrLim hrLim ψ).sub
    (tendsto_weightedTopMeasure_of_decreasing hvW hr hqL hrL
      hq.2.1 hrAnti hq.2.2 hrLim ψ)
  have hEq (j : ℕ) :
      (∫ x, ψ x * r j x ∂topMeasure (hpL j)) - (∫ x, ψ x * q j x ∂topMeasure (hpL j)) =
        (∫ x, ψ x * r j x ∂topMeasure (hrL j)) - ∫ x, ψ x * q j x ∂topMeasure (hrL j) := by
    rw [← integral_test_mul_sub (hrL j) (hqL j) (hpL j) ψ,
      ← integral_test_mul_sub (hrL j) (hqL j) (hrL j) ψ]
    exact integral_max_eq_of_smooth (hp.1 j) (hq.1 j) ψ
  change (∫ x, ψ x * (max (u x) (v x) - v x) ∂topMeasure huW) =
    ∫ x, ψ x * (max (u x) (v x) - v x) ∂topMeasure hr
  rw [integral_test_mul_sub hr hvW huW ψ, integral_test_mul_sub hr hvW hr ψ]
  exact tendsto_nhds_unique h₁ (h₂.congr fun j => (hEq j).symm)

private theorem regular_withDensity_of_localBound {g : ComplexModel n → ℝ}
    (hg : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω → ∃ C, ∀ x ∈ K, g x ≤ C) (μ : Measure Ω) [μ.Regular] :
    (μ.withDensity (fun x : Ω => ENNReal.ofReal (g x))).Regular := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let : IsFiniteMeasureOnCompacts (μ.withDensity (fun x : Ω => ENNReal.ofReal (g x))) :=
    ⟨fun K hK => by
      have hKC : IsCompact (Subtype.val '' K : Set (ComplexModel n)) :=
        hK.image continuous_subtype_val
      obtain ⟨C, hC⟩ := hg _ hKC (fun _ ⟨x, _, hx⟩ => hx ▸ x.property)
      rw [withDensity_apply _ hK.measurableSet]
      calc
        _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal C ∂μ.restrict K := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          exact ENNReal.ofReal_le_ofReal (hC x ⟨x, hx, rfl⟩)
        _ < ⊤ := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top⟩
  infer_instance

theorem measurableSet_lt_of_locallyBoundedPsh (hv : IsLocallyBoundedPshOn Ω v)
    (hu : IsLocallyBoundedPshOn Ω u) :
    MeasurableSet {x ∈ Ω | v x < u x} := by
  have he : MeasurableEmbedding (Subtype.val : Ω → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet
  have hH : MeasurableSet {x : Ω | v x < u x} :=
    measurableSet_lt (measurable_subtype_of_locallyBoundedPsh hv)
      (measurable_subtype_of_locallyBoundedPsh hu)
  have hEq : (Subtype.val : Ω → ComplexModel n) '' {x : Ω | v x < u x} =
      {x ∈ Ω | v x < u x} := by
    ext x
    exact ⟨fun ⟨y, hy, heq⟩ => heq ▸ ⟨y.property, hy⟩, fun hx => ⟨⟨x, hx.1⟩, hx.2, rfl⟩⟩
  rw [← hEq]
  exact he.measurableSet_image.2 hH

/-- The bounded Monge–Ampère measure is local on the Borel set where the first
potential strictly exceeds the second. -/
theorem topMeasure_restrict_gt_max (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) :
    let G : Set (ComplexModel n) := {x ∈ Ω | v x < u x}
    (topMeasure hu).restrict G = (topMeasure (locallyBoundedPsh_max hu hv)).restrict G := by
  let hq := locallyBoundedPsh_max hu hv
  let g := fun x => max (u x) (v x) - v x
  have hg (K : Set (ComplexModel n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      ∃ C, ∀ x ∈ K, g x ≤ C := by
    obtain ⟨A, _, hA⟩ := hq.exists_compact_abs_bound hK hKΩ
    obtain ⟨B, _, hB⟩ := hv.exists_compact_abs_bound hK hKΩ
    exact ⟨A + B, fun x hx => sub_le_iff_le_add.mpr
      ((abs_le.mp (hA x hx)).2.trans (by linarith [(abs_le.mp (hB x hx)).1]))⟩
  let μ := diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => hu)) id
  let ν := diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ x => max (u x) (v x)) (fun _ => hq)) id
  let : μ.Regular := diagonalMeasure_regular
    (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => hu)) id
  let : ν.Regular := diagonalMeasure_regular
    (mixedProduct_positive (k := n) (u := fun _ x => max (u x) (v x)) (fun _ => hq)) id
  let d : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (g x)
  have hd : Measurable d := ((measurable_subtype_of_locallyBoundedPsh hq).sub
    (measurable_subtype_of_locallyBoundedPsh hv)).ennreal_ofReal
  let : (μ.withDensity d).Regular := regular_withDensity_of_localBound hg μ
  let : (ν.withDensity d).Regular := regular_withDensity_of_localBound hg ν
  have hmeasure : μ.withDensity d = ν.withDensity d := by
    apply measure_eq_of_smooth_test
    intro φ
    rw [integral_withDensity_eq_integral_toReal_smul hd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul hd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have h := integral_weighted_topMeasure_max_eq hu hv φ
    rw [integral_topMeasure_map hu, integral_topMeasure_map hq] at h
    change (Real.pi ^ n)⁻¹ * (∫ x : Ω, φ x * g x ∂μ) =
      (Real.pi ^ n)⁻¹ * ∫ x : Ω, φ x * g x ∂ν at h
    have h' := mul_left_cancel₀ (by positivity : (Real.pi ^ n)⁻¹ ≠ 0) h
    have hnonneg (x : Ω) : 0 ≤ g x := sub_nonneg.mpr (le_max_right _ _)
    simpa only [d, ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul, mul_comm] using h'
  let H : Set Ω := {x | v x < u x}
  have hH : MeasurableSet H := measurableSet_lt (measurable_subtype_of_locallyBoundedPsh hv)
      (measurable_subtype_of_locallyBoundedPsh hu)
  have hpos (ρ : Measure Ω) : ∀ᵐ x ∂ρ.restrict H, d x ≠ 0 := by
    filter_upwards [ae_restrict_mem hH] with x hx
    have hlt : v x < u x := hx
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hlt.trans_le (le_max_left _ _))))
  have hdtop (ρ : Measure Ω) : ∀ᵐ x ∂ρ.restrict H, d x ≠ ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  have hrestrict : μ.restrict H = ν.restrict H := by
    have he := congrArg (fun ρ : Measure Ω => (ρ.restrict H).withDensity (fun x => (d x)⁻¹)) hmeasure
    simpa only [restrict_withDensity hH, withDensity_inv_same hd (hpos μ) (hdtop μ),
      withDensity_inv_same hd (hpos ν) (hdtop ν)] using he
  let G : Set (ComplexModel n) := {x ∈ Ω | v x < u x}
  have hPre : (Subtype.val : Ω → ComplexModel n) ⁻¹' G = H := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
  have he : MeasurableEmbedding (Subtype.val : Ω → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet
  have hμG : (μ.map (Subtype.val : Ω → ComplexModel n)).restrict G =
      (μ.restrict H).map Subtype.val := by
    exact (he.restrict_map μ G).trans (congrArg
      (fun S => (μ.restrict S).map (Subtype.val : Ω → ComplexModel n)) hPre)
  have hνG : (ν.map (Subtype.val : Ω → ComplexModel n)).restrict G =
      (ν.restrict H).map Subtype.val := by
    exact (he.restrict_map ν G).trans (congrArg
      (fun S => (ν.restrict S).map (Subtype.val : Ω → ComplexModel n)) hPre)
  change (ENNReal.ofReal ((Real.pi ^ n)⁻¹) • μ.map Subtype.val).restrict G =
    (ENNReal.ofReal ((Real.pi ^ n)⁻¹) • ν.map Subtype.val).restrict G
  rw [Measure.restrict_smul, Measure.restrict_smul, hμG, hνG, hrestrict]

end KEBall.BedfordTaylor
