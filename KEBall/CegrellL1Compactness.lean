import KEBall.CegrellL1RegularizedFamily
import KEBall.CegrellSublevelClosed
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Compactness of finite-energy sublevels on the ball
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

/-- The negative real representative of the potential as an (L^1) function. -/
noncomputable def negativePotentialL1 (hn : 0 < n) {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) : Lp ℝ 1 (volume : Measure (ComplexModel n)) :=
  (integrable_negativePotential hn hu).toL1 (negativePotential u)

private theorem dist_toL1_eq_integral_abs_sub {f g : ComplexModel n → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ x, |f x - g x| := by
  rw [dist_edist, Integrable.edist_toL1_toL1]
  simp only [edist_dist, Real.dist_eq]
  have hi : Integrable (fun x => |f x - g x|) volume := (hf.sub hg).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => abs_nonneg _)]
  exact ENNReal.toReal_ofReal (integral_nonneg fun x => abs_nonneg _)

private theorem dist_L1_of_uniform_bound {f g : ComplexModel n → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    {W : Set (ComplexModel n)} (hW : IsCompact W)
    (h₀ : ∀ x ∉ W, f x = 0 ∧ g x = 0)
    {d : ℝ} (hd : ∀ x ∈ W, |f x - g x| ≤ d) :
    dist (hf.toL1 f) (hg.toL1 g) ≤ d * (volume W).toReal := by
  rw [dist_toL1_eq_integral_abs_sub,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := W)
      (fun x hx => by rw [(h₀ x hx).1, (h₀ x hx).2, sub_self, abs_zero])]
  let : IsFiniteMeasure ((volume : Measure (ComplexModel n)).restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hW.measure_lt_top⟩
  calc
    _ ≤ ∫ _ in W, d := by
      apply integral_mono_ae (Integrable.restrict (hf.sub hg).abs) (integrable_const d)
      filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
      exact hd x hx
    _ = _ := by rw [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]

private theorem totallyBounded_range_boundedPotentialL1 (hn : 0 < n)
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsE0 (complexUnitBall n) (p j))
    {M : ℝ≥0∞} (hMfin : M < ⊤) (hM : ∀ j, boundedEnergy (hp j) ≤ M) :
    TotallyBounded (range fun j => negativePotentialL1 hn (hp j).isE1) := by
  classical
  let F (j : ℕ) := negativePotentialL1 hn (hp j).isE1
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨g, A, L, hA, hL, hSupp, hClose⟩ := exists_lipschitz_approximation_of_boundedEnergy hn
    hp hMfin hM (show 0 < ε / 3 by positivity)
  let B := complexUnitBall n
  let W := closure (B : Set (ComplexModel n))
  have hW : IsCompact W := isCompact_closure_complexUnitBall n
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let G (j : ℕ) : W →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => g j x, (hL j).continuous.comp continuous_subtype_val⟩
  have hEqui : Equicontinuous ((↑) : range G → W → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro a ha
    let δ := a / ((L : ℝ) + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    refine ⟨δ, hδ, fun y hy q => ?_⟩
    obtain ⟨j, hj⟩ := q.property
    have h := (hL j).dist_le_mul (x : ComplexModel n) (y : ComplexModel n)
    have hxy : dist (x : ComplexModel n) (y : ComplexModel n) < δ := by
      rw [dist_comm]
      exact hy
    rw [← hj]
    change dist (g j x) (g j y) < a
    refine h.trans_lt ((mul_le_mul_of_nonneg_left hxy.le L.coe_nonneg).trans_lt ?_)
    have hδmul : ((L : ℝ) + 1) * δ = a := by dsimp [δ]; field_simp
    linarith
  have hCompact : IsCompact (closure (range G)) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-(A : ℝ)) (A : ℝ)) isCompact_Icc (range G)
      (by
        rintro _ x ⟨j, rfl⟩
        exact abs_le.mp (hA j x)) hEqui
  let m := (volume W).toReal
  let δ := (ε / 3) / (m + 1)
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨T, hTG, hTfin, hCover⟩ := Metric.finite_approx_of_totallyBounded
    (hCompact.totallyBounded.subset subset_closure) δ hδ
  let index : (W →ᵇ ℝ) → ℕ := Function.invFun G
  refine ⟨(F ∘ index) '' T, hTfin.image _, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi := hCover (mem_range_self i)
  simp only [mem_iUnion, mem_ball] at hi
  obtain ⟨q, hq, hdist⟩ := hi
  let j := index q
  have hj : G j = q := Function.invFun_eq (hTG hq)
  simp only [mem_iUnion, mem_ball]
  refine ⟨F j, ⟨q, hq, rfl⟩, ?_⟩
  have hg (i : ℕ) : Integrable (g i) volume :=
    (hL i).continuous.integrable_of_hasCompactSupport
      (hW.of_isClosed_subset (isClosed_tsupport _) ((hSupp i).trans subset_closure))
  let U (i : ℕ) := (hg i).toL1 (g i)
  have hFU (i : ℕ) : dist (F i) (U i) < ε / 3 := by
    change dist ((integrable_negativePotential hn (hp i).isE1).toL1
      (negativePotential (fun x => (p i x : EReal)))) ((hg i).toL1 (g i)) < ε / 3
    rw [dist_toL1_eq_integral_abs_sub]
    exact hClose i
  have hUU : dist (U i) (U j) ≤ δ * m := by
    apply dist_L1_of_uniform_bound (hg i) (hg j) hW
    · intro x hx
      exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (subset_closure (hSupp i h))),
        image_eq_zero_of_notMem_tsupport (fun h => hx (subset_closure (hSupp j h)))⟩
    · intro x hx
      have hd := BoundedContinuousFunction.dist_coe_le_dist (f := G i) (g := G j) (⟨x, hx⟩ : W)
      rw [hj] at hd
      have h := hd.trans hdist.le
      rw [← hj, Real.dist_eq] at h
      exact h
  have hmid : δ * m < ε / 3 := by
    have he : δ * (m + 1) = ε / 3 := by dsimp [δ]; field_simp
    linarith
  exact (dist_triangle4 (F i) (U i) (U j) (F j)).trans_lt (by
    have h₁ := hFU i
    have h₂ := hUU.trans_lt hmid
    have h₃ : dist (U j) (F j) < ε / 3 := (dist_comm _ _).trans_lt (hFU j)
    linarith)

theorem tendsto_negativePotentialL1_of_E1Approximation (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u) :
    Tendsto (fun j => negativePotentialL1 hn (p.term_mem j).isE1) atTop
      (𝓝 (negativePotentialL1 hn hu)) := by
  let B := complexUnitBall n
  let f := negativePotential u
  let g (j : ℕ) := negativePotential (fun x => (p.term j x : EReal))
  have hF := (ae_restrict_iff' B.isOpen.measurableSet).mp (hu.ae_finite hn)
  have hlim : ∀ᵐ x ∂(volume : Measure (ComplexModel n)), Tendsto (fun j => g j x) atTop (𝓝 (f x)) := by
    filter_upwards [hF] with x hx
    by_cases hxB : x ∈ (complexUnitBall n : Set (ComplexModel n))
    · have ht := ((EReal.tendsto_toReal (hx hxB).1 (hx hxB).2).comp (p.pointwise x hxB)).neg
      simpa only [f, g, negativePotential, indicator_of_mem hxB, Function.comp_def, EReal.toReal_coe] using ht
    · simp only [f, g, negativePotential, indicator_of_notMem hxB]
      exact tendsto_const_nhds
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [negativePotentialL1, dist_toL1_eq_integral_abs_sub]
  have hI := integrable_negativePotential hn hu
  have hbound (j : ℕ) : ∀ᵐ x ∂(volume : Measure (ComplexModel n)), |g j x - f x| ≤ f x := by
    filter_upwards [hF] with x hx
    by_cases hxB : x ∈ (complexUnitBall n : Set (ComplexModel n))
    · have hp := EReal.toReal_le_toReal (p.le_term j x hxB) (hx hxB).2 (EReal.coe_ne_top _)
      have hle : g j x ≤ f x := by
        simpa only [g, f, negativePotential, indicator_of_mem hxB, EReal.toReal_coe] using neg_le_neg hp
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith [negativePotential_nonneg hn (p.term_mem j).isE1 x]
    · simp only [f, g, negativePotential, indicator_of_notMem hxB, sub_self, abs_zero, le_rfl]
  have ht : Tendsto (fun j => ∫ x, |g j x - f x|) atTop (𝓝 (∫ _ : ComplexModel n, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence f
    · intro j
      exact ((integrable_negativePotential hn (p.term_mem j).isE1).sub hI).abs.aestronglyMeasurable
    · exact hI
    · intro j
      simpa only [Real.norm_eq_abs, abs_abs] using hbound j
    · filter_upwards [hlim] with x hx
      simpa only [sub_self, abs_zero] using (hx.sub (tendsto_const_nhds (x := f x))).abs
  simpa only [integral_zero] using ht

/-- Each sequence in a finite-energy sublevel has a subsequence
converging in (L^1) and almost everywhere to a potential in the same sublevel. -/
theorem exists_subseq_tendsto_of_energy_le (hn : 0 < n)
    {p : ℕ → ComplexModel n → EReal} (hp : ∀ j, IsE1 (complexUnitBall n) (p j))
    {M : ℝ≥0∞} (hMfin : M < ⊤) (hM : ∀ j, energy (hp j) ≤ M) :
    ∃ (v : ComplexModel n → EReal) (hv : IsE1 (complexUnitBall n) v) (φ : ℕ → ℕ),
      StrictMono φ ∧ energy hv ≤ M ∧
      Tendsto (fun j => negativePotentialL1 hn (hp (φ j))) atTop (𝓝 (negativePotentialL1 hn hv)) ∧
      ∀ᵐ x ∂(volume : Measure (ComplexModel n)).restrict (complexUnitBall n),
        Tendsto (fun j => p (φ j) x) atTop (𝓝 (v x)) := by
  let B := complexUnitBall n
  let μ := (volume : Measure (ComplexModel n)).restrict B
  let F (j : ℕ) := negativePotentialL1 hn (hp j)
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hex (j : ℕ) : ∃ (w : ComplexModel n → ℝ) (hw : IsE0 B w), boundedEnergy hw ≤ M ∧
      dist (negativePotentialL1 hn hw.isE1) (F j) < ε j := by
    obtain ⟨a⟩ := (hp j).2
    have ht := tendsto_negativePotentialL1_of_E1Approximation hn (hp j) a
    obtain ⟨i, hi⟩ := ((Metric.tendsto_nhds.mp ht) (ε j) (hε j)).exists
    exact ⟨a.term i, a.term_mem i, ((le_iSup (fun k => boundedEnergy (a.term_mem k)) i).trans_eq
      (energy_eq_iSup hn (hp j) a).symm).trans (hM j), hi⟩
  choose w hw hclose using hex
  let G (j : ℕ) := negativePotentialL1 hn (hw j).isE1
  have hG := totallyBounded_range_boundedPotentialL1 hn hw hMfin (fun j => (hclose j).1)
  have hK := hG.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨g, _, φ, hφ, hg⟩ := hK.tendsto_subseq (x := G) (fun j => subset_closure (mem_range_self j))
  have hF : Tendsto (fun j => F (φ j)) atTop (𝓝 g) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have he := (hεlim.comp hφ.tendsto_atTop).eventually_lt_const (half_pos hδ)
    filter_upwards [he, (Metric.tendsto_nhds.mp hg) (δ / 2) (half_pos hδ)] with j hj hgj
    change ε (φ j) < δ / 2 at hj
    change dist (G (φ j)) g < δ / 2 at hgj
    have hc : dist (F (φ j)) (G (φ j)) < ε (φ j) := by
      rw [dist_comm]
      exact (hclose (φ j)).2
    exact (dist_triangle _ (G (φ j)) _).trans_lt (by linarith [hc.trans hj])
  obtain ⟨ψ, hψ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  let σ := φ ∘ ψ
  have hσ : StrictMono σ := hφ.comp hψ
  have hfEq : ∀ᵐ x ∂(volume : Measure (ComplexModel n)), ∀ j,
      F (σ j) x = negativePotential (p (σ j)) x := by
    apply ae_all_iff.mpr
    intro j
    exact (integrable_negativePotential hn (hp (σ j))).coeFn_toL1
  have hAe : ∀ᵐ x ∂(volume : Measure (ComplexModel n)),
      Tendsto (fun j => negativePotential (p (σ j)) x) atTop (𝓝 (g x)) := by
    filter_upwards [hae, hfEq] with x hx he
    exact hx.congr he
  have hFin : ∀ᵐ x ∂μ, ∀ j, p (σ j) x ≠ ⊤ ∧ p (σ j) x ≠ ⊥ :=
    ae_all_iff.mpr fun j => (hp (σ j)).ae_finite hn
  have hP : ∀ᵐ x ∂μ, Tendsto (fun j => p (σ j) x) atTop (𝓝 ((-g x : ℝ) : EReal)) := by
    filter_upwards [ae_restrict_of_ae hAe, hFin, ae_restrict_mem B.isOpen.measurableSet] with x hx hf hxB
    apply (continuous_coe_real_ereal.continuousAt.tendsto.comp hx.neg).congr
    intro j
    change ((-negativePotential (p (σ j)) x : ℝ) : EReal) = _
    rw [negativePotential, indicator_of_mem hxB, neg_neg, EReal.coe_toReal (hf j).1 (hf j).2]
  obtain ⟨v, hv, hvE, hveq⟩ := exists_isE1_of_ae_tendsto_of_energy_le hn
    (fun j => hp (σ j)) hP hMfin (fun j => hM (σ j))
  have hlimit : g = negativePotentialL1 hn hv := by
    apply Lp.ext
    have hV := (ae_restrict_iff' B.isOpen.measurableSet).mp hveq
    filter_upwards [hV, hAe, (integrable_negativePotential hn hv).coeFn_toL1] with x hx ha hneg
    change g x = negativePotentialL1 hn hv x
    rw [show negativePotentialL1 hn hv x = negativePotential v x from hneg]
    by_cases hxB : x ∈ (complexUnitBall n : Set (ComplexModel n))
    · rw [negativePotential, indicator_of_mem hxB, hx hxB, EReal.toReal_coe, neg_neg]
    · rw [negativePotential, indicator_of_notMem hxB]
      have h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (g x)) := by
        simpa only [negativePotential, indicator_of_notMem hxB] using ha
      exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  refine ⟨v, hv, σ, hσ, hvE, hlimit ▸ hF.comp hψ.tendsto_atTop, ?_⟩
  filter_upwards [hP, hveq] with x hx he
  rwa [he]

end KEBall.Cegrell
