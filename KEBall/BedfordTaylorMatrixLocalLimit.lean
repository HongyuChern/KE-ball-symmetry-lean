import KEBall.BedfordTaylorJointWeightLimit
import KEBall.BedfordTaylorMatrixBoundaryLimit

/-!
# Localization of joint weighted convergence
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

private theorem weightedMixedProductQuadratic_restrict (p : PshApproximation Ω)
    (f : Fin k → PshApproximation Ω) {W : Opens (ComplexModel n)} (hW : W ≤ Ω)
    (a : CoordinateTuple n k → ℂ) (φ : 𝓓(W, ℝ)) :
    weightedMixedProductQuadratic (p.restrict hW) (fun i => (f i).restrict hW) a φ =
      weightedMixedProductQuadratic p f a (extendTest hW φ) := by
  rw [weightedMixedProductQuadratic_apply, weightedMixedProductQuadratic_apply]
  let T := mixedProduct (u := fun i => (f i).limit) (fun i => (f i).locallyBounded)
  let hT := mixedProduct_positive (u := fun i => (f i).limit) (fun i => (f i).locallyBounded)
  have hμ : mixedProductQuadraticMeasure (fun i => (f i).restrict hW) a =
      quadraticMeasure (restrictCoordinateMatrix_isPositive hW hT) a :=
    quadraticMeasure_congr _ _ (mixedProduct_restrict (u := fun i => (f i).limit) hW
      (fun i => (f i).locallyBounded)) a
  rw [hμ]
  exact integral_weightedQuadraticMeasure_restrict hW hT a φ

private theorem weightedMixedProductQuadratic_congr
    (p q : PshApproximation Ω) (f g : Fin k → PshApproximation Ω)
    (hpq : EqOn p.limit q.limit Ω) (hfg : ∀ i, EqOn (f i).limit (g i).limit Ω)
    (a : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) :
    weightedMixedProductQuadratic p f a φ = weightedMixedProductQuadratic q g a φ := by
  rw [weightedMixedProductQuadratic_apply, weightedMixedProductQuadratic_apply]
  have hμ : mixedProductQuadraticMeasure f a = mixedProductQuadraticMeasure g a :=
    quadraticMeasure_congr _ _ (mixedProduct_congr (u := fun i => (f i).limit)
      (w := fun i => (g i).limit) (fun i => (f i).locallyBounded) (fun i => (g i).locallyBounded) hfg) a
  rw [hμ]
  exact integral_congr_ae (Eventually.of_forall fun x => congrArg (φ x * ·) (hpq x.property))

private theorem weightedMixedProductQuadratic_extendTest_congr
    {V W : Opens (ComplexModel n)} (hWΩ : W ≤ Ω) (hWV : W ≤ V)
    (p : PshApproximation Ω) (q : PshApproximation V)
    (f : Fin k → PshApproximation Ω) (g : Fin k → PshApproximation V)
    (hpq : EqOn p.limit q.limit W) (hfg : ∀ i, EqOn (f i).limit (g i).limit W)
    (a : CoordinateTuple n k → ℂ) (φ : 𝓓(W, ℝ)) :
    weightedMixedProductQuadratic p f a (extendTest hWΩ φ) =
      weightedMixedProductQuadratic q g a (extendTest hWV φ) := by
  rw [← weightedMixedProductQuadratic_restrict p f hWΩ,
    ← weightedMixedProductQuadratic_restrict q g hWV]
  exact weightedMixedProductQuadratic_congr _ _ _ _ hpq hfg a φ

private noncomputable def PshApproximation.smoothMaxWith (p : PshApproximation Ω)
    {b : ComplexModel n → ℝ} (hb : IsSmoothPshOn Ω b) : PshApproximation Ω where
  limit := fun x => smoothMax (p.limit x) (b x)
  term := fun j x => smoothMax (p.term j x) (b x)
  locallyBounded := isLocallyBoundedPshOn_smoothMax_of_decreasing p.locallyBounded hb
    p.approximation.1 p.approximation.2.1 p.approximation.2.2
  approximation := ⟨fun j => isSmoothPshOn_smoothMax (p.approximation.1 j) hb,
    fun x hx _ _ hj => monotone_smoothMax_left (b x) (p.approximation.2.1 x hx hj),
    fun x hx => tendsto_smoothMax_left (b x) (p.approximation.2.2 x hx)⟩

set_option maxHeartbeats 750000 in
theorem tendsto_weightedMixedProductQuadratic_of_tsupport_subset_ball
    (h : MixedProductMonotone n (k + 1)) (p : PshApproximation Ω)
    (f : Fin (k + 1) → PshApproximation Ω)
    (z : ComplexModel n) {r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hr : r₀ < r)
    (hB : closedBall z r ⊆ Ω) (a : CoordinateTuple n (k + 1) → ℂ) (φ : 𝓓(Ω, ℝ))
    (hφ : tsupport φ ⊆ ball z r₀) :
    Tendsto (fun j => weightedMixedProductQuadratic (p.atTerm j) (fun i => (f i).atTerm j) a φ)
      atTop (𝓝 (weightedMixedProductQuadratic p f a φ)) := by
  let V := ballDomain z r
  let W := ballDomain z r₀
  have hVΩ : V ≤ Ω := ball_subset_closedBall.trans hB
  have hWV : W ≤ V := ball_subset_ball hr.le
  have hWΩ : W ≤ Ω := hWV.trans hVΩ
  let ψ : 𝓓(W, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
  have hφeq : extendTest hWΩ ψ = φ := TestFunction.ext fun _ => rfl
  have hbound (q : PshApproximation Ω) : ∃ C ≥ 0,
      ∀ j x, x ∈ closedBall z r → |q.term j x| ≤ C :=
    exists_compact_abs_bound_of_antitone q.locallyBounded q.term_locallyBounded
      q.approximation.2.1 q.approximation.2.2 (isCompact_closedBall z r) hB
  obtain ⟨Cp, hCp, hpB⟩ := hbound p
  choose Cf hCf hfB using fun i => hbound (f i)
  let C := Cp + ∑ i, Cf i
  have hC : 0 ≤ C := add_nonneg hCp (Finset.sum_nonneg fun i _ => hCf i)
  have hpC (j : ℕ) (x : ComplexModel n) (hx : x ∈ V) : |p.term j x| ≤ C :=
    (hpB j x (ball_subset_closedBall hx)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hCf i))
  have hfC (i : Fin (k + 1)) (j : ℕ) (x : ComplexModel n) (hx : x ∈ V) :
      |(f i).term j x| ≤ C :=
    (hfB i j x (ball_subset_closedBall hx)).trans
      ((Finset.single_le_sum (fun l _ => hCf l) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left hCp))
  obtain ⟨b, hb, hbInner, K, hK, hKV, hbOuter⟩ :=
    exists_quadratic_boundary_barrier z hr₀ hr hC
  let modify (q : PshApproximation Ω) := (q.restrict hVΩ).smoothMaxWith hb
  have hOut (q : PshApproximation Ω) (hq : ∀ j x, x ∈ V → |q.term j x| ≤ C) :
      (modify q).hasCommonBoundary b K := by
    intro j x hx
    change smoothMax (q.term j x) (b x) = b x
    exact smoothMax_eq_right (by linarith [hbOuter x hx, (abs_le.mp (hq j x hx.1)).2])
  have hIn (q : PshApproximation Ω) (hq : ∀ j x, x ∈ V → |q.term j x| ≤ C)
      (j : ℕ) : EqOn (q.term j) ((modify q).term j) W := by
    intro x hx
    change q.term j x = smoothMax (q.term j x) (b x)
    exact (smoothMax_eq_left (by linarith [hbInner x (ball_subset_closedBall hx),
      (abs_le.mp (hq j x (hWV hx))).1])).symm
  have hlimIn (q : PshApproximation Ω) (hq : ∀ j x, x ∈ V → |q.term j x| ≤ C) :
      EqOn q.limit (modify q).limit W := by
    intro x hx
    exact tendsto_nhds_unique (q.approximation.2.2 x (hWΩ hx))
      (((modify q).approximation.2.2 x (hWV hx)).congr fun j => (hIn q hq j hx).symm)
  have hl := tendsto_weightedMixedProductQuadratic_of_commonBoundary h (modify p)
    (fun i => modify (f i)) hK hKV (hOut p hpC) (fun i => hOut (f i) (hfC i)) a (extendTest hWV ψ)
  rw [← hφeq, weightedMixedProductQuadratic_extendTest_congr hWΩ hWV p (modify p) f
    (fun i => modify (f i)) (hlimIn p hpC) (fun i => hlimIn (f i) (hfC i))]
  apply hl.congr
  intro j
  exact (weightedMixedProductQuadratic_extendTest_congr hWΩ hWV (p.atTerm j)
    ((modify p).atTerm j) (fun i => (f i).atTerm j) (fun i => (modify (f i)).atTerm j)
    (hIn p hpC j) (fun i => hIn (f i) (hfC i) j) a ψ).symm

/-- Joint convergence for weighted quadratic coefficients on an arbitrary open set. -/
theorem tendsto_weightedMixedProductQuadratic (h : MixedProductMonotone n (k + 1))
    (p : PshApproximation Ω) (f : Fin (k + 1) → PshApproximation Ω)
    (a : CoordinateTuple n (k + 1) → ℂ) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => weightedMixedProductQuadratic (p.atTerm j) (fun i => (f i).atTerm j) a φ)
      atTop (𝓝 (weightedMixedProductQuadratic p f a φ)) := by
  classical
  let T := fun j => weightedMixedProductQuadratic (p.atTerm j) (fun i => (f i).atTerm j) a
  let S := weightedMixedProductQuadratic p f a
  change Tendsto (fun j => T j φ) atTop (𝓝 (S φ))
  have hrad (x : Ω) : ∃ r : ℝ, 0 < r ∧ closedBall (x : ComplexModel n) r ⊆ Ω := by
    obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp Ω.isOpen x x.property
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hB⟩
  choose r hr hB using hrad
  choose χ hχ₀ hχ₁ hχB using fun x => exists_test_on_inner_ball x (hr x) (hB x)
  have hlocal (x : Ω) : Tendsto (fun j => T j (χ x)) atTop (𝓝 (S (χ x))) :=
    tendsto_weightedMixedProductQuadratic_of_tsupport_subset_ball h p f
      x (half_pos (hr x)).le (half_lt_self (hr x)) (hB x) a (χ x) (hχB x)
  have hcover : tsupport φ ⊆ ⋃ x : Ω, ball (x : ComplexModel n) (r x / 4) := by
    intro y hy
    let x : Ω := ⟨y, φ.tsupport_subset hy⟩
    exact mem_iUnion.mpr ⟨x, mem_ball_self (div_pos (hr x) (by norm_num))⟩
  obtain ⟨F, hF⟩ := φ.hasCompactSupport.elim_finite_subcover
    (fun x : Ω => ball (x : ComplexModel n) (r x / 4)) (fun _ => isOpen_ball) hcover
  let η := ∑ x ∈ F, χ x
  have hηEval (y : ComplexModel n) : η y = ∑ x ∈ F, χ x y :=
    map_sum ({ toFun := fun ψ => ψ y, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      𝓓(Ω, ℝ) →+ ℝ) χ F
  have hη₀ (y : ComplexModel n) : 0 ≤ η y := by
    rw [hηEval]
    exact Finset.sum_nonneg (fun x _ => hχ₀ x y)
  have hη₁ (y : ComplexModel n) (hy : y ∈ tsupport φ) : 1 ≤ η y := by
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hF hy)
    obtain ⟨hxF, hyB⟩ := mem_iUnion.mp hx
    have h₁ : χ x y = 1 := hχ₁ x (ball_subset_closedBall hyB)
    have hle : χ x y ≤ ∑ x ∈ F, χ x y :=
      Finset.single_le_sum (fun z _ => hχ₀ z y) hxF
    simpa only [hηEval, h₁] using hle
  obtain ⟨C₀, hC₀⟩ :=
    (φ.hasCompactSupport.image_of_continuousOn φ.continuous.abs.continuousOn).bddAbove
  let C := max 0 C₀
  have hC₀' : 0 ≤ C := le_max_left _ _
  have hη (y : ComplexModel n) : |φ y| ≤ (C • η) y := by
    rw [smul_apply, smul_eq_mul]
    by_cases hy : y ∈ tsupport φ
    · exact ((hC₀ ⟨y, hy, rfl⟩).trans (le_max_right _ _)).trans
        (le_mul_of_one_le_right hC₀' (hη₁ y hy))
    · simp only [image_eq_zero_of_notMem_tsupport hy, abs_zero]
      exact mul_nonneg hC₀' (hη₀ y)
  apply tendsto_of_upper_of_dominating_test
    (fun ψ hψ _ hε => weightedMixedProductQuadratic_eventually_lt_add h p f a ψ hψ hε)
    (C • η) φ hη
  simp only [η, map_smul, map_sum, smul_eq_mul]
  exact (tendsto_finsetSum F (fun x _ => hlocal x)).const_mul C

end KEBall.BedfordTaylor
