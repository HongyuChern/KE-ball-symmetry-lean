import KEBall.BedfordTaylorMatrixBoundaryPairing
import KEBall.BedfordTaylorMixedApproximation
import KEBall.BedfordTaylorBoundaryWeightLimit

/-!
# Joint weighted convergence under a common boundary potential
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

noncomputable def mixedProductQuadraticMeasure (p : Fin k → PshApproximation Ω)
    (a : CoordinateTuple n k → ℂ) : Measure Ω :=
  quadraticMeasure (mixedProduct_positive (u := fun i => (p i).limit) (fun i => (p i).locallyBounded)) a

theorem mixedProductQuadraticMeasure_regular (p : Fin k → PshApproximation Ω)
    (a : CoordinateTuple n k → ℂ) : (mixedProductQuadraticMeasure p a).Regular :=
  quadraticMeasure_regular _ _

/-- A scalar coefficient after multiplication by a PSH weight. -/
noncomputable def weightedMixedProductQuadratic (p : PshApproximation Ω)
    (f : Fin k → PshApproximation Ω) (a : CoordinateTuple n k → ℂ) : 𝓓'(Ω, ℝ) :=
  letI := mixedProductQuadraticMeasure_regular f a
  weightRadonMeasure p.locallyBounded (mixedProductQuadraticMeasure f a)

theorem weightedMixedProductQuadratic_apply (p : PshApproximation Ω)
    (f : Fin k → PshApproximation Ω) (a : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) :
    weightedMixedProductQuadratic p f a φ =
      ∫ x : Ω, φ x * p.limit x ∂mixedProductQuadraticMeasure f a := by
  letI := mixedProductQuadraticMeasure_regular f a
  exact weightRadonMeasure_apply p.locallyBounded (mixedProductQuadraticMeasure f a) φ

private theorem weightedMixedProductQuadratic_mono (p q : PshApproximation Ω)
    (f : Fin k → PshApproximation Ω) (a : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ))
    (hφ : ∀ x, 0 ≤ φ x) (hle : ∀ x ∈ Ω, p.limit x ≤ q.limit x) :
    weightedMixedProductQuadratic p f a φ ≤ weightedMixedProductQuadratic q f a φ := by
  let μ := mixedProductQuadraticMeasure f a
  let : μ.Regular := mixedProductQuadraticMeasure_regular f a
  simp only [weightedMixedProductQuadratic_apply]
  exact integral_mono (integrable_test_mul_psh p.locallyBounded μ φ)
    (integrable_test_mul_psh q.locallyBounded μ φ)
    (fun x => mul_le_mul_of_nonneg_left (hle x x.property) (hφ x))

private theorem mixedProductQuadraticMeasure_perm (hsym : MixedProductSymmetric n k)
    (f : Fin k → PshApproximation Ω) (σ : Equiv.Perm (Fin k)) (a : CoordinateTuple n k → ℂ) :
    mixedProductQuadraticMeasure (f ∘ σ) a = mixedProductQuadraticMeasure f a :=
  quadraticMeasure_congr _ _
    (hsym Ω (fun i => (f i).limit) (fun i => (f i).locallyBounded) σ) a

private theorem weightedMixedProductQuadratic_swap
    (hsym : MixedProductSymmetric n (k + 1))
    {q : ComplexModel n → ℝ} (hq : IsSmoothPshOn Ω q)
    (f : Fin (k + 1) → PshApproximation Ω) (i : Fin (k + 1))
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (he : ∀ j, EqOn q ((f i).term j) ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (a : CoordinateTuple n (k + 1) → ℂ) :
    weightedMixedProductQuadratic (PshApproximation.constant hq) f a χ =
      weightedMixedProductQuadratic (f i) (Function.update f i (PshApproximation.constant hq)) a χ := by
  let σ := Equiv.swap (0 : Fin (k + 1)) i
  let v := Fin.tail (f ∘ σ)
  let Q := PshApproximation.constant hq
  have hperm (t : PshApproximation Ω) :
      (Function.update f i t) ∘ σ =
        Fin.cons (α := fun _ : Fin (k + 1) => PshApproximation Ω) t v := by
    funext r
    cases r using Fin.cases with
    | zero => simp [σ]
    | succ r =>
      have hn : σ r.succ ≠ i := by
        intro heq
        have hh : σ r.succ = σ 0 := heq.trans (Equiv.swap_apply_left _ _).symm
        exact Fin.succ_ne_zero r (σ.injective hh)
      simp only [Function.comp_apply, Function.update_of_ne hn, Fin.cons_succ]
      rfl
  have hf : f ∘ σ = Fin.cons (α := fun _ : Fin (k + 1) => PshApproximation Ω) (f i) v := by
    simpa only [Function.update_eq_self] using hperm (f i)
  rw [weightedMixedProductQuadratic_apply, weightedMixedProductQuadratic_apply,
    ← mixedProductQuadraticMeasure_perm hsym f σ, ← mixedProductQuadraticMeasure_perm hsym
      (Function.update f i Q) σ, hf, hperm Q]
  let vl (r : Fin k) := (v r).limit
  let vs (j : ℕ) (r : Fin k) := (v r).term j
  have hpair := integral_quadraticMeasure_mixedProduct_swap hq (f i).locallyBounded
    (f i).approximation.1 (f i).approximation.2.1 (f i).approximation.2.2
    (v := vl) (fun r => (v r).locallyBounded)
    (v' := vs) (fun j r => (v r).approximation.1 j)
    (fun r => (v r).approximation.2.1) (fun r => (v r).approximation.2.2)
    hK he χ hχ a
  have hcons (p : PshApproximation Ω) :
      (fun r => (Fin.cons (α := fun _ : Fin (k + 1) => PshApproximation Ω) p v r).limit) =
        Fin.cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) p.limit vl := by
    funext r
    cases r using Fin.cases with
    | zero => simp
    | succ r => simp [vl]
  have hμ (p : PshApproximation Ω) :
      mixedProductQuadraticMeasure (Fin.cons p v) a =
        quadraticMeasure (mixedProduct_positive (locallyBoundedPsh_cons p.locallyBounded
          (fun r => (v r).locallyBounded))) a :=
    quadraticMeasure_congr _ _ (mixedProduct_congr_tuple (hcons p) _ _) a
  rw [hμ (f i), hμ Q]
  exact hpair

set_option maxHeartbeats 750000 in
private theorem weightedMixedProductQuadratic_cutoff_lower
    (hsym : MixedProductSymmetric n (k + 1)) (p : PshApproximation Ω)
    (f : Fin (k + 1) → PshApproximation Ω) {b : ComplexModel n → ℝ}
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hp : p.hasCommonBoundary b K) (hf : ∀ i, (f i).hasCommonBoundary b K)
    (χ : 𝓓(Ω, ℝ)) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (a : CoordinateTuple n (k + 1) → ℂ) (j : ℕ) :
    weightedMixedProductQuadratic p f a χ ≤ weightedMixedProductQuadratic
      (PshApproximation.constant (p.approximation.1 j))
      (fun i => PshApproximation.constant ((f i).approximation.1 j)) a χ := by
  classical
  let P := PshApproximation.constant (p.approximation.1 j)
  let F (i : Fin (k + 1)) := PshApproximation.constant ((f i).approximation.1 j)
  let R (s : Finset (Fin (k + 1))) (i : Fin (k + 1)) := if i ∈ s then F i else f i
  have hR (s : Finset (Fin (k + 1))) (i : Fin (k + 1)) : (R s i).hasCommonBoundary b K := by
    by_cases hi : i ∈ s
    · simpa only [R, if_pos hi, F, PshApproximation.hasCommonBoundary, PshApproximation.constant] using
        (fun _ : ℕ => hf i j)
    · simpa only [R, if_neg hi] using hf i
  have hle (s : Finset (Fin (k + 1))) (i : Fin (k + 1)) :
      weightedMixedProductQuadratic P (R s) a χ ≤
        weightedMixedProductQuadratic P (Function.update (R s) i (F i)) a χ := by
    have hleft := weightedMixedProductQuadratic_swap hsym (p.approximation.1 j) (R s) i hK
      (fun m x hx => (hp j hx).trans (hR s i m hx).symm) χ hχ₁ a
    have hright := weightedMixedProductQuadratic_swap hsym (p.approximation.1 j)
      (Function.update (R s) i (F i)) i hK
      (fun m x hx => by
        simpa only [Function.update_self, F, PshApproximation.constant] using
          (hp j hx).trans (hf i j hx).symm) χ hχ₁ a
    rw [hleft, hright, Function.update_self, Function.update_idem]
    apply weightedMixedProductQuadratic_mono _ _ _ _ _ hχ₀
    intro x hx
    by_cases hi : i ∈ s
    · simp [R, hi]
    · simpa only [R, if_neg hi, F, PshApproximation.constant] using (f i).le_term j x hx
  have hAll (s : Finset (Fin (k + 1))) :
      weightedMixedProductQuadratic P f a χ ≤ weightedMixedProductQuadratic P (R s) a χ := by
    induction s using Finset.induction_on with
    | empty => simp [R]
    | insert i s _ ih =>
      refine ih.trans ((hle s i).trans_eq ?_)
      congr 2
      funext l
      by_cases h : l = i
      · subst l
        simp [R]
      · simp [R, h]
  exact (weightedMixedProductQuadratic_mono p P f a χ hχ₀ (p.le_term j)).trans
    (by simpa only [R, Finset.mem_univ, if_true] using hAll Finset.univ)

theorem weightedMixedProductQuadratic_eventually_lt_add (h : MixedProductMonotone n k)
    (p : PshApproximation Ω) (f : Fin k → PshApproximation Ω)
    (a : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, weightedMixedProductQuadratic (p.atTerm j) (fun i => (f i).atTerm j) a φ <
      weightedMixedProductQuadratic p f a φ + ε := by
  simpa only [weightedMixedProductQuadratic_apply, mixedProductQuadraticMeasure,
    PshApproximation.atTerm, PshApproximation.constant] using eventually_weightedQuadraticIntegral_lt_add
    (h Ω f) (fun j => mixedProduct_positive (u := fun i => (f i).term j)
      (fun i => (f i).term_locallyBounded j))
    (mixedProduct_positive (u := fun i => (f i).limit) (fun i => (f i).locallyBounded))
    p.locallyBounded p.approximation.1 p.approximation.2.1 p.approximation.2.2 a φ hφ hε

theorem tendsto_weightedMixedProductQuadratic_zero (p : PshApproximation Ω)
    (f : Fin 0 → PshApproximation Ω) (a : CoordinateTuple n 0 → ℂ) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => weightedMixedProductQuadratic (p.atTerm j) (fun i => (f i).atTerm j) a φ)
      atTop (𝓝 (weightedMixedProductQuadratic p f a φ)) := by
  let μ := mixedProductQuadraticMeasure f a
  let : μ.Regular := mixedProductQuadraticMeasure_regular f a
  have he (j : ℕ) : (fun i => (f i).atTerm j) = f := funext fun i => Fin.elim0 i
  have h := tendsto_integral_psh_weight_of_antitone p.locallyBounded p.term_locallyBounded
    p.approximation.2.1 p.approximation.2.2 μ φ
  rw [weightedMixedProductQuadratic_apply p f a φ]
  apply h.congr
  intro j
  rw [he j, weightedMixedProductQuadratic_apply]
  rfl

/-- Joint weighted weak convergence when all sequences coincide with
one potential off a compact subset of the domain. -/
theorem tendsto_weightedMixedProductQuadratic_of_commonBoundary
    (h : MixedProductMonotone n (k + 1)) (p : PshApproximation Ω)
    (f : Fin (k + 1) → PshApproximation Ω) {b : ComplexModel n → ℝ}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hp : p.hasCommonBoundary b K) (hf : ∀ i, (f i).hasCommonBoundary b K)
    (a : CoordinateTuple n (k + 1) → ℂ) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => weightedMixedProductQuadratic (p.atTerm j) (fun i => (f i).atTerm j) a φ)
      atTop (𝓝 (weightedMixedProductQuadratic p f a φ)) := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure
    (hK.union φ.hasCompactSupport) Ω.isOpen (union_subset hKΩ φ.tsupport_subset)
  obtain ⟨χ, hχ, hχW⟩ := exists_testFunction_one_on hWc hWΩ
  have hχ₁ (x : ComplexModel n) (hx : x ∈ K) : (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1 := by
    filter_upwards [hWo.mem_nhds (hKW (Or.inl hx))] with y hy
    exact hχW (subset_closure hy)
  have hχlim : Tendsto
      (fun j => weightedMixedProductQuadratic (p.atTerm j) (fun i => (f i).atTerm j) a χ)
      atTop (𝓝 (weightedMixedProductQuadratic p f a χ)) := by
    apply tendsto_order.2
    constructor
    · intro c hc
      exact Eventually.of_forall fun j => hc.trans_le
        (weightedMixedProductQuadratic_cutoff_lower h.symmetric p f hK hp hf χ
          (fun x => (hχ x).1) hχ₁ a j)
    · intro c hc
      simpa only [add_sub_cancel] using weightedMixedProductQuadratic_eventually_lt_add h p f a χ
        (fun x => (hχ x).1) (sub_pos.mpr hc)
  obtain ⟨C₀, hC₀⟩ := (φ.hasCompactSupport.image_of_continuousOn φ.continuous.abs.continuousOn).bddAbove
  let C := max 0 C₀
  have hC (x : ComplexModel n) : |φ x| ≤ (C • χ) x := by
    by_cases hx : x ∈ tsupport φ
    · rw [smul_apply, hχW (subset_closure (hKW (Or.inr hx))), Pi.one_apply, smul_eq_mul, mul_one]
      exact (hC₀ ⟨x, hx, rfl⟩).trans (le_max_right _ _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, abs_zero, smul_apply, smul_eq_mul]
      exact mul_nonneg (le_max_left _ _) (hχ x).1
  apply tendsto_of_upper_of_dominating_test
    (fun ψ hψ _ hε => weightedMixedProductQuadratic_eventually_lt_add h p f a ψ hψ hε)
    (C • χ) φ hC
  simpa only [map_smul, smul_eq_mul] using hχlim.const_mul C

end KEBall.BedfordTaylor
