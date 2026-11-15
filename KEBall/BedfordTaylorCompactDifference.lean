import KEBall.BedfordTaylorMonotone

/-!
# Total mass under compactly supported changes of a potential
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn coordinateVector)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

private theorem weightedCoefficient_eq_on_test
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    {T : CoordinateDistributions Ω k k} (hT : IsPositiveMatrixDistribution T)
    (I J : CoordinateTuple n k) (ψ : 𝓓(Ω, ℝ))
    (hψ : ∀ x ∈ Ω, ψ x * u x = ψ x * p x) :
    weightPositiveMatrixDistribution hu hT I J ψ = weightPositiveMatrixDistribution hp hT I J ψ := by
  have h (a : CoordinateTuple n k → ℂ) :
      (∫ x : Ω, ψ x * u x ∂quadraticMeasure hT a) = ∫ x : Ω, ψ x * p x ∂quadraticMeasure hT a :=
    integral_congr_ae (Eventually.of_forall fun x => hψ x x.property)
  simp only [weightPositiveMatrixDistribution_entry_apply, h]

private theorem mixedProductStep_eq_on_cutoff
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    {T : CoordinateDistributions Ω k k} (hT : IsPositiveMatrixDistribution T)
    {K : Set (ComplexModel n)} (heq : EqOn u p ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (I J : CoordinateTuple n (k + 1)) :
    mixedProductStep hu hT I J χ = mixedProductStep hp hT I J χ := by
  let S := weightPositiveMatrixDistribution hu hT
  let R := weightPositiveMatrixDistribution hp hT
  have hpair (P Q : CoordinateTuple n k) (a b : ComplexModel n) :
      S P Q (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ b χ)) =
      R P Q (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ b χ)) := by
    apply weightedCoefficient_eq_on_test hu hp hT
    intro x hx
    by_cases hxK : x ∈ K
    · rw [testFunction_lineDerivCLM_lineDerivCLM_apply, realHessian_eq_fderiv,
        (hχ x hxK).fderiv.fderiv_eq]
      simp
    · rw [heq ⟨hx, hxK⟩]
  let eval : 𝓓'(Ω, ℂ) →+ ℂ :=
    { toFun := fun D => D χ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change eval (coordinateRowDerivative (coordinateColumnDerivative S) I J) =
    eval (coordinateRowDerivative (coordinateColumnDerivative R) I J)
  simp only [coordinateRowDerivative, coordinateColumnDerivative, Matrix.of_apply,
    alternatingDerivative, map_sum, map_zsmul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  let a := coordinateVector (I i)
  let b := coordinateVector (J j)
  let F (D : 𝓓'(Ω, ℂ)) := wirtingerDerivative a (Complex.I • a)
    (wirtingerDerivative b (-(Complex.I • b)) D)
  have hF : F (S (i.removeNth I) (j.removeNth J)) χ =
      F (R (i.removeNth I) (j.removeNth J)) χ := by
    simp only [F, wirtingerDerivative, directionalDerivative, Distribution.lineDerivCLM_apply,
      smul_apply, sub_apply, hpair]
  exact congrArg (fun t : ℂ => (-1 : ℤ) ^ (i : ℕ) • ((-1 : ℤ) ^ (j : ℕ) • t)) hF

private theorem mixedProduct_update_eq_on_cutoff
    {u : Fin (k + 1) → ComplexModel n → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i))
    (i : Fin (k + 1)) {p : ComplexModel n → ℝ} (hp : IsLocallyBoundedPshOn Ω p)
    {K : Set (ComplexModel n)} (he : EqOn (u i) p ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (I J : CoordinateTuple n (k + 1)) :
    mixedProduct hu I J χ =
      mixedProduct (u := Function.update u i p) (locallyBoundedPsh_update (u := u) hu i hp) I J χ := by
  let σ := Equiv.swap (0 : Fin (k + 1)) i
  let U := u ∘ σ
  let P := (Function.update u i p) ∘ σ
  let hU : ∀ r, IsLocallyBoundedPshOn Ω (U r) := fun r => hu (σ r)
  let hP : ∀ r, IsLocallyBoundedPshOn Ω (P r) :=
    fun r => locallyBoundedPsh_update (u := u) hu i hp (σ r)
  have htail : Fin.tail U = Fin.tail P := by
    funext r
    change u (σ r.succ) = Function.update u i p (σ r.succ)
    have hn : σ r.succ ≠ i := fun h =>
      Fin.succ_ne_zero r (σ.injective (h.trans (Equiv.swap_apply_left _ _).symm))
    rw [Function.update_of_ne hn]
  have h0 : EqOn (U 0) (P 0) ((Ω : Set (ComplexModel n)) \ K) := by
    simpa only [U, P, Function.comp_apply, σ, Equiv.swap_apply_left, Function.update_self] using he
  have hUsym : mixedProduct hU = mixedProduct hu := mixedProductSymmetric n (k + 1) Ω u hu σ
  have hPsym : mixedProduct hP =
      mixedProduct (u := Function.update u i p) (locallyBoundedPsh_update (u := u) hu i hp) :=
    mixedProductSymmetric n (k + 1) Ω (Function.update u i p) (locallyBoundedPsh_update (u := u) hu i hp) σ
  rw [← hUsym, ← hPsym, mixedProduct_succ hU, mixedProduct_succ hP]
  let hTU := mixedProduct_positive (u := Fin.tail U) (fun r => hU r.succ)
  let hTP := mixedProduct_positive (u := Fin.tail P) (fun r => hP r.succ)
  have hTUeq := mixedProduct_congr_tuple htail (fun r => hU r.succ) (fun r => hP r.succ)
  have hStep := mixedProductStep_eq_of_coefficient_eq (hP 0) hTU hTP hTUeq
  rw [← hStep]
  exact mixedProductStep_eq_on_cutoff (hU 0) (hP 0) hTU h0 χ hχ I J

private theorem mixedProduct_eq_on_cutoff_of_eq_off_compact
    {u p : Fin k → ComplexModel n → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i))
    (hp : ∀ i, IsLocallyBoundedPshOn Ω (p i))
    {K : Set (ComplexModel n)} (he : ∀ i, EqOn (u i) (p i) ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (I J : CoordinateTuple n k) :
    mixedProduct hu I J χ = mixedProduct hp I J χ := by
  cases k with
  | zero =>
    exact congrArg (fun T : CoordinateDistributions Ω 0 0 => T I J χ)
      (mixedProduct_congr_tuple (funext fun i => Fin.elim0 i) hu hp)
  | succ k =>
    classical
    let f (s : Finset (Fin (k + 1))) (i : Fin (k + 1)) := if i ∈ s then p i else u i
    have hf (s : Finset (Fin (k + 1))) (i : Fin (k + 1)) : IsLocallyBoundedPshOn Ω (f s i) := by
      by_cases hi : i ∈ s <;> simp [f, hi, hu, hp]
    have hAll (s : Finset (Fin (k + 1))) :
        mixedProduct hu I J χ = mixedProduct (u := f s) (hf s) I J χ := by
      induction s using Finset.induction_on with
      | empty =>
        exact congrArg (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J χ)
          (mixedProduct_congr_tuple (by funext i; simp [f]) hu (hf ∅))
      | insert i s hi ih =>
        have heq : EqOn (f s i) (p i) ((Ω : Set (ComplexModel n)) \ K) := by
          simpa only [f, if_neg hi] using he i
        have hstep := mixedProduct_update_eq_on_cutoff (u := f s) (hf s) i (hp i) heq χ hχ I J
        have hfun : Function.update (f s) i (p i) = f (insert i s) := by
          funext l
          by_cases hl : l = i
          · subst l
            simp [f]
          · simp [f, hl]
        exact ih.trans (hstep.trans (congrArg
          (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J χ)
          (mixedProduct_congr_tuple hfun (locallyBoundedPsh_update (u := f s) (hf s) i (hp i))
            (hf (insert i s)))))
    exact (hAll Finset.univ).trans (congrArg
      (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J χ)
      (mixedProduct_congr_tuple (by funext i; simp [f]) (hf Finset.univ) hp))

theorem integral_topMeasure_eq_on_cutoff_of_eq_off_compact
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    {K : Set (ComplexModel n)} (he : EqOn u p ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1) :
    (∫ x, χ x ∂topMeasure hu) = ∫ x, χ x ∂topMeasure hp := by
  rw [integral_topMeasure, integral_topMeasure,
    mixedProduct_eq_on_cutoff_of_eq_off_compact (u := fun _ => u) (p := fun _ => p)
      (fun _ => hu) (fun _ => hp) (fun _ => he) χ hχ]

theorem integrable_test_topMeasure {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (χ : 𝓓(Ω, ℝ)) :
    Integrable (fun x => χ x) (topMeasure hu) := by
  let K := tsupport χ
  have hK : IsCompact K := χ.hasCompactSupport
  have hKΩ : K ⊆ Ω := χ.tsupport_subset
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn χ.continuous.norm.continuousOn).bddAbove
  have hInt : IntegrableOn (fun x => χ x) K (topMeasure hu) :=
    Measure.integrableOn_of_bounded (topMeasure_finite_on_compact hu hK hKΩ).ne
      χ.continuous.aestronglyMeasurable (by
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        exact hC ⟨x, hx, rfl⟩)
  have hi := hInt.integrable_indicator hK.measurableSet
  rw [indicator_eq_self.mpr (subset_tsupport χ)] at hi
  exact hi

theorem topMeasure_restrict_compl_eq_of_eq_off_compact
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (he : EqOn u p ((Ω : Set (ComplexModel n)) \ K)) :
    (topMeasure hu).restrict Kᶜ = (topMeasure hp).restrict Kᶜ := by
  let W : Opens (ComplexModel n) := ⟨Ω \ K, Ω.isOpen.sdiff hK.isClosed⟩
  have hW : W ≤ Ω := diff_subset
  have hWmeasure : (topMeasure hu).restrict (W : Set (ComplexModel n)) =
      (topMeasure hp).restrict (W : Set (ComplexModel n)) := by
    rw [topMeasure_restrict hu hW, topMeasure_restrict hp hW, topMeasure_congr _ _ he]
  have hcut {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v) :
      (topMeasure hv).restrict Kᶜ = (topMeasure hv).restrict (W : Set (ComplexModel n)) := by
    have ha : ∀ᵐ x ∂topMeasure hv, x ∈ Ω := by
      rw [ae_iff]
      exact topMeasure_compl hv
    have hres := Measure.restrict_eq_self_of_ae_mem ha
    calc
      _ = ((topMeasure hv).restrict (Ω : Set (ComplexModel n))).restrict Kᶜ := by rw [hres]
      _ = _ := by
        rw [Measure.restrict_restrict hK.measurableSet.compl]
        congr 1
        exact inter_comm _ _
  rw [hcut hu, hcut hp, hWmeasure]

/-- A compactly supported change of a locally bounded PSH potential
preserves the total Monge–Ampère mass. -/
theorem topMeasure_total_eq_of_eq_off_compact
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (he : EqOn u p ((Ω : Set (ComplexModel n)) \ K)) :
    topMeasure hu univ = topMeasure hp univ := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨χ, _, hχ⟩ := exists_testFunction_one_on hWc hWΩ
  have hχ₁ (x : ComplexModel n) (hx : x ∈ K) : (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1 := by
    filter_upwards [hWo.mem_nhds (hKW hx)] with y hy
    exact hχ (subset_closure hy)
  have hi := integral_topMeasure_eq_on_cutoff_of_eq_off_compact hu hp he χ hχ₁
  have hcompl := topMeasure_restrict_compl_eq_of_eq_off_compact hu hp hK he
  have hreal : (∫ x in K, χ x ∂topMeasure hu) = ∫ x in K, χ x ∂topMeasure hp := by
    have hsplit₁ := integral_add_compl hK.measurableSet (integrable_test_topMeasure hu χ)
    have hsplit₂ := integral_add_compl hK.measurableSet (integrable_test_topMeasure hp χ)
    rw [hcompl] at hsplit₁
    linarith
  have hχK : EqOn χ (fun _ => (1 : ℝ)) K := fun x hx => hχ (subset_closure (hKW hx))
  rw [setIntegral_congr_fun hK.measurableSet hχK, setIntegral_congr_fun hK.measurableSet hχK] at hreal
  have hmass : topMeasure hu K = topMeasure hp K := by
    apply (ENNReal.toReal_eq_toReal_iff' (topMeasure_finite_on_compact hu hK hKΩ).ne
      (topMeasure_finite_on_compact hp hK hKΩ).ne).mp
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply_univ] using hreal
  have hmassC := congrArg (fun μ : Measure (ComplexModel n) => μ univ) hcompl
  rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ] at hmassC
  rw [← measure_add_measure_compl (μ := topMeasure hu) hK.measurableSet,
    ← measure_add_measure_compl (μ := topMeasure hp) hK.measurableSet, hmass, hmassC]

end KEBall.BedfordTaylor
