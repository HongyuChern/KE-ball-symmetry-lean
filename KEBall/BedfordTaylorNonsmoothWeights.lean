import KEBall.BedfordTaylorLocallyBoundedMonotone

/-!
# Joint weighted convergence for nonsmooth bounded sequences
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

private noncomputable def weightedProductIntegral
    (p : Fin (k + 1) → ComplexModel n → ℝ) (hp : ∀ i, IsLocallyBoundedPshOn Ω (p i))
    (a : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) : ℝ :=
  ∫ x : Ω, φ x * p 0 x ∂quadraticMeasure (mixedProduct_positive
    (u := Fin.tail p) (fun i => hp i.succ)) a

private theorem weightedProductIntegral_restrict {W : Opens (ComplexModel n)} (hWΩ : W ≤ Ω)
    (p : Fin (k + 1) → ComplexModel n → ℝ) (hp : ∀ i, IsLocallyBoundedPshOn Ω (p i))
    (a : CoordinateTuple n k → ℂ) (ψ : 𝓓(W, ℝ)) :
    weightedProductIntegral p (fun i => IsLocallyBoundedPshOn.mono (hp i) hWΩ) a ψ =
      weightedProductIntegral p hp a (extendTest hWΩ ψ) := by
  let hT := mixedProduct_positive (u := Fin.tail p) (fun i => hp i.succ)
  have hμ : quadraticMeasure (mixedProduct_positive (u := Fin.tail p)
      (fun i => IsLocallyBoundedPshOn.mono (hp i.succ) hWΩ)) a =
      quadraticMeasure (restrictCoordinateMatrix_isPositive hWΩ hT) a :=
    quadraticMeasure_congr _ _ (mixedProduct_restrict (u := Fin.tail p) hWΩ
      (fun i => hp i.succ)) a
  unfold weightedProductIntegral
  rw [hμ]
  exact integral_weightedQuadraticMeasure_restrict (u := p 0) hWΩ hT a ψ

private theorem tendsto_weightedProductIntegral_smooth (p : Fin (k + 1) → PshApproximation Ω)
    (a : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => weightedProductIntegral (fun i => (p i).term j)
      (fun i => (p i).term_locallyBounded j) a φ) atTop
      (𝓝 (weightedProductIntegral (fun i => (p i).limit) (fun i => (p i).locallyBounded) a φ)) := by
  have h : Tendsto (fun j => weightedMixedProductQuadratic ((p 0).atTerm j)
      (fun i => (p i.succ).atTerm j) a φ) atTop
      (𝓝 (weightedMixedProductQuadratic (p 0) (Fin.tail p) a φ)) := by
    cases k with
    | zero => exact tendsto_weightedMixedProductQuadratic_zero (p 0) (Fin.tail p) a φ
    | succ k =>
      exact tendsto_weightedMixedProductQuadratic (mixedProductMonotone n (k + 1)) (p 0) (Fin.tail p) a φ
  simp only [weightedMixedProductQuadratic_apply, mixedProductQuadraticMeasure,
    PshApproximation.atTerm, PshApproximation.constant] at h
  exact h

/-- Joint convergence of a locally bounded PSH weight and arbitrary
mixed-product factors on each smooth compactly supported test. -/
theorem tendsto_weightedQuadraticMeasure_mixedProduct_of_decreasing
    {p : Fin (k + 1) → ComplexModel n → ℝ} (hp : ∀ i, IsLocallyBoundedPshOn Ω (p i))
    {q : ℕ → Fin (k + 1) → ComplexModel n → ℝ} (hq : ∀ j i, IsLocallyBoundedPshOn Ω (q j i))
    (hanti : ∀ i x, x ∈ Ω → Antitone (fun j => q j i x))
    (hlim : ∀ i x, x ∈ Ω → Tendsto (fun j => q j i x) atTop (𝓝 (p i x)))
    (a : CoordinateTuple n k → ℂ) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => ∫ x : Ω, φ x * q j 0 x ∂quadraticMeasure (mixedProduct_positive
      (u := Fin.tail (q j)) (fun i => hq j i.succ)) a) atTop
      (𝓝 (∫ x : Ω, φ x * p 0 x ∂quadraticMeasure (mixedProduct_positive
        (u := Fin.tail p) (fun i => hp i.succ)) a)) := by
  change Tendsto (fun j => weightedProductIntegral (q j) (hq j) a φ) atTop
    (𝓝 (weightedProductIntegral p hp a φ))
  obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let W : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hrel : RelativelyCompactIn W Ω := ⟨hVc, hVΩ⟩
  have hWΩ : W ≤ Ω := subset_closure.trans hVΩ
  let ψ : 𝓓(W, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩
  have hψ : extendTest hWΩ ψ = φ := TestFunction.ext fun _ => rfl
  rw [← hψ]
  simp_rw [← weightedProductIntegral_restrict hWΩ]
  exact tendsto_of_orderedMollification hrel (fun v hv => weightedProductIntegral v hv a ψ)
    (fun A => tendsto_weightedProductIntegral_smooth A a ψ) hp hq hanti hlim

theorem tendsto_weightedTopMeasure_of_decreasing
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    {q p : ℕ → ComplexModel n → ℝ}
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j)) (hp : ∀ j, IsLocallyBoundedPshOn Ω (p j))
    (hqu : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hpu : ∀ x ∈ Ω, Antitone (fun j => p j x))
    (hqlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p j x) atTop (𝓝 (v x)))
    (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => ∫ x, φ x * q j x ∂topMeasure (hp j)) atTop
      (𝓝 (∫ x, φ x * u x ∂topMeasure hv)) := by
  let A : Fin (n + 1) → ComplexModel n → ℝ := Fin.cons u (fun _ => v)
  let B (j : ℕ) : Fin (n + 1) → ComplexModel n → ℝ := Fin.cons (q j) (fun _ => p j)
  have hA : ∀ i, IsLocallyBoundedPshOn Ω (A i) :=
    locallyBoundedPsh_cons hu (u := fun _ : Fin n => v) (fun _ => hv)
  have hB (j : ℕ) : ∀ i, IsLocallyBoundedPshOn Ω (B j i) :=
    locallyBoundedPsh_cons (hq j) (u := fun _ : Fin n => p j) (fun _ => hp j)
  have hanti (i : Fin (n + 1)) (x : ComplexModel n) (hx : x ∈ Ω) :
      Antitone (fun j => B j i x) := by
    cases i using Fin.cases with
    | zero => exact hqu x hx
    | succ i => exact hpu x hx
  have hlim (i : Fin (n + 1)) (x : ComplexModel n) (hx : x ∈ Ω) :
      Tendsto (fun j => B j i x) atTop (𝓝 (A i x)) := by
    cases i using Fin.cases with
    | zero => exact hqlim x hx
    | succ i => exact hplim x hx
  let a : CoordinateTuple n n → ℂ := Pi.single id 1
  have h := tendsto_weightedQuadraticMeasure_mixedProduct_of_decreasing hA hB hanti hlim a φ
  have hAeq : Fin.tail A = fun _ => v := by
    funext i
    simp [A, Fin.tail]
  have hBeq (j : ℕ) : Fin.tail (B j) = fun _ => p j := by
    funext i
    simp [B, Fin.tail]
  have hM (j : ℕ) := quadraticMeasure_congr
    (mixedProduct_positive (u := Fin.tail (B j)) (fun i => hB j i.succ))
    (mixedProduct_positive (u := fun _ : Fin n => p j) (fun _ => hp j))
    (mixedProduct_congr_tuple (hBeq j) (fun i => hB j i.succ) (fun _ => hp j)) a
  have hLim := quadraticMeasure_congr
    (mixedProduct_positive (u := Fin.tail A) (fun i => hA i.succ))
    (mixedProduct_positive (u := fun _ : Fin n => v) (fun _ => hv))
    (mixedProduct_congr_tuple hAeq (fun i => hA i.succ) (fun _ => hv)) a
  simp_rw [hM, hLim] at h
  simp only [integral_topMeasure_map, diagonalMeasure_eq_quadraticMeasure]
  exact tendsto_const_nhds.mul h

#print axioms tendsto_weightedQuadraticMeasure_mixedProduct_of_decreasing

end KEBall.BedfordTaylor
