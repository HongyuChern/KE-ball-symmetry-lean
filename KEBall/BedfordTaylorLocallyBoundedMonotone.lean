import KEBall.BedfordTaylorMonotone
import KEBall.BedfordTaylorOrderedMollification

/-!
# Bedford–Taylor continuity for decreasing locally bounded potentials
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

private theorem exists_cofinal_indices (N : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, Monotone m ∧ (∀ j, N j ≤ m j) ∧ Tendsto m atTop atTop := by
  let m : ℕ → ℕ := Nat.rec (N 0) (fun j z => max (z + 1) (N (j + 1)))
  have hm (j : ℕ) : m (j + 1) = max (m j + 1) (N (j + 1)) := rfl
  have hm₁ (j : ℕ) : m j + 1 ≤ m (j + 1) := by rw [hm]; exact le_max_left _ _
  have hj (j : ℕ) : j ≤ m j := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih => exact (Nat.succ_le_succ ih).trans (hm₁ j)
  refine ⟨m, monotone_nat_of_le_succ fun j => (Nat.le_succ _).trans (hm₁ j), ?_,
    tendsto_atTop_mono hj tendsto_id⟩
  intro j
  cases j with
  | zero => exact le_rfl
  | succ j => rw [hm]; exact le_max_right _ _

set_option maxHeartbeats 750000 in
/-- Continuity along decreasing smooth approximations extends to
decreasing locally bounded sequences by ordered regularization. -/
theorem tendsto_of_orderedMollification {Y : Type*} [PseudoMetricSpace Y]
    {W : Opens (ComplexModel n)} (hrel : RelativelyCompactIn W Ω)
    (F : (v : Fin k → ComplexModel n → ℝ) → (∀ i, IsLocallyBoundedPshOn W (v i)) → Y)
    (hSmooth : ∀ A : Fin k → PshApproximation W,
      Tendsto (fun j => F (fun i => (A i).term j) (fun i => (A i).term_locallyBounded j)) atTop
        (𝓝 (F (fun i => (A i).limit) (fun i => (A i).locallyBounded))))
    {p : Fin k → ComplexModel n → ℝ} (hp : ∀ i, IsLocallyBoundedPshOn Ω (p i))
    {q : ℕ → Fin k → ComplexModel n → ℝ} (hq : ∀ j i, IsLocallyBoundedPshOn Ω (q j i))
    (hanti : ∀ i x, x ∈ Ω → Antitone (fun j => q j i x))
    (hlim : ∀ i x, x ∈ Ω → Tendsto (fun j => q j i x) atTop (𝓝 (p i x))) :
    Tendsto (fun j => F (q j) (fun i => IsLocallyBoundedPshOn.mono (hq j i)
      (subset_closure.trans hrel.2))) atTop
      (𝓝 (F p (fun i => IsLocallyBoundedPshOn.mono (hp i) (subset_closure.trans hrel.2)))) := by
  have hWΩ : W ≤ Ω := subset_closure.trans hrel.2
  obtain ⟨smooth, hsmooth, hmono⟩ := exists_order_preserving_smoothApproximation hrel
  let Q (j : ℕ) (i : Fin k) : PshApproximation W :=
    ⟨q j i, smooth (q j i), IsLocallyBoundedPshOn.mono (hq j i) hWΩ, hsmooth _ (hq j i)⟩
  let g (j m : ℕ) :=
    F (fun i => (Q j i).term m) (fun i => (Q j i).term_locallyBounded m)
  let a (j : ℕ) := F (q j) (fun i => IsLocallyBoundedPshOn.mono (hq j i) hWΩ)
  let L := F p (fun i => IsLocallyBoundedPshOn.mono (hp i) hWΩ)
  change Tendsto a atTop (𝓝 L)
  have hconv (j : ℕ) : Tendsto (g j) atTop (𝓝 (a j)) :=
    hSmooth (Q j)
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hr (j : ℕ) : ∃ N, ∀ m ≥ N, dist (g j m) (a j) < ε j :=
    eventually_atTop.mp (Metric.tendsto_nhds.mp (hconv j) (ε j) (hε j))
  choose N hN using hr
  obtain ⟨m, hm, hmN, hmTop⟩ := exists_cofinal_indices N
  have horder (i : Fin k) (x : ComplexModel n) (hx : x ∈ W) {l j : ℕ} (hlj : l ≤ j) (r : ℕ) :
      (Q j i).term r x ≤ (Q l i).term r x :=
    hmono _ _ (hq j i) (hq l i) (fun y hy => hanti i y hy hlj) r x hx
  let P (i : Fin k) : PshApproximation W :=
    ⟨p i, fun j => (Q j i).term (m j), IsLocallyBoundedPshOn.mono (hp i) hWΩ,
      fun j => (Q j i).approximation.1 (m j),
      fun x hx l j hlj => (horder i x hx hlj (m j)).trans
        ((Q l i).approximation.2.1 x hx (hm hlj)),
      by
        intro x hx
        apply tendsto_order.2
        constructor
        · intro c hc
          exact Eventually.of_forall fun j => hc.trans_le
            ((le_of_tendsto (hlim i x (hWΩ hx))
              ((eventually_ge_atTop j).mono fun l hl => hanti i x (hWΩ hx) hl)).trans
              ((Q j i).le_term (m j) x hx))
        · intro c hc
          obtain ⟨l, hl⟩ := ((hlim i x (hWΩ hx)).eventually_lt_const hc).exists
          have h := ((Q l i).approximation.2.2 x hx).comp hmTop
          filter_upwards [eventually_ge_atTop l, h.eventually_lt_const hl] with j hj hlt
          exact (horder i x hx hj (m j)).trans_lt hlt⟩
  have hP : Tendsto (fun j => g j (m j)) atTop (𝓝 L) :=
    hSmooth P
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [Metric.tendsto_nhds.mp hP (δ / 2) (half_pos hδ),
    hεlim.eventually_lt_const (half_pos hδ)] with j hj hjε
  calc
    dist (a j) L ≤ dist (a j) (g j (m j)) + dist (g j (m j)) L := dist_triangle _ _ _
    _ < δ := by
      have hrate := hN j (m j) (hmN j)
      rw [dist_comm] at hrate
      linarith

set_option maxHeartbeats 750000 in
/-- Decreasing locally bounded PSH sequences, including nonsmooth
sequences, converge in every mixed Bedford–Taylor coefficient. -/
theorem weakMatrixLimit_mixedProduct_of_decreasing
    {p : Fin k → ComplexModel n → ℝ} (hp : ∀ i, IsLocallyBoundedPshOn Ω (p i))
    {q : ℕ → Fin k → ComplexModel n → ℝ}
    (hq : ∀ j i, IsLocallyBoundedPshOn Ω (q j i))
    (hanti : ∀ i x, x ∈ Ω → Antitone (fun j => q j i x))
    (hlim : ∀ i x, x ∈ Ω → Tendsto (fun j => q j i x) atTop (𝓝 (p i x))) :
    WeakMatrixLimit (fun j => mixedProduct (u := q j) (hq j)) (mixedProduct hp) := by
  intro I J φ
  obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let W : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hrel : RelativelyCompactIn W Ω := ⟨hVc, hVΩ⟩
  have hWΩ : W ≤ Ω := subset_closure.trans hVΩ
  let ψ : 𝓓(W, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩
  have hψ : extendTest hWΩ ψ = φ := TestFunction.ext fun _ => rfl
  rw [← hψ]
  simp_rw [← restrictCoordinateMatrix_apply hWΩ, ← mixedProduct_restrict hWΩ]
  exact tendsto_of_orderedMollification hrel (fun v hv => mixedProduct (u := v) hv I J ψ)
    (fun A => mixedProductMonotone n k W A I J ψ) hp hq hanti hlim

theorem tendsto_topMeasure_of_decreasing {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {q : ℕ → ComplexModel n → ℝ}
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    (f : ComplexModel n → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfΩ : tsupport f ⊆ Ω) :
    Tendsto (fun j => ∫ x, f x ∂topMeasure (hq j)) atTop (𝓝 (∫ x, f x ∂topMeasure hu)) := by
  let μ (j : ℕ) := diagonalMeasure
    (mixedProduct_positive (k := n) (u := fun _ => q j) (fun _ => hq j)) id
  let ν := diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => hu)) id
  let : ∀ j, (μ j).Regular := fun j => diagonalMeasure_regular
    (mixedProduct_positive (k := n) (u := fun _ => q j) (fun _ => hq j)) id
  let : ν.Regular := diagonalMeasure_regular
    (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => hu)) id
  have htest (φ : 𝓓(Ω, ℝ)) :
      Tendsto (fun j => ∫ x : Ω, φ x ∂μ j) atTop (𝓝 (∫ x : Ω, φ x ∂ν)) := by
    simp only [μ, ν, integral_diagonalMeasure]
    exact (Complex.continuous_re.tendsto _).comp
      (weakMatrixLimit_mixedProduct_of_decreasing
        (p := fun _ : Fin n => u) (q := fun j _ => q j) (fun _ => hu) (fun j _ => hq j)
        (fun _ => hanti) (fun _ => hlim) id id φ)
  simp only [integral_topMeasure_map]
  exact tendsto_const_nhds.mul (tendsto_integral_of_tendsto_smooth_tests htest hf hfc hfΩ)

#print axioms weakMatrixLimit_mixedProduct_of_decreasing

end KEBall.BedfordTaylor
