import KEBall.BedfordTaylorCommonRegularization
import KEBall.BedfordTaylorMatrixBoundaryPairing

/-!
# Integration by parts with a compact difference of bounded potentials
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

theorem integral_weightedDiagonalMeasure_restrict {W : Opens (ComplexModel n)} (hWΩ : W ≤ Ω)
    {u : ComplexModel n → ℝ} {v : Fin k → ComplexModel n → ℝ}
    (hv : ∀ i, IsLocallyBoundedPshOn Ω (v i))
    (I : CoordinateTuple n k) (φ : 𝓓(W, ℝ)) :
    (∫ x : W, φ x * u x ∂diagonalMeasure (mixedProduct_positive
        (fun i => IsLocallyBoundedPshOn.mono (hv i) hWΩ)) I) =
      ∫ x : Ω, extendTest hWΩ φ x * u x ∂diagonalMeasure (mixedProduct_positive hv) I := by
  simp only [diagonalMeasure_eq_quadraticMeasure]
  rw [quadraticMeasure_congr _
    (restrictCoordinateMatrix_isPositive hWΩ (mixedProduct_positive hv))
    (mixedProduct_restrict hWΩ hv) _]
  exact integral_weightedQuadraticMeasure_restrict hWΩ (mixedProduct_positive hv) _ φ

theorem tendsto_weightedDiagonalMeasure_mixedProduct_of_decreasing
    {u : ComplexModel n → ℝ} {v : Fin k → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : ∀ i, IsLocallyBoundedPshOn Ω (v i))
    {p : ℕ → ComplexModel n → ℝ} {q : ℕ → Fin k → ComplexModel n → ℝ}
    (hp : ∀ j, IsLocallyBoundedPshOn Ω (p j))
    (hq : ∀ j i, IsLocallyBoundedPshOn Ω (q j i))
    (hpAnti : ∀ x ∈ Ω, Antitone (fun j => p j x))
    (hqAnti : ∀ i x, x ∈ Ω → Antitone (fun j => q j i x))
    (hpLim : ∀ x ∈ Ω, Tendsto (fun j => p j x) atTop (𝓝 (u x)))
    (hqLim : ∀ i x, x ∈ Ω → Tendsto (fun j => q j i x) atTop (𝓝 (v i x)))
    (I : CoordinateTuple n k) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => ∫ x : Ω, φ x * p j x ∂diagonalMeasure (mixedProduct_positive (hq j)) I)
      atTop (𝓝 (∫ x : Ω, φ x * u x ∂diagonalMeasure (mixedProduct_positive hv) I)) := by
  let A : Fin (k + 1) → ComplexModel n → ℝ := Fin.cons u v
  let B (j : ℕ) : Fin (k + 1) → ComplexModel n → ℝ := Fin.cons (p j) (q j)
  have hA : ∀ i, IsLocallyBoundedPshOn Ω (A i) := locallyBoundedPsh_cons hu hv
  have hB (j : ℕ) : ∀ i, IsLocallyBoundedPshOn Ω (B j i) := locallyBoundedPsh_cons (hp j) (hq j)
  have hanti (i : Fin (k + 1)) (x : ComplexModel n) (hx : x ∈ Ω) :
      Antitone (fun j => B j i x) := by
    cases i using Fin.cases with
    | zero => exact hpAnti x hx
    | succ i => exact hqAnti i x hx
  have hlim (i : Fin (k + 1)) (x : ComplexModel n) (hx : x ∈ Ω) :
      Tendsto (fun j => B j i x) atTop (𝓝 (A i x)) := by
    cases i using Fin.cases with
    | zero => exact hpLim x hx
    | succ i => exact hqLim i x hx
  let a : CoordinateTuple n k → ℂ := Pi.single I 1
  have h := tendsto_weightedQuadraticMeasure_mixedProduct_of_decreasing hA hB hanti hlim a φ
  have hAeq : Fin.tail A = v := Fin.tail_cons _ _
  have hBeq (j : ℕ) : Fin.tail (B j) = q j := Fin.tail_cons _ _
  have hM (j : ℕ) := quadraticMeasure_congr
    (mixedProduct_positive (u := Fin.tail (B j)) (fun i => hB j i.succ))
    (mixedProduct_positive (hq j))
    (mixedProduct_congr_tuple (hBeq j) (fun i => hB j i.succ) (hq j)) a
  have hLim := quadraticMeasure_congr
    (mixedProduct_positive (u := Fin.tail A) (fun i => hA i.succ))
    (mixedProduct_positive hv)
    (mixedProduct_congr_tuple hAeq (fun i => hA i.succ) hv) a
  simp_rw [hM, hLim] at h
  simpa only [diagonalMeasure_eq_quadraticMeasure, a, A, B, Fin.cons_zero] using h

private theorem integral_diagonalMeasure_mixedProduct_swap_smooth
    {u p : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u) (hp : IsSmoothPshOn Ω p)
    {v : Fin k → ComplexModel n → ℝ} (hv : ∀ i, IsSmoothPshOn Ω (v i))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (he : EqOn u p (Ω \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (I : CoordinateTuple n (k + 1)) :
    (∫ x : Ω, χ x * u x ∂diagonalMeasure (mixedProduct_positive
      (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hp)
        (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (hv i)))) I) =
      ∫ x : Ω, χ x * p x ∂diagonalMeasure (mixedProduct_positive
      (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn hu)
        (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (hv i)))) I := by
  change (∫ x : Ω, multiplySmoothTest χ hu.1 x ∂_) =
    ∫ x : Ω, multiplySmoothTest χ hp.1 x ∂_
  rw [integral_diagonalMeasure, integral_diagonalMeasure]
  exact congrArg Complex.re (smoothMixedProduct_swap_test hu hp hv hK he χ hχ I I)

/-- A compact difference allows the PSH weight and the first
Bedford–Taylor factor to be exchanged in the integral. -/
theorem integral_diagonalMeasure_mixedProduct_swap_bounded
    {u p : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p)
    {v : Fin k → ComplexModel n → ℝ} (hv : ∀ i, IsLocallyBoundedPshOn Ω (v i))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (he : EqOn u p (Ω \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (I : CoordinateTuple n (k + 1)) :
    (∫ x : Ω, χ x * u x ∂diagonalMeasure (mixedProduct_positive (locallyBoundedPsh_cons hp hv)) I) =
      ∫ x : Ω, χ x * p x ∂diagonalMeasure (mixedProduct_positive (locallyBoundedPsh_cons hu hv)) I := by
  let U := (Ω : Set (ComplexModel n)) ∩ interior {x | χ x = 1}
  have hU : IsOpen U := Ω.isOpen.inter isOpen_interior
  have hKU : K ⊆ U := fun x hx => ⟨hKΩ hx, mem_interior_iff_mem_nhds.mpr (hχ x hx)⟩
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hVΩ : closure V ⊆ Ω := hVU.trans inter_subset_left
  obtain ⟨D, hDo, hKD, hDΩ, hDc⟩ := exists_open_between_and_isCompact_closure
    (χ.hasCompactSupport.union hVc) Ω.isOpen (union_subset χ.tsupport_subset hVΩ)
  let W : Opens (ComplexModel n) := ⟨D, hDo⟩
  have hrel : RelativelyCompactIn W Ω := ⟨hDc, hDΩ⟩
  have hWΩ : W ≤ Ω := subset_closure.trans hDΩ
  let ψ : 𝓓(W, ℝ) := ⟨χ, χ.contDiff, χ.hasCompactSupport, subset_union_left.trans hKD⟩
  have hψ (x : ComplexModel n) (hx : x ∈ closure V) : (ψ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1 :=
    mem_interior_iff_mem_nhds.mp (hVU hx).2
  obtain ⟨f, g, hf, hg, hfg⟩ := exists_common_decreasingRegularization hu hp hrel hK
    (L' := closure V) (hKV.trans (interior_maximal subset_closure hV)) he
  choose q hq using fun i => PshLines.Regularization.HolomorphicPullback.exists_decreasingMollifierApproximation
    (hv i) hrel
  let uW := IsLocallyBoundedPshOn.mono hu hWΩ
  let pW := IsLocallyBoundedPshOn.mono hp hWΩ
  let vW := fun i => IsLocallyBoundedPshOn.mono (hv i) hWΩ
  let qL := fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hq i).1 j)
  have limit (a b : ComplexModel n → ℝ)
      (ha : IsLocallyBoundedPshOn W a) (hb : IsLocallyBoundedPshOn W b)
      (a' b' : ℕ → ComplexModel n → ℝ)
      (ha' : IsDecreasingApproximation W a a') (hb' : IsDecreasingApproximation W b b') :
      Tendsto (fun j => ∫ x : W, ψ x * a' j x ∂diagonalMeasure (mixedProduct_positive
          (locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn (hb'.1 j)) (qL j))) I)
        atTop (𝓝 (∫ x : W, ψ x * a x ∂diagonalMeasure (mixedProduct_positive
          (locallyBoundedPsh_cons hb vW)) I)) := by
    apply tendsto_weightedDiagonalMeasure_mixedProduct_of_decreasing ha (locallyBoundedPsh_cons hb vW)
      (fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (ha'.1 j))
      (fun j => locallyBoundedPsh_cons (isLocallyBoundedPshOn_of_isSmoothPshOn (hb'.1 j)) (qL j))
      ha'.2.1 ?_ ha'.2.2 ?_ I ψ
    · intro i x hx
      cases i using Fin.cases with
      | zero => exact hb'.2.1 x hx
      | succ i => exact (hq i).2.1 x hx
    · intro i x hx
      cases i using Fin.cases with
      | zero => exact hb'.2.2 x hx
      | succ i => exact (hq i).2.2 x hx
  have hs (j : ℕ) := integral_diagonalMeasure_mixedProduct_swap_smooth (hf.1 j) (hg.1 j)
    (fun i => (hq i).1 j) hVc (hfg j) ψ hψ I
  have hEq := tendsto_nhds_unique (limit u p uW pW f g hf hg)
    ((limit p u pW uW g f hg hf).congr fun j => (hs j).symm)
  exact (integral_weightedDiagonalMeasure_restrict hWΩ (locallyBoundedPsh_cons hp hv) I ψ).symm.trans
    (hEq.trans (integral_weightedDiagonalMeasure_restrict hWΩ (locallyBoundedPsh_cons hu hv) I ψ))

end KEBall.BedfordTaylor
