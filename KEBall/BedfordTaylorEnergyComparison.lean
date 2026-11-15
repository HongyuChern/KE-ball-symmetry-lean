import KEBall.BedfordTaylorBoundedPairing

/-!
# Monotonicity of the energy integrand under compact changes
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

private theorem diagonalMeasure_congr {S T : CoordinateDistributions Ω k k}
    (hS : IsPositiveMatrixDistribution S) (hT : IsPositiveMatrixDistribution T)
    (he : S = T) (I : CoordinateTuple n k) :
    diagonalMeasure hS I = diagonalMeasure hT I := by
  subst T
  rfl

private theorem integral_weightedDiagonalMeasure_update_mono
    {w : Fin (k + 1) → ComplexModel n → ℝ} (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i))
    (i : Fin (k + 1)) {p : ComplexModel n → ℝ} (hp : IsLocallyBoundedPshOn Ω p)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (he : EqOn (w i) p (Ω \ K)) (hle : ∀ x ∈ Ω, w i x ≤ p x)
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (hχnonneg : ∀ x ∈ Ω, 0 ≤ χ x) (I : CoordinateTuple n (k + 1)) :
    (∫ x : Ω, χ x * p x ∂diagonalMeasure (mixedProduct_positive hw) I) ≤
      ∫ x : Ω, χ x * p x ∂diagonalMeasure
        (mixedProduct_positive (locallyBoundedPsh_update (u := w) hw i hp)) I := by
  let σ := Equiv.swap (0 : Fin (k + 1)) i
  let t (j : Fin k) := w (σ j.succ)
  let ht (j : Fin k) := hw (σ j.succ)
  let hwp := locallyBoundedPsh_update (u := w) hw i hp
  have h₁ : Fin.cons (w i) t = w ∘ σ := by
    funext j
    cases j using Fin.cases with
    | zero => simp only [Fin.cons_zero, Function.comp_apply, σ, Equiv.swap_apply_left]
    | succ j => rfl
  have h₂ : Fin.cons p t = Function.update w i p ∘ σ := by
    funext j
    cases j using Fin.cases with
    | zero => simp only [Fin.cons_zero, Function.comp_apply, σ, Equiv.swap_apply_left,
        Function.update_self]
    | succ j =>
      have hne : σ j.succ ≠ i := fun h => Fin.succ_ne_zero j
        (σ.injective (h.trans (Equiv.swap_apply_left _ _).symm))
      simp only [Fin.cons_succ, t, Function.comp_apply, Function.update_of_ne hne]
  have h₁prod : mixedProduct (locallyBoundedPsh_cons (hw i) ht) = mixedProduct hw :=
    (mixedProduct_congr_tuple h₁ _ (fun j => hw (σ j))).trans
      (mixedProductSymmetric n (k + 1) Ω w hw σ)
  have h₂prod : mixedProduct (locallyBoundedPsh_cons hp ht) = mixedProduct hwp :=
    (mixedProduct_congr_tuple h₂ _ (fun j => hwp (σ j))).trans
      (mixedProductSymmetric n (k + 1) Ω (Function.update w i p) hwp σ)
  have hs := integral_diagonalMeasure_mixedProduct_swap_bounded (hw i) hp ht hK hKΩ he χ hχ I
  rw [diagonalMeasure_congr _ (mixedProduct_positive hwp) h₂prod I,
    diagonalMeasure_congr _ (mixedProduct_positive hw) h₁prod I] at hs
  let μ := diagonalMeasure (mixedProduct_positive hwp) I
  let : μ.Regular := diagonalMeasure_regular _ I
  rw [← hs]
  apply integral_mono (integrable_test_mul_psh (hw i) μ χ)
    (integrable_test_mul_psh hp μ χ)
  exact fun x => mul_le_mul_of_nonneg_left (hle x x.property) (hχnonneg x x.property)

/-- If the two ordered potentials agree off a compact set, integration
of the larger potential against the mixed top coefficient is increasing
as the first potential is replaced by the second in every factor. -/
theorem integral_weightedDiagonalMeasure_mono_of_eq_off_compact
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (he : EqOn u v (Ω \ K)) (hle : ∀ x ∈ Ω, u x ≤ v x)
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (hχnonneg : ∀ x ∈ Ω, 0 ≤ χ x) (I : CoordinateTuple n k) :
    (∫ x : Ω, χ x * v x ∂diagonalMeasure (mixedProduct_positive
      (u := fun _ : Fin k => u) (fun _ => hu)) I) ≤
      ∫ x : Ω, χ x * v x ∂diagonalMeasure (mixedProduct_positive
        (u := fun _ : Fin k => v) (fun _ => hv)) I := by
  cases k with
  | zero =>
    rw [diagonalMeasure_congr _ (mixedProduct_positive (u := fun _ : Fin 0 => v) (fun _ => hv))
      (mixedProduct_congr_tuple (funext fun i => Fin.elim0 i) (fun _ => hu) (fun _ => hv)) I]
  | succ k =>
    classical
    let f (s : Finset (Fin (k + 1))) (i : Fin (k + 1)) := if i ∈ s then v else u
    have hf (s : Finset (Fin (k + 1))) (i : Fin (k + 1)) : IsLocallyBoundedPshOn Ω (f s i) := by
      by_cases hi : i ∈ s <;> simp [f, hi, hu, hv]
    let G (s : Finset (Fin (k + 1))) :=
      ∫ x : Ω, χ x * v x ∂diagonalMeasure (mixedProduct_positive (hf s)) I
    have hinsert (s : Finset (Fin (k + 1))) (i : Fin (k + 1)) (hi : i ∉ s) :
        G s ≤ G (insert i s) := by
      have hfi : f s i = u := if_neg hi
      have hstep := integral_weightedDiagonalMeasure_update_mono (hf s) i hv hK hKΩ
        (by simpa only [hfi] using he) (by simpa only [hfi] using hle) χ hχ hχnonneg I
      have hfun : Function.update (f s) i v = f (insert i s) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [f]
        · simp [f, hj]
      rw [diagonalMeasure_congr _ (mixedProduct_positive (hf (insert i s)))
        (mixedProduct_congr_tuple hfun _ _) I] at hstep
      exact hstep
    have hmain (s : Finset (Fin (k + 1))) : G ∅ ≤ G s := by
      induction s using Finset.induction_on with
      | empty => rfl
      | insert i s hi ih => exact ih.trans (hinsert s i hi)
    have hzero : f ∅ = fun _ => u := by funext i; simp [f]
    have hall : f Finset.univ = fun _ => v := by funext i; simp [f]
    have h := hmain Finset.univ
    dsimp only [G] at h
    rw [diagonalMeasure_congr _ (mixedProduct_positive (fun _ => hu))
        (mixedProduct_congr_tuple hzero _ _) I,
      diagonalMeasure_congr _ (mixedProduct_positive (fun _ => hv))
        (mixedProduct_congr_tuple hall _ _) I] at h
    exact h

end KEBall.BedfordTaylor
