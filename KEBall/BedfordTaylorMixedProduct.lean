import KEBall.BedfordTaylorMatrixRestriction
import KEBall.BedfordTaylorSeparateMatrixLimit

/-!
# The positive Bedford–Taylor mixed product

Positivity is proved by regularizing one factor at a time. Passing to
the limit in the first factor uses its integrals against fixed
coefficient measures. Passing to the limit in a later factor uses
the smoothness of the preceding factors.
-/

set_option autoImplicit false

open Filter Set TopologicalSpace
open scoped ComplexOrder Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn RelativelyCompactIn)
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {n k : ℕ}

/-- Replace a single potential by a locally bounded PSH potential. -/
theorem locallyBoundedPsh_update {Ω : Opens (ComplexModel n)}
    {u : Fin k → ComplexModel n → ℝ} (hu : ∀ r, IsLocallyBoundedPshOn Ω (u r))
    (r : Fin k) {p : ComplexModel n → ℝ} (hp : IsLocallyBoundedPshOn Ω p) :
    ∀ i, IsLocallyBoundedPshOn Ω (Function.update u r p i) := by
  intro i
  by_cases hi : i = r
  · simpa [hi] using hp
  · simpa [Function.update_of_ne hi] using hu i

private theorem mixedProductStep_congr {Ω : Opens (ComplexModel n)}
    {u u' : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hu' : IsLocallyBoundedPshOn Ω u') (heq : u = u')
    {T T' : CoordinateDistributions Ω k k}
    (hT : IsPositiveMatrixDistribution T) (hT' : IsPositiveMatrixDistribution T')
    (hEq : T = T') :
    mixedProductStep hu hT = mixedProductStep hu' hT' := by
  subst u' T'
  rfl

theorem mixedProductStep_eq_of_coefficient_eq {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    {T T' : CoordinateDistributions Ω k k}
    (hT : IsPositiveMatrixDistribution T) (hT' : IsPositiveMatrixDistribution T')
    (heq : T = T') :
    mixedProductStep hu hT = mixedProductStep hu hT' :=
  mixedProductStep_congr hu hu rfl hT hT' heq

private theorem mixedProductStep_restrict {U V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn U u)
    {T : CoordinateDistributions U k k} (hT : IsPositiveMatrixDistribution T) :
    mixedProductStep (IsLocallyBoundedPshOn.mono hu hVU)
        (restrictCoordinateMatrix_isPositive hVU hT) =
      (restrictCoordinateMatrix (mixedProductStep hu hT) : CoordinateDistributions V (k + 1) (k + 1)) := by
  unfold mixedProductStep
  rw [weightPositiveMatrixDistribution_restrict hVU hu, coordinateColumnDerivative_restrict hVU,
    coordinateRowDerivative_restrict hVU]

private structure MixedProductConstruction (n k : ℕ) where
  coeff (Ω : Opens (ComplexModel n)) (u : Fin k → ComplexModel n → ℝ)
    (hu : ∀ r, IsLocallyBoundedPshOn Ω (u r)) : CoordinateDistributions Ω k k
  positive {Ω u} (hu : ∀ r, IsLocallyBoundedPshOn Ω (u r)) :
    IsPositiveMatrixDistribution (coeff Ω u hu)
  restriction {U V u} (hVU : V ≤ U) (hu : ∀ r, IsLocallyBoundedPshOn U (u r)) :
    coeff V u (fun r => IsLocallyBoundedPshOn.mono (hu r) hVU) =
      restrictCoordinateMatrix (coeff U u hu)
  smooth {Ω u} (hu : ∀ r, IsSmoothPshOn Ω (u r)) :
    coeff Ω u (fun r => isLocallyBoundedPshOn_of_isSmoothPshOn (hu r)) =
      matrixOfDensities (smoothMixedDensities n k u) (contDiffOn_smoothMixedDensities u fun r => (hu r).1)
  separateLimit {Ω u} (hu : ∀ r, IsLocallyBoundedPshOn Ω (u r)) (r : Fin k)
    (hpre : ∀ i : Fin k, i < r → IsSmoothPshOn Ω (u i))
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsLocallyBoundedPshOn Ω (p j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => p j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => p j x) atTop (𝓝 (u r x))) :
    WeakMatrixLimit (fun j => coeff Ω (Function.update u r (p j))
      (locallyBoundedPsh_update (u := u) hu r (hp j))) (coeff Ω u hu)

private theorem MixedProductConstruction.coeff_congr (data : MixedProductConstruction n k)
    {Ω : Opens (ComplexModel n)} {u w : Fin k → ComplexModel n → ℝ} (heq : u = w)
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i)) :
    data.coeff Ω u hu = data.coeff Ω w hw := by
  subst w
  rfl

private noncomputable def MixedProductConstruction.zero (n : ℕ) : MixedProductConstruction n 0 where
  coeff Ω u _ :=
    matrixOfDensities (smoothMixedDensities n 0 u) (contDiffOn_smoothMixedDensities u (fun r => Fin.elim0 r))
  positive := fun {Ω u} _ => smoothMixedDensities_isPositive u (fun r => Fin.elim0 r)
  restriction := by
    intro U V u hVU hu
    ext I J φ
    simp only [restrictCoordinateMatrix_apply hVU, matrixOfDensities, Matrix.of_apply,
      complexRegularDistribution_apply, extendTest_apply]
  smooth := fun _ => rfl
  separateLimit := fun _ r => Fin.elim0 r

private noncomputable def MixedProductConstruction.nextMatrix (data : MixedProductConstruction n k)
    (Ω : Opens (ComplexModel n)) (u : Fin (k + 1) → ComplexModel n → ℝ)
    (hu : ∀ r, IsLocallyBoundedPshOn Ω (u r)) : CoordinateDistributions Ω (k + 1) (k + 1) :=
  mixedProductStep (hu 0) (data.positive (u := Fin.tail u) (fun r => hu r.succ))

private theorem MixedProductConstruction.nextMatrix_restriction (data : MixedProductConstruction n k)
    {U V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {u : Fin (k + 1) → ComplexModel n → ℝ} (hu : ∀ r, IsLocallyBoundedPshOn U (u r)) :
    data.nextMatrix V u (fun r => IsLocallyBoundedPshOn.mono (hu r) hVU) =
      restrictCoordinateMatrix (data.nextMatrix U u hu) := by
  unfold MixedProductConstruction.nextMatrix
  rw [← mixedProductStep_restrict hVU]
  exact mixedProductStep_congr _ _ rfl _ _ (data.restriction hVU (fun r => hu r.succ))

private theorem MixedProductConstruction.nextMatrix_smooth (data : MixedProductConstruction n k)
    {Ω : Opens (ComplexModel n)} {u : Fin (k + 1) → ComplexModel n → ℝ}
    (hu : ∀ r, IsSmoothPshOn Ω (u r)) :
    data.nextMatrix Ω u (fun r => isLocallyBoundedPshOn_of_isSmoothPshOn (hu r)) =
      matrixOfDensities (smoothMixedDensities n (k + 1) u)
        (contDiffOn_smoothMixedDensities u fun r => (hu r).1) := by
  have hc := smoothMixedDensities_closed (Fin.tail u) (fun r => hu r.succ)
  rw [← mixedProductStep_eq_smooth u hu hc.1 hc.2]
  exact mixedProductStep_congr _ _ rfl _ _ (data.smooth (u := Fin.tail u) (fun r => hu r.succ))

private theorem MixedProductConstruction.nextMatrix_separateLimit (data : MixedProductConstruction n k)
    {Ω : Opens (ComplexModel n)} {u : Fin (k + 1) → ComplexModel n → ℝ}
    (hu : ∀ r, IsLocallyBoundedPshOn Ω (u r)) (r : Fin (k + 1))
    (hpre : ∀ i : Fin (k + 1), i < r → IsSmoothPshOn Ω (u i))
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsLocallyBoundedPshOn Ω (p j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => p j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => p j x) atTop (𝓝 (u r x))) :
    WeakMatrixLimit (fun j => data.nextMatrix Ω (Function.update u r (p j))
      (locallyBoundedPsh_update (u := u) hu r (hp j))) (data.nextMatrix Ω u hu) := by
  cases r using Fin.cases with
  | zero =>
    have h := (weakMatrixLimit_weight (hu 0) hp hanti hlim
      (data.positive (u := Fin.tail u) (fun i => hu i.succ))).columnDerivative.rowDerivative
    intro I J φ
    apply (h I J φ).congr
    intro j
    unfold MixedProductConstruction.nextMatrix
    exact congrArg (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J φ)
      (mixedProductStep_congr (hp j) _ (by simp) _ _
        (data.coeff_congr (by simp) _ _))
  | succ r =>
    have h₀ : IsSmoothPshOn Ω (u 0) := hpre 0 (Fin.succ_pos r)
    have hpreTail (i : Fin k) (hi : i < r) : IsSmoothPshOn Ω (Fin.tail u i) :=
      hpre i.succ (Fin.succ_lt_succ_iff.mpr hi)
    have ht := data.separateLimit (u := Fin.tail u) (fun i => hu i.succ) r hpreTail hp hanti hlim
    have h := (ht.weightSmooth h₀ (fun j => data.positive (locallyBoundedPsh_update (u := Fin.tail u)
      (fun i => hu i.succ) r (hp j))) (data.positive (u := Fin.tail u)
        (fun i => hu i.succ))).columnDerivative.rowDerivative
    intro I J φ
    apply (h I J φ).congr
    intro j
    unfold MixedProductConstruction.nextMatrix
    exact congrArg (fun T : CoordinateDistributions Ω (k + 1) (k + 1) => T I J φ)
      (mixedProductStep_congr (isLocallyBoundedPshOn_of_isSmoothPshOn h₀) _
        (Function.update_of_ne (Fin.succ_ne_zero r).symm _ _).symm _ _
        (data.coeff_congr (by simp) _ _))

private theorem MixedProductConstruction.nextMatrix_positive (data : MixedProductConstruction n k)
    {Ω : Opens (ComplexModel n)} {u : Fin (k + 1) → ComplexModel n → ℝ}
    (hu : ∀ r, IsLocallyBoundedPshOn Ω (u r)) :
    IsPositiveMatrixDistribution (data.nextMatrix Ω u hu) := by
  have hlocal (φ : 𝓓(Ω, ℝ)) :
      ∃ W : Opens (ComplexModel n), ∃ hWΩ : W ≤ Ω, RelativelyCompactIn W Ω ∧
        ∃ ψ : 𝓓(W, ℝ), extendTest hWΩ ψ = φ := by
    obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
    exact ⟨⟨V, hVo⟩, subset_closure.trans hVΩ, ⟨hVc, hVΩ⟩,
      ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩, TestFunction.ext fun _ => rfl⟩
  have htest (φ : 𝓓(Ω, ℝ)) :
      (Matrix.of fun I J => data.nextMatrix Ω u hu I J φ).IsHermitian ∧
      ((∀ x, 0 ≤ φ x) → (Matrix.of fun I J => data.nextMatrix Ω u hu I J φ).PosSemidef) := by
    obtain ⟨W, hWΩ, hrel, ψ, hφ⟩ := hlocal φ
    rw [← hφ]
    simp_rw [← restrictCoordinateMatrix_apply hWΩ, ← data.nextMatrix_restriction hWΩ hu]
    let P (m : ℕ) : Prop :=
      ∀ w : Fin (k + 1) → ComplexModel n → ℝ, ∀ hw : ∀ i, IsLocallyBoundedPshOn W (w i),
        (∀ i : Fin (k + 1), (i : ℕ) < m → IsSmoothPshOn W (w i)) →
          (∀ i : Fin (k + 1), m ≤ (i : ℕ) → w i = u i) →
          (Matrix.of fun I J => data.nextMatrix W w hw I J ψ).IsHermitian ∧
          ((∀ x, 0 ≤ ψ x) → (Matrix.of fun I J => data.nextMatrix W w hw I J ψ).PosSemidef)
    have hPTop : P (k + 1) := by
      intro w hw hs _
      let hwS := fun i : Fin (k + 1) => hs i i.isLt
      have he := data.nextMatrix_smooth hwS
      have hpos := smoothMixedDensities_isPositive w hwS
      rw [← he] at hpos
      exact ⟨hpos.1 ψ, hpos.2 ψ⟩
    have hP : P 0 := Nat.decreasingInduction' (fun m hm _ ih => by
      intro w hw hpre hpost
      let r : Fin (k + 1) := ⟨m, hm⟩
      have hru : w r = u r := hpost r le_rfl
      obtain ⟨p, hp⟩ := exists_decreasingMollifierApproximation (hu r) hrel
      let hpL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp.1 j)
      have hlim := data.nextMatrix_separateLimit hw r (fun i hi => hpre i hi)
        hpL hp.2.1 (fun x hx => by rw [hru]; exact hp.2.2 x hx)
      have happ (j : ℕ) := ih (Function.update w r (p j))
        (locallyBoundedPsh_update (u := w) hw r (hpL j)) (by
          intro i hi
          by_cases he : i = r
          · simpa [he] using hp.1 j
          · rw [Function.update_of_ne he]
            exact hpre i (by
              have hne : (i : ℕ) ≠ m := fun h => he (Fin.ext h)
              omega)) (by
          intro i hi
          have hne : i ≠ r := fun he => by
            have h := congrArg Fin.val he
            dsimp [r] at h
            omega
          rw [Function.update_of_ne hne]
          exact hpost i (by omega))
      exact ⟨hlim.hermitian ψ (fun j => (happ j).1), fun hψ =>
        hlim.posSemidef ψ (fun j => (happ j).2 hψ)⟩) (Nat.zero_le _) hPTop
    exact hP u (fun i => IsLocallyBoundedPshOn.mono (hu i) hWΩ) (fun _ h => by omega)
      (fun _ _ => rfl)
  exact ⟨fun φ => (htest φ).1, fun φ => (htest φ).2⟩

private noncomputable def MixedProductConstruction.succ (data : MixedProductConstruction n k) :
    MixedProductConstruction n (k + 1) where
  coeff := data.nextMatrix
  positive := data.nextMatrix_positive
  restriction := fun {_U _V u} hVU hu => data.nextMatrix_restriction (u := u) hVU hu
  smooth := data.nextMatrix_smooth
  separateLimit := data.nextMatrix_separateLimit

private noncomputable def mixedProductConstruction (n : ℕ) : (k : ℕ) → MixedProductConstruction n k
  | 0 => MixedProductConstruction.zero n
  | k + 1 => (mixedProductConstruction n k).succ

variable {Ω : Opens (ComplexModel n)} {u : Fin k → ComplexModel n → ℝ}

/-- The coefficient distributions of the Bedford–Taylor mixed product. -/
noncomputable def mixedProduct (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    CoordinateDistributions Ω k k :=
  (mixedProductConstruction n k).coeff Ω u hu

theorem mixedProduct_positive (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    IsPositiveMatrixDistribution (mixedProduct hu) :=
  (mixedProductConstruction n k).positive hu

theorem mixedProduct_succ {u : Fin (k + 1) → ComplexModel n → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    mixedProduct hu = mixedProductStep (hu 0)
      (mixedProduct_positive (u := Fin.tail u) fun i => hu i.succ) := rfl

theorem mixedProduct_restrict {V : Opens (ComplexModel n)} (hVΩ : V ≤ Ω)
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    mixedProduct (fun i => IsLocallyBoundedPshOn.mono (hu i) hVΩ) =
      restrictCoordinateMatrix (mixedProduct hu) :=
  (mixedProductConstruction n k).restriction hVΩ hu

theorem mixedProduct_eq_smooth (hu : ∀ i, IsSmoothPshOn Ω (u i)) :
    mixedProduct (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (hu i)) =
      matrixOfDensities (smoothMixedDensities n k u) (contDiffOn_smoothMixedDensities u fun r => (hu r).1) :=
  (mixedProductConstruction n k).smooth hu

theorem locallyBoundedPsh_cons {p : ComplexModel n → ℝ} (hp : IsLocallyBoundedPshOn Ω p)
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    ∀ r, IsLocallyBoundedPshOn Ω
      (Fin.cons (α := fun _ : Fin (k + 1) => ComplexModel n → ℝ) p u r) := by
  intro r
  induction r using Fin.cases with
  | zero => exact hp
  | succ r => exact hu r

theorem mixedProduct_congr_tuple {w : Fin k → ComplexModel n → ℝ} (heq : u = w)
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i)) :
    mixedProduct hu = mixedProduct hw :=
  (mixedProductConstruction n k).coeff_congr heq hu hw

theorem mixedProduct_congr {w : Fin k → ComplexModel n → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i))
    (heq : ∀ i, EqOn (u i) (w i) Ω) :
    mixedProduct hu = mixedProduct hw := by
  induction k with
  | zero => exact mixedProduct_congr_tuple (funext fun i => Fin.elim0 i) hu hw
  | succ k ih =>
    rw [mixedProduct_succ hu, mixedProduct_succ hw]
    unfold mixedProductStep
    rw [weightPositiveMatrixDistribution_congr (hu 0) (hw 0) (heq 0) _ _
      (ih (u := Fin.tail u) (w := Fin.tail w) (fun i => hu i.succ) (fun i => hw i.succ)
        (fun i => heq i.succ))]

theorem weakMatrixLimit_mixedProduct_update (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) (r : Fin k)
    (hpre : ∀ i : Fin k, i < r → IsSmoothPshOn Ω (u i))
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsLocallyBoundedPshOn Ω (p j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => p j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => p j x) atTop (𝓝 (u r x))) :
    WeakMatrixLimit (fun j => mixedProduct (u := Function.update u r (p j))
      (locallyBoundedPsh_update (u := u) hu r (hp j))) (mixedProduct hu) :=
  (mixedProductConstruction n k).separateLimit hu r hpre hp hanti hlim

#print axioms mixedProduct_positive
#print axioms mixedProduct_eq_smooth

end KEBall.BedfordTaylor
