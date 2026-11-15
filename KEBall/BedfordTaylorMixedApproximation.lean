import KEBall.BedfordTaylorMixedProduct

/-!
# Decreasing smooth approximations of mixed products
-/

set_option autoImplicit false

open Filter Set TopologicalSpace
open scoped ComplexOrder ContDiff Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsDecreasingApproximation IsLocallyBoundedPshOn IsSmoothPshOn RelativelyCompactIn)
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

/-- A locally bounded PSH potential and an actual decreasing smooth
PSH approximation on a specified open set. -/
structure PshApproximation (Ω : Opens (ComplexModel n)) where
  limit : ComplexModel n → ℝ
  term : ℕ → ComplexModel n → ℝ
  locallyBounded : IsLocallyBoundedPshOn Ω limit
  approximation : IsDecreasingApproximation Ω limit term

theorem PshApproximation.term_locallyBounded (p : PshApproximation Ω) (j : ℕ) :
    IsLocallyBoundedPshOn Ω (p.term j) :=
  isLocallyBoundedPshOn_of_isSmoothPshOn (p.approximation.1 j)

theorem PshApproximation.le_term (p : PshApproximation Ω) (j : ℕ) (x : ComplexModel n)
    (hx : x ∈ Ω) : p.limit x ≤ p.term j x :=
  le_of_tendsto (p.approximation.2.2 x hx)
    ((eventually_ge_atTop j).mono fun m hm => p.approximation.2.1 x hx hm)

def PshApproximation.constant {p : ComplexModel n → ℝ} (hp : IsSmoothPshOn Ω p) :
    PshApproximation Ω :=
  ⟨p, fun _ => p, isLocallyBoundedPshOn_of_isSmoothPshOn hp,
    fun _ => hp, fun _ _ _ _ _ => le_rfl, fun _ _ => tendsto_const_nhds⟩

def PshApproximation.atTerm (p : PshApproximation Ω) (j : ℕ) : PshApproximation Ω :=
  PshApproximation.constant (p.approximation.1 j)

def PshApproximation.restrict {V : Opens (ComplexModel n)} (p : PshApproximation Ω)
    (hVΩ : V ≤ Ω) : PshApproximation V where
  limit := p.limit
  term := p.term
  locallyBounded := IsLocallyBoundedPshOn.mono p.locallyBounded hVΩ
  approximation :=
    ⟨fun j => ⟨(p.approximation.1 j).1.mono hVΩ, (p.approximation.1 j).2.1.mono hVΩ,
        fun x hx => (p.approximation.1 j).2.2 x (hVΩ hx)⟩,
      fun x hx => p.approximation.2.1 x (hVΩ hx), fun x hx => p.approximation.2.2 x (hVΩ hx)⟩

/-- Agreement with a fixed potential on the outside of a compact
subset. The limit inherits this agreement. -/
def PshApproximation.hasCommonBoundary (p : PshApproximation Ω)
    (b : ComplexModel n → ℝ) (K : Set (ComplexModel n)) : Prop :=
  ∀ j, EqOn (p.term j) b ((Ω : Set (ComplexModel n)) \ K)

theorem PshApproximation.limit_eq_of_hasCommonBoundary (p : PshApproximation Ω)
    {b : ComplexModel n → ℝ} {K : Set (ComplexModel n)} (h : p.hasCommonBoundary b K) :
    EqOn p.limit b ((Ω : Set (ComplexModel n)) \ K) := by
  intro x hx
  exact tendsto_nhds_unique (p.approximation.2.2 x hx.1)
    (tendsto_const_nhds.congr fun j => (h j hx).symm)

/-- Joint convergence for the mixed product of a given degree. -/
def MixedProductMonotone (n k : ℕ) : Prop :=
  ∀ (Ω : Opens (ComplexModel n)) (p : Fin k → PshApproximation Ω),
    WeakMatrixLimit
      (fun j => mixedProduct (u := fun i => (p i).term j) (fun i => (p i).term_locallyBounded j))
      (mixedProduct (u := fun i => (p i).limit) (fun i => (p i).locallyBounded))

/-- Invariance of a mixed product under reordering of the factors. -/
def MixedProductSymmetric (n k : ℕ) : Prop :=
  ∀ (Ω : Opens (ComplexModel n)) (p : Fin k → ComplexModel n → ℝ)
    (hp : ∀ i, IsLocallyBoundedPshOn Ω (p i)) (σ : Equiv.Perm (Fin k)),
    mixedProduct (u := p ∘ σ) (fun i => hp (σ i)) = mixedProduct hp

theorem mixedProductMonotone_zero (n : ℕ) : MixedProductMonotone n 0 := by
  intro Ω p I J φ
  apply tendsto_const_nhds.congr
  intro j
  exact congrArg (fun T : CoordinateDistributions Ω 0 0 => T I J φ)
    (mixedProduct_congr_tuple (funext fun i => Fin.elim0 i) _ _)

theorem smoothMixedProduct_comp_perm
    {p : Fin k → ComplexModel n → ℝ} (hp : ∀ i, IsSmoothPshOn Ω (p i))
    (σ : Equiv.Perm (Fin k)) :
    mixedProduct (u := p ∘ σ) (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (hp (σ i))) =
      mixedProduct (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (hp i)) := by
  rw [mixedProduct_eq_smooth (u := p ∘ σ) (fun i => hp (σ i)), mixedProduct_eq_smooth hp]
  apply matrixOfDensities_congr
  intro I J x hx
  let A (i : Fin k) := Matrix.of fun r s => classicalComplexHessianEntry (p i)
    (PshLines.FirstPass.MongeAmpere.coordinateVector r) (PshLines.FirstPass.MongeAmpere.coordinateVector s) x
  have hA (i : Fin k) : (A i).PosSemidef :=
    posSemidef_classicalComplexHessianEntry (hp i) hx PshLines.FirstPass.MongeAmpere.coordinateVector
  rw [smoothMixedDensities_eq_mixedMinor, smoothMixedDensities_eq_mixedMinor]
  exact congrArg (fun M => M I J) (mixedMinorMatrix_comp_perm hA σ)

theorem MixedProductMonotone.symmetric (h : MixedProductMonotone n k) :
    MixedProductSymmetric n k := by
  intro Ω p hp σ
  ext I J φ
  obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let W : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hrel : RelativelyCompactIn W Ω := ⟨hVc, hVΩ⟩
  have hWΩ : W ≤ Ω := subset_closure.trans hVΩ
  let ψ : 𝓓(W, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩
  have hφ : extendTest hWΩ ψ = φ := TestFunction.ext fun _ => rfl
  rw [← hφ, ← restrictCoordinateMatrix_apply hWΩ, ← restrictCoordinateMatrix_apply hWΩ,
    ← mixedProduct_restrict hWΩ, ← mixedProduct_restrict hWΩ]
  choose q hq using fun i => exists_decreasingMollifierApproximation (hp i) hrel
  let a (i : Fin k) : PshApproximation W :=
    ⟨p i, q i, IsLocallyBoundedPshOn.mono (hp i) hWΩ, hq i⟩
  apply tendsto_nhds_unique (h W (a ∘ σ) I J ψ)
  exact (h W a I J ψ).congr fun j =>
    congrArg (fun T : CoordinateDistributions W k k => T I J ψ)
      (smoothMixedProduct_comp_perm (fun i => (a i).approximation.1 j) σ).symm

end KEBall.BedfordTaylor
