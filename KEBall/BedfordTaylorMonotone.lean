import KEBall.BedfordTaylorMatrixLocalLimit
import KEBall.BedfordTaylorTopMeasure
import KEBall.BedfordTaylorWeakConvergence

/-!
# The Bedford–Taylor monotone convergence theorem for smooth approximants
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {n k : ℕ} {Ω : Opens (ComplexModel n)}

private theorem weakMatrixLimit_weight_of_quadratic
    (p : PshApproximation Ω) (f : Fin k → PshApproximation Ω)
    (h : ∀ a (φ : 𝓓(Ω, ℝ)),
      Tendsto (fun j => weightedMixedProductQuadratic (p.atTerm j) (fun i => (f i).atTerm j) a φ)
        atTop (𝓝 (weightedMixedProductQuadratic p f a φ))) :
    WeakMatrixLimit
      (fun j => weightPositiveMatrixDistribution (p.term_locallyBounded j)
        (mixedProduct_positive (u := fun i => (f i).term j) (fun i => (f i).term_locallyBounded j)))
      (weightPositiveMatrixDistribution p.locallyBounded
        (mixedProduct_positive (u := fun i => (f i).limit) (fun i => (f i).locallyBounded))) := by
  intro I J φ
  simp only [weightPositiveMatrixDistribution_entry_apply]
  have hQ (a : CoordinateTuple n k → ℂ) :=
    h a φ
  simp only [weightedMixedProductQuadratic_apply, mixedProductQuadraticMeasure,
    PshApproximation.atTerm, PshApproximation.constant] at hQ
  exact (((Complex.continuous_ofReal.tendsto _).comp ((hQ _).sub (hQ _))).div_const 4).add
    ((tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
      ((hQ _).sub (hQ _)))).div_const 4)

private theorem mixedProductMonotone_succ (h : MixedProductMonotone n k) :
    MixedProductMonotone n (k + 1) := by
  intro Ω p
  have hweighted :
      ∀ a (φ : 𝓓(Ω, ℝ)), Tendsto
        (fun j => weightedMixedProductQuadratic ((p 0).atTerm j)
          (fun i => (p i.succ).atTerm j) a φ) atTop
        (𝓝 (weightedMixedProductQuadratic (p 0) (Fin.tail p) a φ)) := by
    intro a φ
    cases k with
    | zero => exact tendsto_weightedMixedProductQuadratic_zero (p 0) (Fin.tail p) a φ
    | succ k => exact tendsto_weightedMixedProductQuadratic h (p 0) (Fin.tail p) a φ
  have hW := (weakMatrixLimit_weight_of_quadratic (p 0) (Fin.tail p) hweighted).columnDerivative.rowDerivative
  have he (j : ℕ) :
      mixedProduct (u := fun i => (p i).term j) (fun i => (p i).term_locallyBounded j) =
        mixedProductStep ((p 0).term_locallyBounded j)
          (mixedProduct_positive (u := fun i => ((Fin.tail p) i).term j)
            (fun i => ((Fin.tail p) i).term_locallyBounded j)) :=
    mixedProduct_succ (u := fun i => (p i).term j) (fun i => (p i).term_locallyBounded j)
  have heLim :
      mixedProduct (u := fun i => (p i).limit) (fun i => (p i).locallyBounded) =
        mixedProductStep (p 0).locallyBounded
          (mixedProduct_positive (u := fun i => ((Fin.tail p) i).limit)
            (fun i => ((Fin.tail p) i).locallyBounded)) :=
    mixedProduct_succ (u := fun i => (p i).limit) (fun i => (p i).locallyBounded)
  intro I J φ
  simp_rw [he, heLim]
  exact hW I J φ

/-- Every decreasing smooth PSH approximation of a locally bounded
tuple converges in the corresponding mixed Bedford–Taylor product. -/
theorem mixedProductMonotone (n k : ℕ) : MixedProductMonotone n k := by
  induction k with
  | zero => exact mixedProductMonotone_zero n
  | succ k ih => exact mixedProductMonotone_succ ih

theorem mixedProductSymmetric (n k : ℕ) : MixedProductSymmetric n k :=
  (mixedProductMonotone n k).symmetric

/-- The top measure satisfies the local Bedford–Taylor relation in
every complex dimension. -/
theorem isLocalBedfordTaylorMeasure_top {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) : IsLocalBedfordTaylorMeasure Ω u (topMeasure hu) := by
  refine ⟨hu, topMeasure_compl hu, fun _ => topMeasure_finite_on_compact hu, ?_⟩
  intro V hV
  refine ⟨exists_decreasingMollifierApproximation hu hV, ?_⟩
  intro p hp f hf hfc hfV
  have hVΩ : V ≤ Ω := subset_closure.trans hV.2
  let huV := IsLocallyBoundedPshOn.mono hu hVΩ
  let A : PshApproximation V := ⟨u, p, huV, hp⟩
  let μ (j : ℕ) := diagonalMeasure
    (mixedProduct_positive (k := n) (u := fun _ => p j) (fun _ => A.term_locallyBounded j)) id
  let ν := diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => huV)) id
  let : ∀ j, (μ j).Regular := fun j => diagonalMeasure_regular
    (mixedProduct_positive (k := n) (u := fun _ => p j) (fun _ => A.term_locallyBounded j)) id
  let : ν.Regular := diagonalMeasure_regular
    (mixedProduct_positive (k := n) (u := fun _ => u) (fun _ => huV)) id
  have htest (φ : 𝓓(V, ℝ)) :
      Tendsto (fun j => ∫ x : V, φ x ∂μ j) atTop (𝓝 (∫ x : V, φ x ∂ν)) := by
    simp only [μ, ν, integral_diagonalMeasure]
    exact (Complex.continuous_re.tendsto _).comp (mixedProductMonotone n n V (fun _ => A) id id φ)
  have hweak := tendsto_integral_of_tendsto_smooth_tests htest hf hfc hfV
  have hres : (∫ x, f x ∂topMeasure hu) = ∫ x, f x ∂topMeasure huV := by
    rw [← topMeasure_restrict hu hVΩ, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun _ hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hfV ht)))]
  change Tendsto (fun j => ∫ x, f x ∂smoothMeasure V (p j) (hp.1 j)) atTop
    (𝓝 (∫ x, f x ∂topMeasure hu))
  rw [hres, integral_topMeasure_map huV f]
  simp_rw [← topMeasure_eq_smoothMeasure, integral_topMeasure_map]
  exact tendsto_const_nhds.mul hweak

#print axioms mixedProductMonotone
#print axioms isLocalBedfordTaylorMeasure_top

end KEBall.BedfordTaylor
