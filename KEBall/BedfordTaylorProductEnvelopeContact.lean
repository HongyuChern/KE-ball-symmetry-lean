import KEBall.BedfordTaylorProductEnvelopeHessian
import KEBall.BedfordTaylorEnvelopeContactPoint
import KEBall.BedfordTaylorDensityLimit
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Compactness.Lindelof

/-!
# The contact-set support theorem on a product ball
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsLocallyBoundedPshOn smoothDensity complexHessian_isHermitian)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

set_option maxHeartbeats 900000 in
/-- The Bedford–Taylor measure of the greatest PSH minorant of a smooth
nonpositive ball potential extended by zero to a product ball is carried by
the contact set. -/
theorem topMeasure_productEnvelope_off_contact_eq_zero {n m : ℕ} (hn : 0 < n + m) {R : ℝ}
    {u v : ComplexModel (n + m) → ℝ} (hu : ContDiff ℝ 2 u)
    (hu₀ : ∀ x ∈ ball 0 R, u x ≤ 0) (huBoundary : ∀ x ∈ sphere 0 R, u x = 0)
    (hv : IsLocallyBoundedPshOn (complexProductBall n m) v)
    (hvf : ∀ x ∈ complexProductBall n m, v x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x)
    (hgreatest : ∀ w : ComplexModel (n + m) → ℝ, IsLocallyBoundedPshOn (complexProductBall n m) w →
      (∀ x ∈ complexProductBall n m, w x ≤ (ball (0 : ComplexModel (n + m)) R).indicator u x) →
        ∀ x ∈ complexProductBall n m, w x ≤ v x) :
    topMeasure hv {x ∈ complexProductBall n m | v x < (ball (0 : ComplexModel (n + m)) R).indicator u x} = 0 := by
  let X := ComplexModel (n + m)
  let P := complexProductBall n m
  let f := (ball (0 : X) R).indicator u
  let S : Set X := {x ∈ P | v x < f x}
  let μ := topMeasure hv
  have hf : Continuous f :=
    hu.continuous.indicator (fun x hx => huBoundary x (frontier_ball_subset_sphere hx))
  have hvCont : ContinuousOn v P := by
    intro x hx
    obtain ⟨W, hxW, _, hdiff, _⟩ :=
      exists_lipschitz_fderiv_productEnvelope hu hu₀ huBoundary hv hvf hgreatest hx
    exact ((hdiff x hxW).differentiableAt (W.isOpen.mem_nhds hxW)).continuousAt.continuousWithinAt
  have hS : IsOpen S := isOpen_iff_mem_nhds.mpr (by
    intro x hx
    have hmem : ∀ᶠ y in 𝓝 x, y ∈ P := P.isOpen.mem_nhds hx.1
    have hvx := (hvCont x hx.1).continuousAt (P.isOpen.mem_nhds hx.1)
    have hlt := hvx.tendsto.eventually_lt hf.continuousAt.tendsto hx.2
    filter_upwards [hmem, hlt] with y hy hy'
    exact ⟨hy, hy'⟩)
  have hlocal (a : X) (ha : a ∈ P) : ∃ W : Opens X, a ∈ W ∧ μ (S ∩ W) = 0 := by
    obtain ⟨W, haW, hrel, q, hq, ⟨C, _, hess⟩, hAE⟩ :=
      exists_ae_hessianApproximation_productEnvelope hu hu₀ huBoundary hv hvf hgreatest ha
    have hW : W ≤ P := subset_closure.trans hrel.2
    let ν := volume.restrict (W : Set X)
    let Q (x : X) := potentialTaylorModel v x
    let d (x : X) := smoothDensity (Q x) x
    have hcont : Continuous (fun M : Matrix (Fin (n + m)) (Fin (n + m)) ℂ =>
        ((n + m).factorial : ℝ) / Real.pi ^ (n + m) * M.det.re) :=
      continuous_const.mul (Complex.continuous_re.comp continuous_id.matrix_det)
    have hlim : ∀ᵐ x ∂ν, Tendsto (fun j => smoothDensity (q j) x) atTop (𝓝 (d x)) := by
      filter_upwards [hAE] with x hx
      exact (hcont.tendsto _).comp hx.1
    obtain ⟨D, _, hD⟩ := exists_smoothDensity_bound_of_boundedHessian (n := n + m) C
    have hDensity := topMeasure_eq_withDensity_of_smoothDensity_limit
      (IsLocallyBoundedPshOn.mono hv hW) hq (fun j x hx => hD _ _ (hess j x hx)) hlim
    refine ⟨W, haW, ?_⟩
    change topMeasure hv (S ∩ (W : Set X)) = 0
    rw [← Measure.restrict_apply' W.isOpen.measurableSet, topMeasure_restrict hv hW, hDensity,
      withDensity_apply _ hS.measurableSet]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_of_ae (s := S) hAE, ae_restrict_mem (μ := ν) hS.measurableSet,
      ae_restrict_of_ae (s := S) (ae_restrict_mem W.isOpen.measurableSet)] with x hx hxS hxW
    have hQ : ContDiff ℝ ∞ (Q x) := contDiff_quadraticTaylorModel _ _ _ _
    have hQ₂ : ContDiffAt ℝ 2 (Q x) x := hQ.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hpsd : (modelHessian (Q x) x).PosSemidef := posSemidef_of_tendsto_of_isHermitian
      (complexHessian_isHermitian hQ₂) hx.1 (fun j => (hq.1 j).2.2 x hxW)
    have hQc (y : X) : modelHessian (Q x) y = modelHessian (Q x) x := by
      simp only [Q, potentialTaylorModel, complexHessian_quadraticTaylorModel]
    have hQx : Q x x = v x := by
      simp [Q, potentialTaylorModel, quadraticTaylorModel]
    have hdet := det_eq_zero_of_quadratic_expansion_off_contact hn hv hvf hgreatest hxS.1
      hf.continuousAt hxS.2 hQ hQx hQc hpsd hx.2
    change ENNReal.ofReal (smoothDensity (Q x) x) = 0
    simp [smoothDensity, hdet]
  choose W hW hNull using (fun a : (P : Set X) => hlocal a a.2)
  have hCover : S ⊆ ⋃ a : (P : Set X), (W a : Set X) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx.1⟩, hW ⟨x, hx.1⟩⟩
  obtain ⟨I, hI, hICover⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    (fun a : (P : Set X) => (W a : Set X)) (fun a => (W a).isOpen) hCover
  have hSub : S ⊆ ⋃ a ∈ I, S ∩ (W a : Set X) := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hICover hx)
    obtain ⟨haI, hax⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨haI, hx, hax⟩⟩
  change μ S = 0
  exact nonpos_iff_eq_zero.mp ((measure_mono hSub).trans_eq
    ((measure_biUnion_null_iff hI).mpr (fun a _ => hNull a)))

end KEBall.BedfordTaylor
