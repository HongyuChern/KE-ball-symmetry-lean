import KEBall.BedfordTaylorSmoothCoefficients

/-!
# Boundary cancellation for the directional Levi pairing

When the two smooth potentials agree off a compact subset, a cutoff
identically one near that subset leaves the integrated pairing symmetric.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}

private theorem leviForm_congr_at {x v : ComplexModel n} (h : u =ᶠ[𝓝 x] p) :
    leviForm u x v = leviForm p x v := by
  simp only [leviForm, PshLines.realHessian_eq_fderiv, h.fderiv.fderiv_eq]

private theorem locallyIntegrableOn_leviForm_of_contDiffOn (hu : ContDiffOn ℝ ∞ u Ω)
    (v : ComplexModel n) : LocallyIntegrableOn (fun x => leviForm u x v) Ω volume := by
  have hD : ContinuousOn (iteratedFDeriv ℝ 2 u) Ω :=
    (hu.continuousOn_iteratedFDerivWithin (m := 2)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) Ω.isOpen.uniqueDiffOn).congr
      (fun x hx => (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) 2 Ω.isOpen hx).symm)
  have hR (a : ComplexModel n) : ContinuousOn (fun x => PshLines.realHessian u x a a) Ω :=
    (continuous_eval_const ![a, a]).comp_continuousOn hD
  have hL : ContinuousOn (fun x => leviForm u x v) Ω :=
    ((hR v).add (hR (Complex.I • v))).div_const 4
  exact (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2
    (fun _ hKΩ hK => (hL.mono hKΩ).integrableOn_compact hK)

/-- Integration by parts has no boundary contribution when the two
potentials have the same germ outside a compact set and the test is one
near that set. -/
theorem integral_mul_directionalLeviMeasure_swap
    (hu : IsSmoothPshOn Ω u) (hp : IsSmoothPshOn Ω p)
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (heq : EqOn u p ((Ω : Set (ComplexModel n)) \ K))
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x ∈ K, (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1)
    (v : ComplexModel n) :
    (∫ x : Ω, χ x * u x ∂directionalLeviMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hp) v) =
      ∫ x : Ω, χ x * p x ∂directionalLeviMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) v := by
  let U := multiplySmoothTest χ hu.1
  let P := multiplySmoothTest χ hp.1
  let A := ∫ x : Ω, U x ∂directionalLeviMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hp) v
  let B := ∫ x : Ω, P x ∂directionalLeviMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) v
  change A = B
  have hA₁ : A = ∫ x, p x * leviForm U x v := integral_directionalLeviMeasure _ v U
  have hB₁ : B = ∫ x, u x * leviForm P x v := integral_directionalLeviMeasure _ v P
  have hA₂ : A = ∫ x, U x * leviForm p x v :=
    integral_directionalLeviMeasure_of_isSmoothPshOn hp v U
  have hB₂ : B = ∫ x, P x * leviForm u x v :=
    integral_directionalLeviMeasure_of_isSmoothPshOn hu v P
  have hiA₁ := integrable_mul_leviForm_testFunction
    (PshLines.FirstPass.MongeAmpere.locallyIntegrableOn_of_plurisubharmonicOn_real hp.2.1) U v
  have hiB₁ := integrable_mul_leviForm_testFunction
    (PshLines.FirstPass.MongeAmpere.locallyIntegrableOn_of_plurisubharmonicOn_real hu.2.1) P v
  have hiA₂ : Integrable (fun x => U x * leviForm p x v) :=
    U.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrableOn_leviForm_of_contDiffOn hp.1 v)
  have hiB₂ : Integrable (fun x => P x * leviForm u x v) :=
    P.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrableOn_leviForm_of_contDiffOn hu.1 v)
  have hAB : A - B = B - A := by
    rw [hA₁, hB₁, ← integral_sub hiA₁ hiB₁, ← hB₁, ← hA₁, hB₂, hA₂, ← integral_sub hiB₂ hiA₂]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hxK : x ∈ K
    · have hU : (U : ComplexModel n → ℝ) =ᶠ[𝓝 x] u := by
        filter_upwards [hχ x hxK] with y hy
        change χ y * u y = u y
        rw [show χ y = 1 from hy, one_mul]
      have hP : (P : ComplexModel n → ℝ) =ᶠ[𝓝 x] p := by
        filter_upwards [hχ x hxK] with y hy
        change χ y * p y = p y
        rw [show χ y = 1 from hy, one_mul]
      rw [leviForm_congr_at hU, leviForm_congr_at hP, hU.eq_of_nhds, hP.eq_of_nhds]
    · by_cases hxΩ : x ∈ Ω
      · have he : u =ᶠ[𝓝 x] p := by
          filter_upwards [Ω.isOpen.mem_nhds hxΩ, hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy hyK
          exact heq ⟨hy, hyK⟩
        have hUP : (U : ComplexModel n → ℝ) =ᶠ[𝓝 x] P := by
          filter_upwards [he] with y hy
          simp only [U, P, multiplySmoothTest_apply, hy]
        rw [leviForm_congr_at he, leviForm_congr_at hUP, he.eq_of_nhds, hUP.eq_of_nhds]
        simp
      · have hU : x ∉ tsupport U := fun h => hxΩ (U.tsupport_subset h)
        have hP : x ∉ tsupport P := fun h => hxΩ (P.tsupport_subset h)
        simp [leviForm_eq_zero_of_notMem_tsupport hU, leviForm_eq_zero_of_notMem_tsupport hP,
          image_eq_zero_of_notMem_tsupport hU, image_eq_zero_of_notMem_tsupport hP]
  linarith

end KEBall.BedfordTaylor
