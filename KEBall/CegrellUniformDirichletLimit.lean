import KEBall.BedfordTaylorUniformLimit
import KEBall.CegrellClass

/-!
# The bounded zero-boundary class under uniform Dirichlet limits
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
  {q : ℕ → ComplexModel n → ℝ}

/-- A uniform limit with a continuous zero boundary trace belongs to E₀
when its limiting test measure has finite mass. -/
theorem exists_isE0_of_tendstoUniformlyOn_and_measure
    (hK : IsCompact (closure (Ω : Set (ComplexModel n))))
    (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    (hu : ContinuousOn u (closure (Ω : Set (ComplexModel n))))
    (hzero : ∀ x ∈ frontier (Ω : Set (ComplexModel n)), u x = 0)
    (hU : TendstoUniformlyOn q u atTop Ω)
    {ν : Measure (ComplexModel n)} (hν : ν univ < ⊤)
    (hν₀ : ν (Ω : Set (ComplexModel n))ᶜ = 0)
    (hTest : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun j => ∫ x, φ x ∂topMeasure (hq j)) atTop (𝓝 (∫ x, φ x ∂ν))) :
    ∃ hu : IsE0 Ω u, topMeasure hu.locallyBoundedPsh = ν := by
  let hp := isLocallyBoundedPshOn_of_tendstoUniformlyOn hq hU
  have hEq : topMeasure hp = ν := by
    apply ambientMeasure_eq_of_smooth_test (topMeasure_compl hp) hν₀
      (fun _ => topMeasure_finite_on_compact hp)
      (fun K _ _ => (measure_mono (subset_univ K)).trans_lt hν)
    intro φ
    exact tendsto_nhds_unique
      (tendsto_topMeasure_of_tendstoUniformlyOn hq hU φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
      (hTest φ)
  have hBound : ∃ C : ℝ, ∀ x ∈ Ω, |u x| ≤ C := by
    obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hu.abs).bddAbove
    exact ⟨C, fun x hx => hC ⟨x, subset_closure hx, rfl⟩⟩
  have hTrace (x : ComplexModel n) (hx : x ∈ frontier (Ω : Set (ComplexModel n))) :
      Tendsto u (𝓝[Ω] x) (𝓝 0) := by
    rw [← hzero x hx]
    exact (hu x (frontier_subset_closure hx)).mono subset_closure
  let huE : IsE0 Ω u := ⟨hp.1, hBound, hTrace, hEq.symm ▸ hν⟩
  exact ⟨huE, hEq⟩

end KEBall.Cegrell

#print axioms KEBall.Cegrell.exists_isE0_of_tendstoUniformlyOn_and_measure
