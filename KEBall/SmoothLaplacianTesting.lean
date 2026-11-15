import KEBall.BedfordTaylorTestMeasure
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Integration by parts against a compactly supported Laplacian test
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace InnerProductSpace
open scoped ContDiff Distributions Laplacian SchwartzMap Topology

namespace KEBall

open BedfordTaylor

/-- Taking the Laplacian preserves containment of the topological support. -/
theorem tsupport_laplacian_subset {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (φ : V → ℝ) :
    tsupport (Δ φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hxφ
  have he : φ =ᶠ[𝓝 x] (0 : V → ℝ) := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxφ] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hz := (laplacian_congr_nhds he).eq_of_nhds
  change Δ φ x = Δ (fun _ : V => (0 : ℝ)) x at hz
  exact hx (by simpa only [laplacian_const, Pi.zero_apply] using hz)

/-- The ordinary Laplacian is symmetric when one smooth factor has
compact support. -/
theorem integral_mul_laplacian_eq_of_compact_test {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f φ : V → ℝ} (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, f x * Δ φ x) = ∫ x, Δ f x * φ x := by
  have hφV : tsupport φ ⊆ (⊤ : Opens V) := by simp
  obtain ⟨W, hW, hφW, _, hWc⟩ :=
    exists_open_between_and_isCompact_closure hφc isOpen_univ hφV
  obtain ⟨χ, _, hχ⟩ := exists_testFunction_one_on (U := ⊤) hWc (by simp)
  let g (x : V) := χ x * f x
  have hg : ContDiff ℝ ∞ g := χ.contDiff.mul hf
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mul_right
  let a := hgc.toSchwartzMap hg
  let b := hφc.toSchwartzMap hφ
  have hSchwartz := SchwartzMap.integral_mul_laplacian_right_eq_left (μ := volume) a b
  simp only [SchwartzMap.laplacian_apply] at hSchwartz

  change (∫ x, g x * Δ φ x) = ∫ x, Δ g x * φ x at hSchwartz
  have heq (x : V) (hx : x ∈ tsupport φ) : g =ᶠ[𝓝 x] f := by
    filter_upwards [hW.mem_nhds (hφW hx)] with y hy
    change χ y * f y = f y
    rw [hχ (subset_closure hy), Pi.one_apply, one_mul]
  have hφzero (x : V) (hx : x ∉ tsupport φ) : Δ φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_laplacian_subset φ h))
  calc
    _ = ∫ x, g x * Δ φ x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport φ
      · rw [(heq x hx).eq_of_nhds]
      · rw [hφzero x hx, mul_zero, mul_zero]
    _ = ∫ x, Δ g x * φ x := hSchwartz
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport φ
      · rw [(laplacian_congr_nhds (heq x hx)).eq_of_nhds]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

/-- The integral of a compactly supported smooth Laplacian vanishes. -/
theorem integral_laplacian_eq_zero_of_compactSupport {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, Δ φ x) = 0 := by
  simpa only [one_mul, laplacian_const, Pi.zero_apply, zero_mul, integral_zero] using
    integral_mul_laplacian_eq_of_compact_test (f := fun _ : V => (1 : ℝ))
      contDiff_const hφ hφc

/-- A compactly supported smooth Laplacian is integrable. -/
theorem integrable_laplacian_of_compactSupport {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (Δ φ) := by
  let f := hφc.toSchwartzMap hφ
  have hf : ((Δ f : 𝓢(V, ℝ)) : V → ℝ) = Δ φ :=
    funext fun x => SchwartzMap.laplacian_apply f x
  rw [← hf]
  exact (Δ f).integrable

end KEBall
