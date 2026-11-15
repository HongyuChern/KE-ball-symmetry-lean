import KEBall.BedfordTaylorObstacleContact
import KEBall.BedfordTaylorObstacleEnvelope
import KEBall.BedfordTaylorScaling
import KEBall.CegrellClass

/-!
# The zero-boundary envelope of a zero-extended potential
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω V : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

/-- A negative PSH exhaustion uniformly below zero on the smaller domain
provides the boundary barrier for the greatest PSH minorant. -/
theorem exists_zeroExtendedObstacle_envelope (hu : IsE0 Ω u)
    (hu₀ : ∀ x ∈ Ω, u x ≤ 0)
    (hvol : (volume : Measure (ComplexModel n)) V < ⊤)
    {ρ : ComplexModel n → ℝ} (hρ : IsLocallyBoundedPshOn V ρ)
    (hρ₀ : ∀ x ∈ V, ρ x ≤ 0)
    (hρboundary : ∀ z ∈ frontier (V : Set (ComplexModel n)), Tendsto ρ (𝓝[V] z) (𝓝 0))
    {η : ℝ} (hη : 0 < η) (hρΩ : ∀ x ∈ Ω, ρ x ≤ -η) :
    let f := (Ω : Set (ComplexModel n)).indicator u
    ∃ v : ComplexModel n → ℝ,
      IsLocallyBoundedPshOn V v ∧ (∃ M : ℝ, ∀ x ∈ V, |v x| ≤ M) ∧
      (∀ x ∈ V, v x ≤ f x) ∧
      (∀ z ∈ frontier (V : Set (ComplexModel n)), Tendsto v (𝓝[V] z) (𝓝 0)) ∧
      (∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn V w →
        (∀ x ∈ V, w x ≤ f x) → ∀ x ∈ V, w x ≤ v x) ∧
      ∃ A > 0, ∀ x ∈ V, A * ρ x ≤ v x := by
  let f := (Ω : Set (ComplexModel n)).indicator u
  have hf₀ (x : ComplexModel n) : f x ≤ 0 := by
    by_cases hx : x ∈ Ω
    · simpa only [f, indicator_of_mem hx] using hu₀ x hx
    · simp only [f, indicator_of_notMem hx, le_refl]
  have hf : UpperSemicontinuousOn (fun x => (f x : EReal)) V := by
    intro x hx a ha
    by_cases hxΩ : x ∈ Ω
    · have hEq (y : ComplexModel n) (hy : y ∈ Ω) : f y = u y := indicator_of_mem hy _
      have huEvt : ∀ᶠ y in 𝓝[Ω] x, (u y : EReal) < a :=
        hu.psh.upperSemicontinuousOn x hxΩ a (by simpa only [hEq x hxΩ] using ha)
      have huFull := (Ω.isOpen.nhdsWithin_eq hxΩ) ▸ huEvt
      have h := huFull.and (show ∀ᶠ y in 𝓝 x, y ∈ Ω from Ω.isOpen.mem_nhds hxΩ)
      exact (h.mono fun y hy => by simpa only [hEq y hy.2] using hy.1).filter_mono nhdsWithin_le_nhds
    · have ha₀ : (0 : EReal) < a := by simpa [f, indicator_of_notMem hxΩ] using ha
      exact Eventually.of_forall fun y =>
        (EReal.coe_le_coe_iff.mpr (hf₀ y)).trans_lt ha₀
  obtain ⟨C, hC⟩ := hu.bounded
  let m := min (-C) 0
  have hm : m ≤ 0 := min_le_right _ _
  have hmf (x : ComplexModel n) : m ≤ f x := by
    by_cases hx : x ∈ Ω
    · rw [show f x = u x from indicator_of_mem hx _]
      exact (min_le_left _ _).trans (by linarith [neg_le_abs (u x), hC x hx])
    · rw [show f x = 0 from indicator_of_notMem hx _]
      exact hm
  obtain ⟨v, hv, hvBound, hgreatest⟩ := exists_bounded_psh_envelope hf
    (fun x _ => EReal.coe_le_coe_iff.mpr (hmf x))
    (fun x _ => EReal.coe_le_coe_iff.mpr (hf₀ x)) hvol
  have hvf (x : ComplexModel n) (hx : x ∈ V) : v x ≤ f x :=
    EReal.coe_le_coe_iff.mp (hvBound x hx).2
  have hv₀ (x : ComplexModel n) (hx : x ∈ V) : v x ≤ 0 := (hvf x hx).trans (hf₀ x)
  let A := (1 - m) / η
  have hA : 0 < A := div_pos (by linarith) hη
  have hAη : A * η = 1 - m := div_mul_cancel₀ _ hη.ne'
  have hbarrier (x : ComplexModel n) (hx : x ∈ V) : A * ρ x ≤ f x := by
    by_cases hxΩ : x ∈ Ω
    · have h := mul_le_mul_of_nonneg_left (hρΩ x hxΩ) hA.le
      rw [mul_neg, hAη] at h
      exact h.trans ((by linarith : -(1 - m) ≤ m).trans (hmf x))
    · rw [show f x = 0 from indicator_of_notMem hxΩ _]
      exact mul_nonpos_of_nonneg_of_nonpos hA.le (hρ₀ x hx)
  have hρv := hgreatest _ (locallyBoundedPsh_const_mul hρ hA)
    (fun x hx => EReal.coe_le_coe_iff.mpr (hbarrier x hx))
  refine ⟨v, hv, ⟨-m, fun x hx => ?_⟩, hvf, ?_, ?_, A, hA, hρv⟩
  · rw [abs_of_nonpos (hv₀ x hx)]
    exact neg_le_neg (hvBound x hx).1
  · intro z hz
    have ht : Tendsto (fun x => A * ρ x) (𝓝[V] z) (𝓝 0) := by
      simpa only [mul_zero] using (hρboundary z hz).const_mul A
    have hmem : ∀ᶠ x in 𝓝[V] z, x ∈ V := self_mem_nhdsWithin
    exact ht.squeeze' tendsto_const_nhds (hmem.mono hρv) (hmem.mono hv₀)
  · exact fun w hw hwf => hgreatest w hw (fun x hx => EReal.coe_le_coe_iff.mpr (hwf x hx))

/-- The contact-set support property makes a bounded zero-boundary envelope
an E₀ subextension, with no increase in total Monge–Ampère mass. -/
theorem IsE0.of_zeroExtendedObstacle_contact (hn : 0 < n) (hu : IsE0 Ω u)
    (hu₀ : ∀ x ∈ Ω, u x ≤ 0) (hΩV : Ω ≤ V)
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn V v)
    (hvB : ∃ M : ℝ, ∀ x ∈ V, |v x| ≤ M)
    (hvf : ∀ x ∈ V, v x ≤ (Ω : Set (ComplexModel n)).indicator u x)
    (hvBoundary : ∀ z ∈ frontier (V : Set (ComplexModel n)), Tendsto v (𝓝[V] z) (𝓝 0))
    (hcontact : topMeasure hv {x ∈ V | v x < (Ω : Set (ComplexModel n)).indicator u x} = 0) :
    IsE0 V v ∧ topMeasure hv ≤ topMeasure hu.locallyBoundedPsh ∧ ∀ x ∈ Ω, v x ≤ u x := by
  have hvu (x : ComplexModel n) (hx : x ∈ Ω) : v x ≤ u x := by
    simpa only [indicator_of_mem hx] using hvf x (hΩV hx)
  have hv₀ (x : ComplexModel n) (hx : x ∈ V) : v x ≤ 0 := by
    by_cases hxΩ : x ∈ Ω
    · exact (hvu x hxΩ).trans (hu₀ x hxΩ)
    · simpa only [indicator_of_notMem hxΩ] using hvf x hx
  have hm := topMeasure_le_of_zeroExtendedObstacle_contact hn hu.locallyBoundedPsh hv
    hΩV hvu hv₀ hcontact
  exact ⟨⟨hv.1, hvB, hvBoundary, (hm univ).trans_lt hu.finiteMass⟩, hm, hvu⟩

end KEBall.Cegrell
