import KEBall.CegrellClass
import PshLines.FirstPass.PshClosedDiscMaximum

/-!
# The zero boundary condition on the unit ball
-/

set_option autoImplicit false

open Filter Metric Set TopologicalSpace
open scoped Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (coordinateVector)

variable {n : ℕ} {u : ComplexModel n → ℝ}

private theorem exists_unit_direction (hn : 0 < n) (z : ComplexModel n) :
    ∃ v : ComplexModel n, ‖v‖ = 1 ∧ (‖z‖ : ℂ) • v = z := by
  by_cases hz : z = 0
  · subst z
    exact ⟨coordinateVector ⟨0, hn⟩, by simp [coordinateVector], by simp⟩
  · let r : ℂ := ‖z‖
    have hr : r ≠ 0 := by
      change ((‖z‖ : ℝ) : ℂ) ≠ 0
      exact_mod_cast norm_ne_zero_iff.mpr hz
    refine ⟨r⁻¹ • z, ?_, ?_⟩
    · rw [norm_smul, norm_inv, show ‖r‖ = ‖z‖ by simp [r]]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)
    · change r • r⁻¹ • z = z
      rw [smul_smul, mul_inv_cancel₀ hr, one_smul]

/-- The ball maximum principle gives the sign of a bounded potential
with zero boundary values. -/
theorem IsE0.nonpositive_unitBall (hn : 0 < n) (hu : IsE0 (complexUnitBall n) u) :
    ∀ x ∈ complexUnitBall n, u x ≤ 0 := by
  intro z hz
  by_contra! hzPos
  let B : Set (ComplexModel n) := complexUnitBall n
  let ε := u z / 2
  have hε : 0 < ε := half_pos hzPos
  let F := {x | x ∈ B ∧ ε ≤ u x}
  have hzF : z ∈ F := ⟨hz, half_le_self hzPos.le⟩
  have hFB : F ⊆ B := fun _ hx => hx.1
  have hFcl : closure F ⊆ B := by
    intro x hx
    by_contra hxB
    have hxFront : x ∈ frontier B := by
      rw [frontier, (complexUnitBall n).isOpen.interior_eq]
      exact ⟨closure_mono hFB hx, hxB⟩
    let : NeBot (𝓝[F] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
    have hlim : Tendsto u (𝓝[F] x) (𝓝 0) :=
      (hu.boundary x hxFront).mono_left (nhdsWithin_mono x hFB)
    have hmem : ∀ᶠ y in 𝓝[F] x, y ∈ F := self_mem_nhdsWithin
    obtain ⟨y, hyF, hylt⟩ := (hmem.and (hlim.eventually_lt_const hε)).exists
    exact (not_lt_of_ge hyF.2) hylt
  have hBball : B ⊆ closedBall (0 : ComplexModel n) 1 := ball_subset_closedBall
  have hK : IsCompact (closure F) :=
    (isCompact_closedBall (0 : ComplexModel n) 1).of_isClosed_subset isClosed_closure
      (closure_minimal (hFB.trans hBball) isClosed_closedBall)
  obtain ⟨y, hy, hyMax⟩ := hK.exists_isMaxOn ⟨z, subset_closure hzF⟩ continuous_norm.continuousOn
  have hyB : ‖y‖ < 1 := by simpa [B, complexUnitBall, mem_ball] using hFcl hy
  let r := (‖y‖ + 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hyr : ‖y‖ < r := by dsimp [r]; linarith
  have hnear (x : ComplexModel n) (hx : ‖x‖ = r) : u x < ε := by
    by_contra! hxu
    have hxB : x ∈ B := by simpa [B, complexUnitBall, mem_ball, hx] using hr₁
    have hxy : ‖x‖ ≤ ‖y‖ := hyMax (subset_closure (show x ∈ F from ⟨hxB, hxu⟩))
    exact (not_lt_of_ge (hx ▸ hxy)) hyr
  obtain ⟨v, hv, hrepr⟩ := exists_unit_direction hn z
  let A : ℂ →L[ℂ] ComplexModel n := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  have hmaps : MapsTo A (ball (0 : ℂ) 1) B := by
    intro w hw
    change dist (w • v) 0 < 1
    rwa [dist_zero_right, norm_smul, hv, mul_one, ← dist_zero_right]
  have hd := hu.psh.discPshOn
  have hdisc : DiscPshOn (fun w : ℂ => (u (A w) : EReal)) (ball 0 1) := by
    refine ⟨fun w hw => hd.ne_top (A w) (hmaps hw),
      hd.upperSemicontinuousOn.comp A.continuous.continuousOn hmaps, ?_⟩
    intro w d R hR hD C hC
    have hA (ζ : ℂ) : A (w + ζ • d) = A w + ζ • A d := by rw [map_add, map_smul]
    have hD' : affineClosedDisc (A w) (A d) R ⊆ B := by
      rintro _ ⟨ζ, hζ, rfl⟩
      change A w + ζ • A d ∈ B
      rw [← hA]
      exact hmaps (hD ⟨ζ, hζ, rfl⟩)
    have hC' : ∀ x ∈ affineClosedDisc (A w) (A d) R, (u x : EReal) ≤ C := by
      rintro _ ⟨ζ, hζ, rfl⟩
      change (u (A w + ζ • A d) : EReal) ≤ C
      rw [← hA]
      exact hC _ ⟨ζ, hζ, rfl⟩
    simpa only [circleDeficit, hA] using hd.submean (A w) (A d) R hR hD' C hC'
  have hpsh := hdisc.plurisubharmonicOn isOpen_ball
  have hD := closedBall_subset_ball (x := (0 : ℂ)) hr₁
  have hs (w : ℂ) (hw : w ∈ sphere (0 : ℂ) r) : (u (A w) : EReal) ≤ (ε : EReal) := by
    apply EReal.coe_le_coe_iff.mpr
    apply (hnear (A w) _).le
    change ‖w • v‖ = r
    rwa [norm_smul, hv, mul_one, ← dist_zero_right]
  have hzMem : (‖z‖ : ℂ) ∈ closedBall (0 : ℂ) r := by
    have hzy : ‖z‖ ≤ ‖y‖ := hyMax (subset_closure hzF)
    simpa [mem_closedBall] using hzy.trans hyr.le
  have h := hpsh.le_const_on_closedBall_of_le_on_sphere hr hD hs _ hzMem
  have hle := EReal.coe_le_coe_iff.mp h
  change u ((‖z‖ : ℂ) • v) ≤ ε at hle
  rw [hrepr] at hle
  dsimp [ε] at hle
  linarith

theorem IsE1.nonpositive_unitBall (hn : 0 < n)
    {v : ComplexModel n → EReal} (hv : IsE1 (complexUnitBall n) v) :
    ∀ x ∈ complexUnitBall n, v x ≤ 0 := by
  intro x hx
  obtain ⟨p⟩ := hv.2
  apply le_of_tendsto (p.pointwise x hx)
  exact Eventually.of_forall fun j => by
    exact_mod_cast (p.term_mem j).nonpositive_unitBall hn x hx

end KEBall.Cegrell
