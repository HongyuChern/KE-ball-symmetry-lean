import KEBall.BedfordTaylorObstacleMaximality
import Mathlib.Analysis.Convex.Basic

/-!
# Local Lipschitz bounds for envelopes on convex domains
-/

set_option autoImplicit false

open Metric Set TopologicalSpace

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u f : ComplexModel n → ℝ}

private theorem obstacleEnvelope_sub_le {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    (hΩ : Convex ℝ (Ω : Set (ComplexModel n))) (hbounded : Bornology.IsBounded (Ω : Set (ComplexModel n)))
    (hu : IsLocallyBoundedPshOn Ω u) (huf : ∀ x ∈ Ω, u x ≤ f x)
    (hgreatest : ∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω w →
      (∀ x ∈ Ω, w x ≤ f x) → ∀ x ∈ Ω, w x ≤ u x)
    (hf : ∀ x ∈ Ω, ∀ y ∈ Ω, f y - f x ≤ L * dist y x)
    {x y : ComplexModel n} (hx : x ∈ Ω) (hball : closedBall x r ⊆ Ω)
    (hxy : dist y x ≤ r) :
    u y - u x ≤ L * diam (Ω : Set (ComplexModel n)) / r * dist y x := by
  by_cases hyx : y = x
  · simp [hyx]
  let t := dist y x / r
  have ht : 0 < t := div_pos (dist_pos.mpr hyx) hr
  have ht₁ : t ≤ 1 := (div_le_one₀ hr).mpr hxy
  let a : ComplexModel n := x + t⁻¹ • (y - x)
  have ha_dist : dist a x = r := by
    rw [dist_eq_norm, show a - x = t⁻¹ • (y - x) by dsimp only [a]; abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), ← dist_eq_norm]
    dsimp only [t]
    field_simp [hr.ne', (dist_pos.mpr hyx).ne']
  have ha : a ∈ Ω := hball (by rw [mem_closedBall, ha_dist])
  let F (z : ComplexModel n) := (1 - t) • z + t • a
  have hmap : MapsTo F Ω Ω := fun z hz =>
    hΩ hz ha (sub_nonneg.mpr ht₁) ht.le (sub_add_cancel 1 t)
  have hF : DifferentiableOn ℂ F Ω := by
    have h := (differentiable_id.const_smul ((1 - t : ℝ) : ℂ)).add
      (differentiable_const (t • a) (𝕜 := ℂ) (E := ComplexModel n))
    change Differentiable ℂ (fun z : ComplexModel n => ((1 - t : ℝ) : ℂ) • z + t • a) at h
    have hEq : F = (fun z : ComplexModel n => ((1 - t : ℝ) : ℂ) • z + t • a) := by
      funext z
      exact congrArg (fun w : ComplexModel n => w + t • a)
        (RCLike.real_smul_eq_coe_smul (K := ℂ) (1 - t) z)
    rw [hEq]
    exact h.differentiableOn
  have hFx : F x = y := by
    dsimp only [F, a]
    rw [sub_smul, one_smul, smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    abel
  have hFdist (z : ComplexModel n) (hz : z ∈ Ω) : dist (F z) z ≤ t * diam (Ω : Set (ComplexModel n)) := by
    rw [dist_eq_norm, show F z - z = t • (a - z) by
      dsimp only [F]
      rw [sub_smul, one_smul, smul_sub]
      abel, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (dist_le_diam_of_mem hbounded ha hz) ht.le
  let C := L * (t * diam (Ω : Set (ComplexModel n)))
  have hw : IsLocallyBoundedPshOn Ω (fun z => u (F z) + -C) :=
    locallyBoundedPsh_add_const (locallyBoundedPsh_comp_holomorphic hu hF hmap) _
  have hwf (z : ComplexModel n) (hz : z ∈ Ω) : u (F z) + -C ≤ f z := by
    have h := (hf z hz (F z) (hmap hz)).trans (mul_le_mul_of_nonneg_left (hFdist z hz) hL)
    linarith [huf (F z) (hmap hz)]
  have h := hgreatest _ hw hwf x hx
  rw [hFx] at h
  have hC : C = L * diam (Ω : Set (ComplexModel n)) / r * dist y x := by
    dsimp only [C, t]
    ring
  linarith

/-- On a convex bounded domain, the envelope of a Lipschitz obstacle is
Lipschitz on each ball whose doubled closed ball lies in the domain. -/
theorem obstacleEnvelope_dist_le {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    (hΩ : Convex ℝ (Ω : Set (ComplexModel n))) (hbounded : Bornology.IsBounded (Ω : Set (ComplexModel n)))
    (hu : IsLocallyBoundedPshOn Ω u) (huf : ∀ x ∈ Ω, u x ≤ f x)
    (hgreatest : ∀ w : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω w →
      (∀ x ∈ Ω, w x ≤ f x) → ∀ x ∈ Ω, w x ≤ u x)
    (hf : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (f y) (f x) ≤ L * dist y x)
    {z x y : ComplexModel n} (hball : closedBall z (2 * r) ⊆ Ω)
    (hx : x ∈ ball z (r / 2)) (hy : y ∈ ball z (r / 2)) :
    dist (u y) (u x) ≤ L * diam (Ω : Set (ComplexModel n)) / r * dist y x := by
  have hsub (a : ComplexModel n) (ha : a ∈ ball z (r / 2)) :
      closedBall a r ⊆ Ω := by
    intro b hb
    apply hball
    rw [mem_closedBall]
    have hh := (dist_triangle b a z).trans (add_le_add (mem_closedBall.mp hb) (mem_ball.mp ha).le)
    linarith
  have hxΩ := hsub x hx (mem_closedBall_self hr.le)
  have hyΩ := hsub y hy (mem_closedBall_self hr.le)
  have hxy : dist y x ≤ r := by
    have hzX : dist z x ≤ r / 2 := (dist_comm z x).trans_le (mem_ball.mp hx).le
    have h := (dist_triangle y z x).trans (add_le_add (mem_ball.mp hy).le hzX)
    linarith
  have hf' (a : ComplexModel n) (ha : a ∈ Ω) (b : ComplexModel n) (hb : b ∈ Ω) :
      f b - f a ≤ L * dist b a :=
    (le_abs_self _).trans (by simpa only [Real.dist_eq] using hf a ha b hb)
  have hyx := obstacleEnvelope_sub_le hr hL hΩ hbounded hu huf hgreatest hf' hxΩ (hsub x hx) hxy
  have hxy' := obstacleEnvelope_sub_le hr hL hΩ hbounded hu huf hgreatest hf' hyΩ (hsub y hy)
    (by rwa [dist_comm x y])
  rw [dist_comm x y] at hxy'
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith, hyx⟩

end KEBall.BedfordTaylor
