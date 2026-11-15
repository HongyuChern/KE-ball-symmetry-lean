import KEBall.DirichletBoundaryOscillation

/-!
# Passing boundary oscillation estimates to a specified pointwise limit

The limit function is part of the input.  These lemmas do not replace a
previously selected PDE limit by a new existential witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped Topology

namespace KEBall

theorem dirichletBoundaryOscillation_le_of_pairwise {n : ℕ}
    (f : E n → ℝ) {p : E n} (hp : p ∈ unitSphere n) {r : ℝ} (hr : 0 < r)
    {C : ℝ} (hPair : ∀ x ∈ dirichletBoundaryCap p r,
      ∀ y ∈ dirichletBoundaryCap p r, |f x - f y| ≤ C) :
    dirichletBoundaryOscillation f p r ≤ C := by
  have hs := (dirichletBoundaryCap_nonempty hp hr).image f
  have hUpper : sSup (f '' dirichletBoundaryCap p r) ≤
      C + sInf (f '' dirichletBoundaryCap p r) := by
    apply csSup_le hs
    rintro _ ⟨x, hx, rfl⟩
    have hLower : f x - C ≤ sInf (f '' dirichletBoundaryCap p r) := by
      apply le_csInf hs
      rintro _ ⟨y, hy, rfl⟩
      have h := (abs_le.mp (hPair x hx y hy)).2
      linarith
    linarith
  unfold dirichletBoundaryOscillation
  linarith

theorem dirichletBoundaryOscillation_le_of_pointwise_limit {n : ℕ}
    {f : ℕ → E n → ℝ} {F : E n → ℝ} {B : ℝ}
    (hB : ∀ m x, x ∈ unitBall n → |f m x| ≤ B)
    (hLim : ∀ x ∈ unitBall n, Tendsto (fun m => f m x) atTop (𝓝 (F x)))
    {p : E n} (hp : p ∈ unitSphere n) {r : ℝ} (hr : 0 < r) {C : ℝ}
    (hOsc : ∀ m, dirichletBoundaryOscillation (f m) p r ≤ C) :
    dirichletBoundaryOscillation F p r ≤ C := by
  apply dirichletBoundaryOscillation_le_of_pairwise F hp hr
  intro x hx y hy
  apply le_of_tendsto' ((hLim x hx.1).sub (hLim y hy.1)).abs
  intro m
  exact (abs_sub_le_dirichletBoundaryOscillation (f m) hp hr
    (fun z hz => abs_le.mp (hB m z hz.1)) hx hy).trans (hOsc m)

theorem abs_dirichlet_pointwise_limit_le {n : ℕ}
    {f : ℕ → E n → ℝ} {F : E n → ℝ} {B : ℝ}
    (hB : ∀ m x, x ∈ unitBall n → |f m x| ≤ B)
    (hLim : ∀ x ∈ unitBall n, Tendsto (fun m => f m x) atTop (𝓝 (F x))) :
    ∀ x ∈ unitBall n, |F x| ≤ B := by
  intro x hx
  exact le_of_tendsto' (hLim x hx).abs (fun m => hB m x hx)

end KEBall
