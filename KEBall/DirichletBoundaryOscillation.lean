import KEBall.DirichletBoundaryInterval

/-! Pointwise oscillation on boundary caps of the actual open unit ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Metric Set

noncomputable section

namespace KEBall

def dirichletBoundaryCap {n : ℕ} (p : E n) (r : ℝ) : Set (E n) :=
  unitBall n ∩ ball p r

def dirichletBoundaryOscillation {n : ℕ} (f : E n → ℝ) (p : E n) (r : ℝ) : ℝ :=
  sSup (f '' dirichletBoundaryCap p r) - sInf (f '' dirichletBoundaryCap p r)

theorem dirichletBoundaryCap_nonempty {n : ℕ} {p : E n} (hp : p ∈ unitSphere n)
    {r : ℝ} (hr : 0 < r) : (dirichletBoundaryCap p r).Nonempty := by
  have h := dirichlet_boundary_small_cap_nonempty hp
    (lt_min zero_lt_one hr) (min_le_left (1 : ℝ) r)
  apply h.mono
  intro x hx
  refine ⟨hx.1, ball_subset_ball ?_ hx.2⟩
  have hmin := min_le_right (1 : ℝ) r
  linarith

theorem dirichlet_bounded_function_extrema {X : Type*} {s : Set X}
    (hs : s.Nonempty) (f : X → ℝ) {a b : ℝ} (hBounds : ∀ x ∈ s, a ≤ f x ∧ f x ≤ b) :
    a ≤ sInf (f '' s) ∧ sSup (f '' s) ≤ b ∧ sInf (f '' s) ≤ sSup (f '' s) ∧
      ∀ x ∈ s, sInf (f '' s) ≤ f x ∧ f x ≤ sSup (f '' s) := by
  have hLo : BddBelow (f '' s) := ⟨a, by rintro _ ⟨x, hx, rfl⟩; exact (hBounds x hx).1⟩
  have hHi : BddAbove (f '' s) := ⟨b, by rintro _ ⟨x, hx, rfl⟩; exact (hBounds x hx).2⟩
  have hRange (x : X) (hx : x ∈ s) : sInf (f '' s) ≤ f x ∧ f x ≤ sSup (f '' s) :=
    ⟨csInf_le hLo (mem_image_of_mem f hx), le_csSup hHi (mem_image_of_mem f hx)⟩
  have hImage : (f '' s).Nonempty := hs.image f
  obtain ⟨x₀, hx₀⟩ := hs
  refine ⟨le_csInf hImage ?_, csSup_le hImage ?_,
    (hRange x₀ hx₀).1.trans (hRange x₀ hx₀).2, hRange⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hBounds x hx).1
  · rintro _ ⟨x, hx, rfl⟩
    exact (hBounds x hx).2

theorem dirichletBoundaryOscillation_le_of_bounds {n : ℕ}
    (f : E n → ℝ) {p : E n} (hp : p ∈ unitSphere n) {r : ℝ} (hr : 0 < r)
    {a b : ℝ} (hBounds : ∀ x ∈ dirichletBoundaryCap p r, a ≤ f x ∧ f x ≤ b) :
    0 ≤ dirichletBoundaryOscillation f p r ∧ dirichletBoundaryOscillation f p r ≤ b - a := by
  obtain ⟨ha, hb, hOrder, _⟩ := dirichlet_bounded_function_extrema
    (dirichletBoundaryCap_nonempty hp hr) f hBounds
  exact ⟨sub_nonneg.mpr hOrder, sub_le_sub hb ha⟩

theorem dirichletBoundaryOscillation_mono {n : ℕ}
    (f : E n → ℝ) {p : E n} (hp : p ∈ unitSphere n) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) {a b : ℝ}
    (hBounds : ∀ x ∈ dirichletBoundaryCap p R, a ≤ f x ∧ f x ≤ b) :
    dirichletBoundaryOscillation f p r ≤ dirichletBoundaryOscillation f p R := by
  have hSub : dirichletBoundaryCap p r ⊆ dirichletBoundaryCap p R :=
    fun _ hx => ⟨hx.1, ball_subset_ball hrR hx.2⟩
  have hLarge := (dirichlet_bounded_function_extrema
    (dirichletBoundaryCap_nonempty hp (hr.trans_le hrR)) f hBounds).2.2.2
  have hSmall (x : E n) (hx : x ∈ dirichletBoundaryCap p r) := hLarge x (hSub hx)
  exact (dirichletBoundaryOscillation_le_of_bounds f hp hr hSmall).2

theorem abs_sub_le_dirichletBoundaryOscillation {n : ℕ}
    (f : E n → ℝ) {p : E n} (hp : p ∈ unitSphere n) {r : ℝ} (hr : 0 < r)
    {a b : ℝ} (hBounds : ∀ x ∈ dirichletBoundaryCap p r, a ≤ f x ∧ f x ≤ b)
    {x y : E n} (hx : x ∈ dirichletBoundaryCap p r) (hy : y ∈ dirichletBoundaryCap p r) :
    |f x - f y| ≤ dirichletBoundaryOscillation f p r := by
  have hRange := (dirichlet_bounded_function_extrema (dirichletBoundaryCap_nonempty hp hr) f hBounds).2.2.2
  obtain ⟨hxLo, hxHi⟩ := hRange x hx
  obtain ⟨hyLo, hyHi⟩ := hRange y hy
  rw [abs_le]
  unfold dirichletBoundaryOscillation
  constructor <;> linarith

end KEBall
