import KEBall.DirichletTangentBall

/-! The two actual boundary defects and their source terms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped BigOperators ContDiff

noncomputable section

namespace KEBall

def dirichletLowerBoundaryDefect {n : ℕ} (q : E n → ℝ) (m : ℝ) (x : E n) : ℝ :=
  q x - m * dirichletBoundaryDistanceProxy x

def dirichletUpperBoundaryDefect {n : ℕ} (q : E n → ℝ) (M : ℝ) (x : E n) : ℝ :=
  M * dirichletBoundaryDistanceProxy x - q x

theorem smoothNear_dirichletLowerBoundaryDefect {n : ℕ} {q : E n → ℝ}
    (hq : SmoothNear (closedUnitBall n) q) (m : ℝ) :
    SmoothNear (closedUnitBall n) (dirichletLowerBoundaryDefect q m) := by
  obtain ⟨U, hU, hSub, hqU⟩ := hq
  exact ⟨U, hU, hSub,
    hqU.sub ((contDiff_dirichletBoundaryDistanceProxy.const_smul m).contDiffOn)⟩

theorem smoothNear_dirichletUpperBoundaryDefect {n : ℕ} {q : E n → ℝ}
    (hq : SmoothNear (closedUnitBall n) q) (M : ℝ) :
    SmoothNear (closedUnitBall n) (dirichletUpperBoundaryDefect q M) := by
  obtain ⟨U, hU, hSub, hqU⟩ := hq
  exact ⟨U, hU, hSub,
    ((contDiff_dirichletBoundaryDistanceProxy.const_smul M).contDiffOn).sub hqU⟩

theorem dirichlet_boundary_defect_sum {n : ℕ} (q : E n → ℝ) (m M : ℝ) (x : E n) :
    dirichletLowerBoundaryDefect q m x + dirichletUpperBoundaryDefect q M x =
      (M - m) * dirichletBoundaryDistanceProxy x := by
  unfold dirichletLowerBoundaryDefect dirichletUpperBoundaryDefect
  ring

theorem dirichlet_boundary_defect_contractions {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (A : E n →L[ℝ] E n)
    {q : E n → ℝ} {x : E n} (hq : ContDiffAt ℝ 2 q x) (m M : ℝ) :
    dirichletBilinearContraction b A (realHessian (dirichletLowerBoundaryDefect q m) x) =
      dirichletBilinearContraction b A (realHessian q x) +
        m * (∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i)) ∧
    dirichletBilinearContraction b A (realHessian (dirichletUpperBoundaryDefect q M) x) =
      -dirichletBilinearContraction b A (realHessian q x) -
        M * (∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i)) := by
  have hρ : ContDiffAt ℝ 2 (@dirichletBoundaryDistanceProxy n) x :=
    (contDiff_dirichletBoundaryDistanceProxy.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  let F := dirichletHessianContractionLinearMap b A
  have hmρ : ContDiffAt ℝ 2 (m • (@dirichletBoundaryDistanceProxy n)) x := by
    simpa only [Pi.smul_apply] using! hρ.const_smul m
  have hMρ : ContDiffAt ℝ 2 (M • (@dirichletBoundaryDistanceProxy n)) x := by
    simpa only [Pi.smul_apply] using! hρ.const_smul M
  constructor
  · change F (realHessian (q - m • (@dirichletBoundaryDistanceProxy n)) x) = _
    rw [dirichlet_realHessian_sub_C2 (v := m • (@dirichletBoundaryDistanceProxy n)) hq hmρ,
      dirichlet_realHessian_smul_C2 hρ m, map_sub, map_smul, smul_eq_mul]
    change dirichletBilinearContraction b A (realHessian q x) -
      m * dirichletBilinearContraction b A (realHessian (@dirichletBoundaryDistanceProxy n) x) = _
    rw [dirichletBilinearContraction_boundaryDistanceProxy]
    ring
  · change F (realHessian (M • (@dirichletBoundaryDistanceProxy n) - q) x) = _
    rw [dirichlet_realHessian_sub_C2 (u := M • (@dirichletBoundaryDistanceProxy n)) hMρ hq,
      dirichlet_realHessian_smul_C2 hρ M, map_sub, map_smul, smul_eq_mul]
    change M * dirichletBilinearContraction b A (realHessian (@dirichletBoundaryDistanceProxy n) x) -
      dirichletBilinearContraction b A (realHessian q x) = _
    rw [dirichletBilinearContraction_boundaryDistanceProxy]
    ring

theorem dirichlet_boundary_defect_source_bounds {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {A : E n →L[ℝ] E n}
    {K B S m M : ℝ} (hNorm : ‖A‖ ≤ K) (hB : 0 ≤ B)
    (hPos : ∀ v : E n, 0 ≤ inner ℝ (A v) v)
    (hmB : -B ≤ m) (hmM : m ≤ M) (hMB : M ≤ B)
    {q : E n → ℝ} {x : E n} (hq : ContDiffAt ℝ 2 q x)
    (hSource : |dirichletBilinearContraction b A (realHessian q x)| ≤ S) :
    dirichletBilinearContraction b A (realHessian (dirichletLowerBoundaryDefect q m) x) ≤
      S + B * (2 * n : ℝ) * K ∧
    dirichletBilinearContraction b A (realHessian (dirichletUpperBoundaryDefect q M) x) ≤
      S + B * (2 * n : ℝ) * K := by
  obtain ⟨hLower, hUpper⟩ := dirichlet_boundary_defect_contractions b A hq m M
  rw [hLower, hUpper]
  let t : ℝ := ∑ i : Fin (2 * n), inner ℝ (A (b i)) (b i)
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => hPos (b i)
  have htK : t ≤ (2 * n : ℝ) * K :=
    (dirichlet_coefficient_trace_le_norm b A).trans
      (mul_le_mul_of_nonneg_left hNorm (by positivity))
  have htB := mul_le_mul_of_nonneg_left htK hB
  have hmT := mul_le_mul_of_nonneg_right (hmM.trans hMB) ht0
  have hMT := mul_le_mul_of_nonneg_right (show -M ≤ B by linarith) ht0
  obtain ⟨hSlo, hShi⟩ := abs_le.mp hSource
  constructor <;> nlinarith only [htB, hmT, hMT, hSlo, hShi]

theorem dirichlet_boundary_defects_nonnegative {n : ℕ} {q : E n → ℝ}
    (hq0 : ∀ x ∈ unitSphere n, q x = 0) {m M : ℝ} {x : E n}
    (hx : x ∈ closedUnitBall n)
    (hBounds : x ∈ unitBall n →
      m ≤ q x / dirichletBoundaryDistanceProxy x ∧ q x / dirichletBoundaryDistanceProxy x ≤ M) :
    0 ≤ dirichletLowerBoundaryDefect q m x ∧ 0 ≤ dirichletUpperBoundaryDefect q M x := by
  by_cases hi : x ∈ unitBall n
  · obtain ⟨hlo, hhi⟩ := hBounds hi
    have hρ := dirichletBoundaryDistanceProxy_pos hi
    have hm := (le_div_iff₀ hρ).mp hlo
    have hM := (div_le_iff₀ hρ).mp hhi
    constructor <;> simp only [dirichletLowerBoundaryDefect, dirichletUpperBoundaryDefect] <;> linarith
  · have hs : x ∈ unitSphere n := by
      apply mem_sphere_zero_iff_norm.mpr
      have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
      have hge : ¬‖x‖ < 1 := fun h => hi (mem_ball_zero_iff.mpr h)
      exact le_antisymm hle (not_lt.mp hge)
    simp only [dirichletLowerBoundaryDefect, dirichletUpperBoundaryDefect,
      hq0 x hs, dirichletBoundaryDistanceProxy_zero_on_sphere hs, mul_zero,
      sub_self, le_refl, and_self]

theorem dirichlet_boundary_defect_quotients {n : ℕ} (q : E n → ℝ) (m M : ℝ)
    {x : E n} (hx : x ∈ unitBall n) :
    dirichletLowerBoundaryDefect q m x / dirichletBoundaryDistanceProxy x =
      q x / dirichletBoundaryDistanceProxy x - m ∧
    dirichletUpperBoundaryDefect q M x / dirichletBoundaryDistanceProxy x =
      M - q x / dirichletBoundaryDistanceProxy x := by
  have hρ := (dirichletBoundaryDistanceProxy_pos hx).ne'
  simp only [dirichletLowerBoundaryDefect, dirichletUpperBoundaryDefect, sub_div,
    mul_div_cancel_right₀ _ hρ, and_self]

end KEBall
