import KEBall.DirichletBoundaryDefects

/-! A bounded scalar source and zero boundary values give a uniform
boundary quotient bound by an explicit quadratic barrier.  No bound for
the derivative of the function is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

open InnerProductSpace Metric Set
open scoped BigOperators ContDiff

noncomputable section
namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

private theorem scalarSource_trace_lower {n : ℕ} {A : E n →L[ℝ] E n} {c : ℝ}
    (hE : ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    (2 * n : ℝ) * c ≤ ∑ i : Fin (2 * n), inner ℝ (A (e[n] i)) (e[n] i) := by
  calc
    _ = ∑ _ : Fin (2 * n), c := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      simpa only [OrthonormalBasis.norm_eq_one, one_pow, mul_one] using hE (e[n] i)

theorem dirichlet_le_source_boundary_barrier {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} {c S : ℝ} (hc : 0 < c) (hS : 0 ≤ S)
    (hSym : ∀ x ∈ unitBall n, (A x).toLinearMap.IsSymmetric)
    (hEll : ∀ x ∈ unitBall n, ∀ v : E n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {q : E n → ℝ} (hq : SmoothNear (closedUnitBall n) q)
    (hq0 : ∀ x ∈ unitSphere n, q x = 0)
    (hSource : ∀ x ∈ unitBall n,
      -S ≤ dirichletBilinearContraction e[n] (A x) (realHessian q x)) :
    ∀ x ∈ closedUnitBall n,
      q x ≤ (S / (2 * n * c)) * dirichletBoundaryDistanceProxy x := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let M : ℝ := S / (2 * n * c)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hScale : M * ((2 * n : ℝ) * c) = S := by
    dsimp [M]
    exact div_mul_cancel₀ S (by positivity)
  let w := dirichletLowerBoundaryDefect q M
  let b : E n → ℝ := (-1 : ℝ) • (@dirichletBoundaryDistanceProxy n)
  let F (x : E n) := dirichletHessianContractionLinearMap e[n] (A x)
  have hw : SmoothNear (closedUnitBall n) w := smoothNear_dirichletLowerBoundaryDefect hq M
  have hb : ContDiff ℝ ∞ b := contDiff_dirichletBoundaryDistanceProxy.const_smul (-1 : ℝ)
  have hρ2 : ContDiff ℝ 2 (@dirichletBoundaryDistanceProxy n) :=
    contDiff_dirichletBoundaryDistanceProxy.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hI : interior (closedUnitBall n) = unitBall n := interior_closedBall _ (by norm_num)
  have hw2 : ContDiffOn ℝ 2 w (interior (closedUnitBall n)) := by
    rw [hI]
    exact fun x hx => ((hw.contDiffAt (ball_subset_closedBall hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffWithinAt
  have hSign (x : E n) (hx : x ∈ interior (closedUnitBall n))
      (D : E n →L[ℝ] E n →L[ℝ] ℝ) (hD : ∀ v : E n, D v v ≤ 0) : F x D ≤ 0 := by
    rw [hI] at hx
    apply dirichletBilinearContraction_nonpos_of_positive e[n] _ D hD
    exact (ContinuousLinearMap.isPositive_iff _).mpr ⟨hSym x hx,
      fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hEll x hx v)⟩
  have hLw (x : E n) (hx : x ∈ interior (closedUnitBall n)) :
      0 ≤ F x (realHessian w x) := by
    rw [hI] at hx
    have hq2 : ContDiffAt ℝ 2 q x :=
      (hq.contDiffAt (ball_subset_closedBall hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    change 0 ≤ dirichletBilinearContraction e[n] (A x)
      (realHessian (dirichletLowerBoundaryDefect q M) x)
    rw [(dirichlet_boundary_defect_contractions e[n] (A x) hq2 M M).1]
    have hTr := mul_le_mul_of_nonneg_left
      (scalarSource_trace_lower (hEll x hx)) hM
    rw [hScale] at hTr
    have hSrc := hSource x hx
    change S ≤ M * (∑ i : Fin (2 * n), inner ℝ (A x (e[n] i)) (e[n] i)) at hTr
    linarith only [hTr, hSrc]
  have hLb (x : E n) (hx : x ∈ interior (closedUnitBall n)) :
      0 < F x (realHessian b x) := by
    rw [hI] at hx
    rw [show b = (-1 : ℝ) • (@dirichletBoundaryDistanceProxy n) from rfl,
      dirichlet_realHessian_smul_C2 hρ2.contDiffAt, map_smul, smul_eq_mul]
    change 0 < (-1 : ℝ) * dirichletBilinearContraction e[n] (A x)
      (realHessian (@dirichletBoundaryDistanceProxy n) x)
    rw [dirichletBilinearContraction_boundaryDistanceProxy]
    have hTr := scalarSource_trace_lower (hEll x hx)
    have hPos : 0 < (2 * n : ℝ) * c := by positivity
    change (2 * n : ℝ) * c ≤
      (∑ i : Fin (2 * n), inner ℝ (A x (e[n] i)) (e[n] i)) at hTr
    nlinarith only [hTr, hPos]
  have hMax := dirichlet_le_frontier_of_linearHessian_nonneg_with_barrier
    (isCompact_closedBall (0 : E n) 1)
    (fun x hx => (hw.contDiffAt hx).continuousAt.continuousWithinAt)
    hb.continuous.continuousOn
    hw2 (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn
    F hSign hLw hLb
    (fun x hx => by
      have hs : x ∈ unitSphere n := frontier_closedBall_subset_sphere hx
      simp only [b, Pi.smul_apply, smul_eq_mul,
        dirichletBoundaryDistanceProxy_zero_on_sphere hs, mul_zero])
    (C := 0) (fun x hx => by
      have hs : x ∈ unitSphere n := frontier_closedBall_subset_sphere hx
      simp only [w, dirichletLowerBoundaryDefect, hq0 x hs,
        dirichletBoundaryDistanceProxy_zero_on_sphere hs, mul_zero, sub_zero, le_refl])
  intro x hx
  exact sub_nonpos.mp (hMax x hx)

theorem abs_dirichlet_boundary_quotient_le_of_source {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} {c S : ℝ} (hc : 0 < c) (hS : 0 ≤ S)
    (hSym : ∀ x ∈ unitBall n, (A x).toLinearMap.IsSymmetric)
    (hEll : ∀ x ∈ unitBall n, ∀ v : E n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {q : E n → ℝ} (hq : SmoothNear (closedUnitBall n) q)
    (hq0 : ∀ x ∈ unitSphere n, q x = 0)
    (hSource : ∀ x ∈ unitBall n,
      |dirichletBilinearContraction e[n] (A x) (realHessian q x)| ≤ S) :
    ∀ x ∈ unitBall n,
      |q x / dirichletBoundaryDistanceProxy x| ≤ S / (2 * n * c) := by
  have hUpper := dirichlet_le_source_boundary_barrier hn hc hS hSym hEll hq hq0
    (fun x hx => (abs_le.mp (hSource x hx)).1)
  let qNeg : E n → ℝ := (-1 : ℝ) • q
  have hqNeg : SmoothNear (closedUnitBall n) qNeg := by
    obtain ⟨U, hU, hSub, hqU⟩ := hq
    exact ⟨U, hU, hSub, hqU.const_smul (-1 : ℝ)⟩
  have hNegSource (x : E n) (hx : x ∈ unitBall n) :
      -S ≤ dirichletBilinearContraction e[n] (A x) (realHessian qNeg x) := by
    have hq2 : ContDiffAt ℝ 2 q x :=
      (hq.contDiffAt (ball_subset_closedBall hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    let F := dirichletHessianContractionLinearMap e[n] (A x)
    change -S ≤ F (realHessian ((-1 : ℝ) • q) x)
    rw [dirichlet_realHessian_smul_C2 hq2, map_smul, smul_eq_mul]
    have h := (abs_le.mp (hSource x hx)).2
    change dirichletBilinearContraction e[n] (A x) (realHessian q x) ≤ S at h
    change -S ≤ (-1 : ℝ) * dirichletBilinearContraction e[n] (A x) (realHessian q x)
    linarith only [h]
  have hLower := dirichlet_le_source_boundary_barrier hn hc hS hSym hEll hqNeg
    (fun x hx => by simp only [qNeg, Pi.smul_apply, smul_eq_mul, hq0 x hx, mul_zero])
    hNegSource
  intro x hx
  rw [abs_div, abs_of_pos (dirichletBoundaryDistanceProxy_pos hx)]
  apply (div_le_iff₀ (dirichletBoundaryDistanceProxy_pos hx)).mpr
  apply abs_le.mpr
  have hLo := hLower x (ball_subset_closedBall hx)
  have hHi := hUpper x (ball_subset_closedBall hx)
  change (-1 : ℝ) * q x ≤ _ at hLo
  constructor <;> linarith only [hLo, hHi]

end KEBall
