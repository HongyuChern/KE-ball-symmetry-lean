import KEBall.DirichletInteriorMaximum

/-!
# Compact-domain comparison with a bounded strict barrier

Unlike the zero-boundary special case, this version applies to annuli and
intersections of balls.  The barrier only needs a finite upper bound on
the frontier.  All second derivatives remain interior derivatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem dirichlet_le_frontier_of_linearHessian_nonneg_with_bounded_barrier {n : ℕ}
    {K : Set (E n)} (hK : IsCompact K)
    {w b : E n → ℝ} (hw : ContinuousOn w K) (hb : ContinuousOn b K)
    (hw2 : ContDiffOn ℝ 2 w (interior K))
    (hb2 : ContDiffOn ℝ 2 b (interior K))
    (F : E n → (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ interior K, ∀ D : E n →L[ℝ] E n →L[ℝ] ℝ,
      (∀ v : E n, D v v ≤ 0) → F x D ≤ 0)
    (hLw : ∀ x ∈ interior K, 0 ≤ F x (realHessian w x))
    (hLb : ∀ x ∈ interior K, 0 < F x (realHessian b x))
    {B : ℝ} (hB : ∀ x ∈ frontier K, b x ≤ B)
    {C : ℝ} (hC : ∀ x ∈ frontier K, w x ≤ C) :
    ∀ x ∈ K, w x ≤ C := by
  have hPerturb (ε : ℝ) (hε : 0 < ε) : ∀ x ∈ K, w x + ε * b x ≤ C + ε * B := by
    apply dirichlet_le_frontier_of_strict_linearHessian hK
      (hw.add (hb.const_smul ε)) (hw2.add (hb2.const_smul ε)) (fun x => F x) hF
    · intro x hx
      have hbx : ContDiffAt ℝ 2 b x := hb2.contDiffAt (isOpen_interior.mem_nhds hx)
      have hεb : ContDiffAt ℝ 2 (ε • b) x := hbx.const_smul ε
      rw [dirichlet_realHessian_add_C2 (v := ε • b)
        (hw2.contDiffAt (isOpen_interior.mem_nhds hx)) hεb,
        dirichlet_realHessian_smul_C2 hbx ε,
        map_add, map_smul, smul_eq_mul]
      exact add_pos_of_nonneg_of_pos (hLw x hx) (mul_pos hε (hLb x hx))
    · intro x hx
      exact add_le_add (hC x hx) (mul_le_mul_of_nonneg_left (hB x hx) hε.le)
  intro x hx
  have hT : Tendsto (fun ε : ℝ => C + ε * (B - b x)) (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    have h : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (h.mul_const (B - b x))
  apply ge_of_tendsto hT
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have h := hPerturb ε hε x hx
  linarith

theorem dirichlet_realHessian_sub_C2 {n : ℕ} {u v : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    realHessian (u - v) x = realHessian u x - realHessian v x := by
  have hNeg : -v = (-1 : ℝ) • v := by ext y; simp
  have hvNeg : ContDiffAt ℝ 2 ((-1 : ℝ) • v) x := by
    simpa only [Pi.smul_apply] using! hv.const_smul (-1 : ℝ)
  rw [sub_eq_add_neg, hNeg, dirichlet_realHessian_add_C2 (v := (-1 : ℝ) • v) hu hvNeg,
    dirichlet_realHessian_smul_C2 hv (-1), neg_one_smul, ← sub_eq_add_neg]

/-- Comparison for inhomogeneous equations: the full source inequality is
retained on the two sides before applying the homogeneous maximum principle. -/
theorem dirichlet_le_of_linearHessian_le_with_bounded_barrier {n : ℕ}
    {K : Set (E n)} (hK : IsCompact K)
    {u v b : E n → ℝ}
    (hu : ContinuousOn u K) (hv : ContinuousOn v K) (hb : ContinuousOn b K)
    (hu2 : ContDiffOn ℝ 2 u (interior K))
    (hv2 : ContDiffOn ℝ 2 v (interior K))
    (hb2 : ContDiffOn ℝ 2 b (interior K))
    (F : E n → (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ interior K, ∀ D : E n →L[ℝ] E n →L[ℝ] ℝ,
      (∀ a : E n, D a a ≤ 0) → F x D ≤ 0)
    (hL : ∀ x ∈ interior K, F x (realHessian v x) ≤ F x (realHessian u x))
    (hLb : ∀ x ∈ interior K, 0 < F x (realHessian b x))
    {B : ℝ} (hB : ∀ x ∈ frontier K, b x ≤ B)
    (hUV : ∀ x ∈ frontier K, u x ≤ v x) :
    ∀ x ∈ K, u x ≤ v x := by
  have h := dirichlet_le_frontier_of_linearHessian_nonneg_with_bounded_barrier
    hK (hu.sub hv) hb (hu2.sub hv2) hb2 F hF (fun x hx => ?_) hLb hB
    (C := 0) (fun x hx => sub_nonpos.mpr (hUV x hx))
  · intro x hx
    exact sub_nonpos.mp (h x hx)
  · rw [dirichlet_realHessian_sub_C2
      (hu2.contDiffAt (isOpen_interior.mem_nhds hx))
      (hv2.contDiffAt (isOpen_interior.mem_nhds hx)), (F x).map_sub]
    exact sub_nonneg.mpr (hL x hx)

end KEBall
