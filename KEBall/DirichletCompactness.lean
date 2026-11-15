import KEBall.DirichletInteriorHessian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Compactness from the Dirichlet Hessian bound

The real Hessian estimates control the operator norm, so the potentials
and their first derivatives admit a common uniformly convergent subsequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

/-- A bound on the real Hessian in every unit direction is also an
operator norm bound on the full symmetric bilinear Hessian. -/
theorem norm_realHessian_le_of_unit_test {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) {D : ℝ} (hD : 0 ≤ D)
    (hTest : ∀ v : E n, ‖v‖ = 1 → |realHessian u x v v| ≤ D) :
    ‖realHessian u x‖ ≤ D := by
  let B := realHessian u x
  have hDiag (v : E n) : |B v v| ≤ D * ‖v‖ ^ 2 := by
    by_cases hv : v = 0
    · simp [hv]
    let w := ‖v‖⁻¹ • v
    have hvp := norm_pos_iff.mpr hv
    have hw : ‖w‖ = 1 := by
      rw [show w = ‖v‖⁻¹ • v from rfl, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ hvp.ne']
    have hVec : ‖v‖ • w = v := by
      simp [w, smul_smul, mul_inv_cancel₀ hvp.ne']
    have hEq : B v v = ‖v‖ ^ 2 * B w w := by
      calc
        B v v = B (‖v‖ • w) (‖v‖ • w) := by rw [hVec]
        _ = _ := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
    rw [hEq, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hTest w hw) (sq_nonneg _)).trans_eq (mul_comm _ _)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hD
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hD
  intro w hw
  change ‖B v w‖ ≤ D
  have hSym : B w v = B v w := realHessian_symm hu w v
  have hPolar : 4 * B v w = B (v + w) (v + w) - B (v - w) (v - w) := by
    simp only [map_add, map_sub, add_apply, sub_apply, hSym]
    ring
  have hTri := abs_sub_le (B (v + w) (v + w)) 0 (B (v - w) (v - w))
  simp only [sub_zero, zero_sub, abs_neg] at hTri
  have hb := hTri.trans (add_le_add (hDiag (v + w)) (hDiag (v - w)))
  rw [← hPolar, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), ← mul_add,
    parallelogram_law_with_norm ℝ, hv, hw] at hb
  rw [Real.norm_eq_abs]
  linarith only [hb]

/-- The a priori real Hessian bound yields a uniform Lipschitz constant
for the derivative on the closed ball. -/
theorem lipschitzOnWith_fderiv_of_unit_hessian_bound {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) {D : ℝ≥0}
    (hBound : ∀ x ∈ closedUnitBall n, ∀ v : E n, ‖v‖ = 1 → |realHessian u x v v| ≤ D) :
    LipschitzOnWith D (fderiv ℝ u) (closedUnitBall n) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall (0 : E n) 1)
  · intro x hx
    exact ((hu.contDiffAt hx).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  · intro x hx
    have h := norm_realHessian_le_of_unit_test (hu.contDiffAt hx) D.coe_nonneg (hBound x hx)
    exact_mod_cast h

/-- Uniform closed-ball bounds through order two yield simultaneous
uniform convergence of a subsequence of potentials and derivatives. -/
theorem exists_subseq_dirichlet_C1_of_uniform_hessian {n : ℕ} {u : ℕ → E n → ℝ}
    (hu : ∀ j, SmoothNear (closedUnitBall n) (u j)) {R : ℝ} {K D : ℝ≥0}
    (hU : ∀ j x, x ∈ closedUnitBall n → ‖u j x‖ ≤ R)
    (hG : ∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ K)
    (hH : ∀ j x, x ∈ closedUnitBall n → ∀ v : E n, ‖v‖ = 1 → |realHessian (u j) x v v| ≤ D) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ), StrictMono φ ∧
      TendstoUniformlyOn (fun j => u (φ j)) w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith D G (closedUnitBall n) := by
  let S := ↥(closedUnitBall n)
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)
  let V := ℝ × (E n →L[ℝ] ℝ)
  let p (j : ℕ) : BoundedContinuousFunction S V := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (u j x, fderiv ℝ (u j) x), by
      apply Continuous.prodMk
      · apply continuous_iff_continuousAt.mpr
        intro x
        exact ((hu j).contDiffAt x.property).continuousAt.comp continuous_subtype_val.continuousAt
      · apply continuous_iff_continuousAt.mpr
        intro x
        exact (((hu j).contDiffAt x.property).fderiv_right (m := ∞) (by simp)).continuousAt.comp
          continuous_subtype_val.continuousAt⟩
  have hLipU (j : ℕ) : LipschitzOnWith K (u j) (closedUnitBall n) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall (0 : E n) 1)
    · intro x hx
      exact ((hu j).contDiffAt hx).differentiableAt (by simp)
    · intro x hx
      exact_mod_cast hG j x hx
  have hLipG (j : ℕ) : LipschitzOnWith D (fderiv ℝ (u j)) (closedUnitBall n) :=
    lipschitzOnWith_fderiv_of_unit_hessian_bound (hu j) (hH j)
  let C := closedBall (0 : V) (max R (K : ℝ))
  have hC : IsCompact C := isCompact_closedBall _ _
  have hPC (f : BoundedContinuousFunction S V) (x : S) (hf : f ∈ range p) : f x ∈ C := by
    obtain ⟨j, rfl⟩ := hf
    apply mem_closedBall_zero_iff.mpr
    change max ‖u j x‖ ‖fderiv ℝ (u j) x‖ ≤ max R (K : ℝ)
    exact max_le_max (hU j x x.property) (hG j x x.property)
  have hEqui : Equicontinuous (fun g : range p => (g.val : S → V)) := by
    let A := max (K : ℝ) (D : ℝ)
    apply Metric.equicontinuous_of_continuity_modulus (fun r => A * r)
    · have hc : ContinuousAt (fun r : ℝ => A * r) 0 := continuousAt_const.mul continuousAt_id
      simpa only [mul_zero] using hc.tendsto
    · intro x y g
      obtain ⟨j, hj⟩ := g.property
      change dist (g.val x) (g.val y) ≤ A * dist x y
      rw [← hj]
      change max (dist (u j x) (u j y)) (dist (fderiv ℝ (u j) x) (fderiv ℝ (u j) y)) ≤ _
      apply max_le
      · exact ((hLipU j).dist_le_mul x x.property y y.property).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
      · exact ((hLipG j).dist_le_mul x x.property y y.property).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)
  have hComp := BoundedContinuousFunction.arzela_ascoli C hC (range p) hPC hEqui
  obtain ⟨f, _, φ, hφ, hf⟩ := hComp.tendsto_subseq (fun j => subset_closure (mem_range_self j))
  have hUnif := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hf
  classical
  let W (x : E n) : V := if hx : x ∈ closedUnitBall n then f ⟨x, hx⟩ else 0
  have hW : TendstoUniformlyOn (fun j x => (u (φ j) x, fderiv ℝ (u (φ j)) x))
      W atTop (closedUnitBall n) := by
    rw [Metric.tendstoUniformlyOn_iff]
    rw [Metric.tendstoUniformly_iff] at hUnif
    intro ε hε
    filter_upwards [hUnif ε hε] with j hj x hx
    have hjx := hj ⟨x, hx⟩
    change dist (f ⟨x, hx⟩) (u (φ j) x, fderiv ℝ (u (φ j)) x) < ε at hjx
    simpa only [W, dif_pos hx] using hjx
  let w (x : E n) := (W x).1
  let G (x : E n) := (W x).2
  have hw : TendstoUniformlyOn (fun j => u (φ j)) w atTop (closedUnitBall n) := by
    rw [Metric.tendstoUniformlyOn_iff] at hW ⊢
    intro ε hε
    filter_upwards [hW ε hε] with j hj x hx
    exact (le_max_left _ _).trans_lt (hj x hx)
  have hG' : TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) := by
    rw [Metric.tendstoUniformlyOn_iff] at hW ⊢
    intro ε hε
    filter_upwards [hW ε hε] with j hj x hx
    exact (le_max_right _ _).trans_lt (hj x hx)
  refine ⟨φ, w, G, hφ, hw, hG', ?_, ?_⟩
  · intro x hx
    exact hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hG'.mono ball_subset_closedBall)
      (fun j y hy => (((hu (φ j)).contDiffAt (ball_subset_closedBall hy)).differentiableAt
        (by simp)).hasFDerivAt) (fun y hy => hw.tendsto_at (ball_subset_closedBall hy)) hx
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hG'.tendsto_at hx).dist (hG'.tendsto_at hy))
      (Eventually.of_forall fun j => (hLipG (φ j)).dist_le_mul x hx y hy)

end KEBall
