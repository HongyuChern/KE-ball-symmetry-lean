import KEBall.DirichletBoundaryCorrection
import KEBall.DirichletCompactComparison
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# C2 approximation preserving the zero sphere trace

A potential which is C2 on the closed ball and smooth in its interior is
approximated in its actual closed-ball jets by functions smooth near the
closed ball.  Every approximant has exactly zero sphere trace.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

noncomputable section

namespace KEBall

def dirichletZeroBoundaryApprox {n : ℕ} (b : ContDiffBump (0 : E n))
    (u : E n → ℝ) (r : ℝ) : E n → ℝ :=
  (fun x => u (r • x)) - dirichletBoundaryCorrection b u r

theorem smoothNear_dirichletZeroBoundaryApprox {n : ℕ}
    (b : ContDiffBump (0 : E n)) {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    SmoothNear (closedUnitBall n) (dirichletZeroBoundaryApprox b u r) := by
  obtain ⟨U, hU, hSub, hI⟩ := smoothNear_dirichlet_inward_dilation hu hr hr1
  exact ⟨U, hU, hSub, hI.sub (contDiff_dirichletBoundaryCorrection b hu hr hr1).contDiffOn⟩

theorem dirichletZeroBoundaryApprox_zero_on_sphere {n : ℕ}
    (b : ContDiffBump (0 : E n)) (hb : b.rOut ≤ 1) (u : E n → ℝ) (r : ℝ) :
    ∀ x ∈ unitSphere n, dirichletZeroBoundaryApprox b u r x = 0 := by
  intro x hx
  change u (r • x) - dirichletBoundaryCorrection b u r x = 0
  rw [dirichletBoundaryCorrection_eq_inward_on_sphere b hb u r hx, sub_self]

theorem tendstoUniformlyOn_dirichletZeroBoundaryApprox_jets {n : ℕ}
    (b : ContDiffBump (0 : E n)) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (hSmooth : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    TendstoUniformlyOn (dirichletZeroBoundaryApprox b u) u
        (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) ∧
    TendstoUniformlyOn (fun r => fderiv ℝ (dirichletZeroBoundaryApprox b u r))
        (fderivWithin ℝ u (closedUnitBall n))
        (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) ∧
    TendstoUniformlyOn (fun r => realHessian (dirichletZeroBoundaryApprox b u r))
        (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n))
        (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) := by
  have hF : 𝓝[Ioo (0 : ℝ) 1] 1 ≤ 𝓝[Icc (0 : ℝ) 1] 1 :=
    nhdsWithin_mono (1 : ℝ) Ioo_subset_Icc_self
  have hCorr := tendstoUniformlyOn_dirichletBoundaryCorrection_jets_zero b hu hu0
  have hC0 : TendstoUniformlyOn (dirichletBoundaryCorrection b u) (fun _ => 0)
      (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) := fun V hV => (hCorr.1 V hV).filter_mono hF
  have hC1 : TendstoUniformlyOn (fun r => fderiv ℝ (dirichletBoundaryCorrection b u r))
      (fun _ => 0) (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) :=
    fun V hV => (hCorr.2.1 V hV).filter_mono hF
  have hC2 : TendstoUniformlyOn (fun r => realHessian (dirichletBoundaryCorrection b u r))
      (fun _ => 0) (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) :=
    fun V hV => (hCorr.2.2 V hV).filter_mono hF
  have hValue : TendstoUniformlyOn (fun r x => u (r • x)) u
      (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) := by
    have h := tendstoUniformlyOn_dirichlet_weighted_dilation hu.continuousOn 0
    simpa only [pow_zero, one_smul] using
      (show TendstoUniformlyOn (fun r x => r ^ 0 • u (r • x)) u
        (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) from fun V hV => (h V hV).filter_mono hF)
  have hFirst := tendstoUniformlyOn_dirichlet_inward_firstJet (hu.of_le (by norm_num))
  have hSecond := tendstoUniformlyOn_dirichlet_inward_secondJet hu
  refine ⟨?_, ?_, ?_⟩
  · have h := hValue.sub hC0
    change TendstoUniformlyOn (dirichletZeroBoundaryApprox b u) (u - 0)
      (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) at h
    simpa only [sub_zero] using h
  · have h : TendstoUniformlyOn
        (fun r x => fderiv ℝ (fun y => u (r • y)) x -
          fderiv ℝ (dirichletBoundaryCorrection b u r) x)
        (fderivWithin ℝ u (closedUnitBall n))
        (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) := by
      have h := hFirst.sub hC1
      change TendstoUniformlyOn
        (fun r x => fderiv ℝ (fun y => u (r • y)) x -
          fderiv ℝ (dirichletBoundaryCorrection b u r) x)
        (fderivWithin ℝ u (closedUnitBall n) - 0)
        (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) at h
      simpa only [sub_zero] using h
    apply h.congr
    filter_upwards [self_mem_nhdsWithin] with r hr x hx
    have hI := (smoothNear_dirichlet_inward_dilation hSmooth hr.1 hr.2).contDiffAt hx
    have hC := (contDiff_dirichletBoundaryCorrection b hSmooth hr.1 hr.2).contDiffAt (x := x)
    exact (fderiv_sub (hI.differentiableAt (by simp)) (hC.differentiableAt (by simp))).symm
  · have h : TendstoUniformlyOn
        (fun r x => realHessian (fun y => u (r • y)) x -
          realHessian (dirichletBoundaryCorrection b u r) x)
        (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n))
        (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) := by
      have h := hSecond.sub hC2
      change TendstoUniformlyOn
        (fun r x => realHessian (fun y => u (r • y)) x -
          realHessian (dirichletBoundaryCorrection b u r) x)
        (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n) - 0)
        (𝓝[Ioo (0 : ℝ) 1] 1) (closedUnitBall n) at h
      simpa only [sub_zero] using h
    apply h.congr
    filter_upwards [self_mem_nhdsWithin] with r hr x hx
    have hI := (smoothNear_dirichlet_inward_dilation hSmooth hr.1 hr.2).contDiffAt hx
    have hC := (contDiff_dirichletBoundaryCorrection b hSmooth hr.1 hr.2).contDiffAt (x := x)
    exact (dirichlet_realHessian_sub_C2
      (hI.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hC.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).symm

theorem exists_dirichlet_zeroBoundary_smooth_C2_approximation {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (hSmooth : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    ∃ v : ℕ → E n → ℝ,
      (∀ j, SmoothNear (closedUnitBall n) (v j) ∧ ∀ x ∈ unitSphere n, v j x = 0) ∧
      TendstoUniformlyOn v u atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (v j))
        (fderivWithin ℝ u (closedUnitBall n)) atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => realHessian (v j))
        (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n))
        atTop (closedUnitBall n) := by
  let b : ContDiffBump (0 : E n) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let r (j : ℕ) : ℝ := 1 - (1 / 2) * (1 / ((j : ℝ) + 1))
  have hr (j : ℕ) : r j ∈ Ioo (0 : ℝ) 1 := by
    have hPos : 0 < (1 : ℝ) / ((j : ℝ) + 1) := by positivity
    have hLe : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [show 0 ≤ (j : ℝ) from Nat.cast_nonneg j])
    dsimp [r]
    constructor <;> nlinarith
  have hR : Tendsto r atTop (𝓝[Ioo (0 : ℝ) 1] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall hr⟩
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2))
    simpa only [mul_zero, sub_zero] using h
  have h := tendstoUniformlyOn_dirichletZeroBoundaryApprox_jets b hu hSmooth hu0
  refine ⟨fun j => dirichletZeroBoundaryApprox b u (r j), ?_,
    h.1.seq_tendstoUniformlyOn r hR, h.2.1.seq_tendstoUniformlyOn r hR,
    h.2.2.seq_tendstoUniformlyOn r hR⟩
  intro j
  exact ⟨smoothNear_dirichletZeroBoundaryApprox b hSmooth (hr j).1 (hr j).2,
    dirichletZeroBoundaryApprox_zero_on_sphere b (by norm_num [b]) u (r j)⟩

end KEBall
