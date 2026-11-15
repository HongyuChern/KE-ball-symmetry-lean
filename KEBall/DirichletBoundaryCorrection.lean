import KEBall.DirichletParametricJets

/-!
# A boundary correction vanishing in C2

The fixed cutoff removes the singularity of radial projection at the
origin.  For inward parameters the correction is globally smooth; at
parameter one it is zero when the potential has zero sphere trace.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

noncomputable section

namespace KEBall

def dirichletBoundaryCorrection {n : ℕ} (b : ContDiffBump (0 : E n))
    (u : E n → ℝ) (r : ℝ) (x : E n) : ℝ :=
  (1 - b x) * u (r • dirichletRadialProjection x)

theorem dirichletBoundaryCorrection_eq_zero_near_origin {n : ℕ}
    (b : ContDiffBump (0 : E n)) (u : E n → ℝ) (r : ℝ) :
    dirichletBoundaryCorrection b u r =ᶠ[𝓝 (0 : E n)] (fun _ => 0) := by
  filter_upwards [b.eventuallyEq_one] with x hx
  change b x = 1 at hx
  simp only [dirichletBoundaryCorrection, hx, sub_self, zero_mul]

theorem contDiffOn_dirichletBoundaryCorrection_parameter {n : ℕ}
    (b : ContDiffBump (0 : E n)) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ContDiffOn ℝ 2 (fun p : ℝ × E n => dirichletBoundaryCorrection b u p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set (E n))) := by
  let U : Set (E n) := {0}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hP : ContDiffOn ℝ 2
      (fun p : ℝ × E n => dirichletBoundaryCorrection b u p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ U) := by
    have hProj : ContDiffOn ℝ 2 (fun p : ℝ × E n => dirichletRadialProjection p.2)
        (Icc (0 : ℝ) 1 ×ˢ U) :=
      (contDiffOn_dirichletRadialProjection.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp contDiffOn_snd
          (fun _ hp => hp.2)
    have hMaps : MapsTo (fun p : ℝ × E n => p.1 • dirichletRadialProjection p.2)
        (Icc (0 : ℝ) 1 ×ˢ U) (closedUnitBall n) := by
      intro p hp
      apply mem_closedBall_zero_iff.mpr
      rw [norm_smul, Real.norm_of_nonneg hp.1.1,
        norm_dirichletRadialProjection (by simpa only [U, mem_compl_iff, mem_singleton_iff] using hp.2), mul_one]
      exact hp.1.2
    exact (contDiffOn_const.sub (b.contDiff.contDiffOn.comp contDiffOn_snd
      (mapsTo_univ _ _))).mul (hu.comp (contDiffOn_fst.smul hProj) hMaps)
  intro p hp
  by_cases hx : p.2 = 0
  · have hb : ∀ᶠ q : ℝ × E n in 𝓝 p, b q.2 = 1 := by
      apply b.eventuallyEq_one.comp_tendsto
      rw [← hx]
      exact continuous_snd.continuousAt
    have he : (fun q : ℝ × E n => dirichletBoundaryCorrection b u q.1 q.2) =ᶠ[𝓝 p]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hb] with q hq
      simp only [dirichletBoundaryCorrection, hq, sub_self, zero_mul]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt
  · have hxU : p.2 ∈ U := by simpa only [U, mem_compl_iff, mem_singleton_iff] using hx
    apply (hP p ⟨hp.1, hxU⟩).mono_of_mem_nhdsWithin
    have hN : ∀ᶠ q : ℝ × E n in 𝓝 p, q.2 ∈ U :=
      continuous_snd.continuousAt (hU.mem_nhds hxU)
    filter_upwards [self_mem_nhdsWithin, hN.filter_mono nhdsWithin_le_nhds] with q hq hqU
    exact ⟨hq.1, hqU⟩

theorem contDiff_dirichletBoundaryCorrection {n : ℕ}
    (b : ContDiffBump (0 : E n)) {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContDiff ℝ ∞ (dirichletBoundaryCorrection b u r) := by
  let U : Set (E n) := {0}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hP : ContDiffOn ℝ ∞ (dirichletBoundaryCorrection b u r) U := by
    have hMaps : MapsTo (fun x : E n => r • dirichletRadialProjection x) U (unitBall n) := by
      intro x hx
      apply mem_ball_zero_iff.mpr
      rw [norm_smul, Real.norm_of_nonneg hr.le,
        norm_dirichletRadialProjection (by simpa only [U, mem_compl_iff, mem_singleton_iff] using hx), mul_one]
      exact hr1
    exact (contDiffOn_const.sub b.contDiff.contDiffOn).mul
      (hu.comp (contDiffOn_dirichletRadialProjection.const_smul r) hMaps)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq
      (dirichletBoundaryCorrection_eq_zero_near_origin b u r)
  · exact hP.contDiffAt (hU.mem_nhds (by simpa only [U, mem_compl_iff, mem_singleton_iff] using hx))

theorem dirichletBoundaryCorrection_eq_inward_on_sphere {n : ℕ}
    (b : ContDiffBump (0 : E n)) (hb : b.rOut ≤ 1) (u : E n → ℝ) (r : ℝ)
    {x : E n} (hx : x ∈ unitSphere n) :
    dirichletBoundaryCorrection b u r x = u (r • x) := by
  have hn : ‖x‖ = 1 := by simpa only [unitSphere, mem_sphere, dist_zero_right] using hx
  have hxB : b x = 0 := b.zero_of_le_dist (by simpa only [dist_zero_right, hn] using hb)
  simp only [dirichletBoundaryCorrection, hxB, sub_zero, one_mul,
    dirichletRadialProjection, hn, inv_one, one_smul]

theorem dirichletBoundaryCorrection_one_eq_zero {n : ℕ}
    (b : ContDiffBump (0 : E n)) {u : E n → ℝ}
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    dirichletBoundaryCorrection b u 1 = (fun _ => 0) := by
  funext x
  by_cases hx : x = 0
  · subst x
    have hb : b (0 : E n) = 1 := b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)
    simp only [dirichletBoundaryCorrection, hb, sub_self, zero_mul]
  · have hp : dirichletRadialProjection x ∈ unitSphere n := by
      change dirichletRadialProjection x ∈ sphere (0 : E n) 1
      simpa only [mem_sphere, dist_zero_right] using norm_dirichletRadialProjection hx
    simp only [dirichletBoundaryCorrection, one_smul, hu0 _ hp, mul_zero]

theorem tendstoUniformlyOn_dirichletBoundaryCorrection_jets_zero {n : ℕ}
    (b : ContDiffBump (0 : E n)) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0) :
    TendstoUniformlyOn (dirichletBoundaryCorrection b u) (fun _ => 0)
        (𝓝[Icc (0 : ℝ) 1] 1) (closedUnitBall n) ∧
    TendstoUniformlyOn (fun r => fderiv ℝ (dirichletBoundaryCorrection b u r)) (fun _ => 0)
        (𝓝[Icc (0 : ℝ) 1] 1) (closedUnitBall n) ∧
    TendstoUniformlyOn (fun r => realHessian (dirichletBoundaryCorrection b u r)) (fun _ => 0)
        (𝓝[Icc (0 : ℝ) 1] 1) (closedUnitBall n) := by
  have hC := contDiffOn_dirichletBoundaryCorrection_parameter b hu
  have hJ := continuousOn_dirichlet_parameter_spatial_jets isOpen_univ hC
  have hSub : Icc (0 : ℝ) 1 ×ˢ closedUnitBall n ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set (E n)) :=
    prod_mono Subset.rfl (subset_univ _)
  have hK : IsCompact (closedUnitBall n) := isCompact_closedBall _ _
  have hZero := dirichletBoundaryCorrection_one_eq_zero b hu0
  refine ⟨?_, ?_, ?_⟩
  · apply (dirichlet_uniform_limit_at_one_of_continuousOn_compact hK
      (hC.continuousOn.mono hSub)).congr_right
    intro x _
    exact congrFun hZero x
  · apply (dirichlet_uniform_limit_at_one_of_continuousOn_compact hK (hJ.1.mono hSub)).congr_right
    intro x _
    change fderiv ℝ (dirichletBoundaryCorrection b u 1) x = 0
    rw [hZero, fderiv_const_apply]
  · apply (dirichlet_uniform_limit_at_one_of_continuousOn_compact hK (hJ.2.mono hSub)).congr_right
    intro x _
    change realHessian (dirichletBoundaryCorrection b u 1) x = 0
    simp only [hZero, realHessian, fderiv_fun_const, fderiv_zero, Pi.zero_apply]

end KEBall
