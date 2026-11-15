import KEBall.DirichletInwardJetConvergence

/-!
# Uniformly vanishing boundary pullback jets

A smooth map into the sphere is contracted inward before evaluating the
potential.  For a C2 zero-boundary potential, the resulting functions and
their first two ordinary derivatives tend uniformly to zero on compact
subsets of the domain of the sphere map.  In particular this applies to
radial projection on a closed annulus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

private theorem scaled_sphere_maps_closedBall {n : ℕ} {U : Set (E n)}
    {φ : E n → E n} (hMaps : MapsTo φ U (unitSphere n)) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    MapsTo (fun y => r • φ y) U (closedUnitBall n) := by
  intro x hx
  have hNorm : ‖φ x‖ = 1 := by
    simpa only [unitSphere, mem_sphere, dist_zero_right] using hMaps hx
  apply mem_closedBall_zero_iff.mpr
  rw [norm_smul, Real.norm_of_nonneg hr.1, hNorm, mul_one]
  exact hr.2

private theorem second_fderiv_const_smul_on_open {n : ℕ} {U : Set (E n)}
    (hU : IsOpen U) {φ : E n → E n} (hφ : ContDiffOn ℝ ∞ φ U)
    {x : E n} (hx : x ∈ U) (r : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => r • φ y)) x = r • fderiv ℝ (fderiv ℝ φ) x := by
  have he : fderiv ℝ (fun y => r • φ y) =ᶠ[𝓝 x] (fun y => r • fderiv ℝ φ y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (((hφ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.const_smul r).fderiv
  have hD := ((((hφ.fderiv_of_isOpen (m := 1) hU (by
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt.const_smul r).fderiv
  exact he.fderiv_eq.trans hD

theorem continuousOn_dirichlet_sphere_pullback_firstJet {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {U : Set (E n)} (hU : IsOpen U) {φ : E n → E n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hMaps : MapsTo φ U (unitSphere n)) :
    ContinuousOn (fun p : ℝ × E n => fderiv ℝ (fun y => u (p.1 • φ y)) p.2)
      (Icc (0 : ℝ) 1 ×ˢ U) := by
  let S := Icc (0 : ℝ) 1 ×ˢ U
  have hUnique : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hG := (hu.fderivWithin (m := 1) hUnique (by norm_num)).continuousOn
  have hρ : ContinuousOn (fun p : ℝ × E n => p.1 • φ p.2) S :=
    continuous_fst.continuousOn.smul
      (hφ.continuousOn.comp continuous_snd.continuousOn (fun _ hp => hp.2))
  have hρMaps : MapsTo (fun p : ℝ × E n => p.1 • φ p.2) S (closedUnitBall n) :=
    fun p hp => scaled_sphere_maps_closedBall hMaps hp.1 hp.2
  have hP : ContinuousOn (fun p : ℝ × E n => p.1 • fderiv ℝ φ p.2) S :=
    continuous_fst.continuousOn.smul
      (((hφ.fderiv_of_isOpen (m := 0) hU (by simp)).continuousOn).comp
        continuous_snd.continuousOn (fun _ hp => hp.2))
  apply ((hG.comp hρ hρMaps).clm_comp hP).congr
  intro p hp
  change fderiv ℝ (u ∘ (fun y => p.1 • φ y)) p.2 = _
  rw [fderiv_dirichlet_comp_closedBall (φ := fun y => p.1 • φ y)
    (hu.of_le (by norm_num)) hU
    ((hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).const_smul p.1)
    (scaled_sphere_maps_closedBall hMaps hp.1) hp.2]
  rw [show fderiv ℝ (fun y => p.1 • φ y) p.2 = p.1 • fderiv ℝ φ p.2 from
    (((hφ.contDiffAt (hU.mem_nhds hp.2)).differentiableAt (by simp)).hasFDerivAt.const_smul p.1).fderiv]
  rfl

theorem continuousOn_dirichlet_sphere_pullback_secondJet {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {U : Set (E n)} (hU : IsOpen U) {φ : E n → E n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hMaps : MapsTo φ U (unitSphere n)) :
    ContinuousOn (fun p : ℝ × E n => realHessian (fun y => u (p.1 • φ y)) p.2)
      (Icc (0 : ℝ) 1 ×ˢ U) := by
  let S := Icc (0 : ℝ) 1 ×ˢ U
  have hUnique : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hG := (hu.fderivWithin (m := 1) hUnique (by norm_num)).continuousOn
  have hB := ((hu.fderivWithin (m := 1) hUnique (by norm_num)).fderivWithin
    (m := 0) hUnique (by norm_num)).continuousOn
  have hρ : ContinuousOn (fun p : ℝ × E n => p.1 • φ p.2) S :=
    continuous_fst.continuousOn.smul
      (hφ.continuousOn.comp continuous_snd.continuousOn (fun _ hp => hp.2))
  have hρMaps : MapsTo (fun p : ℝ × E n => p.1 • φ p.2) S (closedUnitBall n) :=
    fun p hp => scaled_sphere_maps_closedBall hMaps hp.1 hp.2
  have hP : ContinuousOn (fun p : ℝ × E n => p.1 • fderiv ℝ φ p.2) S :=
    continuous_fst.continuousOn.smul
      (((hφ.fderiv_of_isOpen (m := 0) hU (by simp)).continuousOn).comp
        continuous_snd.continuousOn (fun _ hp => hp.2))
  have hQ : ContinuousOn (fun p : ℝ × E n => p.1 • fderiv ℝ (fderiv ℝ φ) p.2) S :=
    continuous_fst.continuousOn.smul
      ((((hφ.fderiv_of_isOpen (m := 1) hU (by
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).fderiv_of_isOpen
        (m := 0) hU (by norm_num)).continuousOn).comp
          continuous_snd.continuousOn (fun _ hp => hp.2))
  apply continuousOn_clm_apply.mpr
  intro v
  apply continuousOn_clm_apply.mpr
  intro z
  have hFirst := ((hB.comp hρ hρMaps).clm_apply
    (hP.clm_apply (continuousOn_const (c := v)))).clm_apply
    (hP.clm_apply (continuousOn_const (c := z)))
  have hSecond := (hG.comp hρ hρMaps).clm_apply
    ((hQ.clm_apply (continuousOn_const (c := v))).clm_apply (continuousOn_const (c := z)))
  apply (hFirst.add hSecond).congr
  intro p hp
  change realHessian (u ∘ (fun y => p.1 • φ y)) p.2 v z = _
  rw [realHessian_dirichlet_comp_closedBall (φ := fun y => p.1 • φ y) hu hU
    ((hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).const_smul p.1)
    (scaled_sphere_maps_closedBall hMaps hp.1) hp.2 v z,
    show fderiv ℝ (fun y => p.1 • φ y) p.2 = p.1 • fderiv ℝ φ p.2 from
      (((hφ.contDiffAt (hU.mem_nhds hp.2)).differentiableAt (by simp)).hasFDerivAt.const_smul p.1).fderiv,
    second_fderiv_const_smul_on_open hU hφ hp.2 p.1]
  rfl

theorem tendstoUniformlyOn_dirichlet_sphere_pullback_jets_zero {n : ℕ}
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    {U K : Set (E n)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {φ : E n → E n} (hφ : ContDiffOn ℝ ∞ φ U) (hMaps : MapsTo φ U (unitSphere n)) :
    TendstoUniformlyOn (fun r x => u (r • φ x)) (fun _ => 0)
        (𝓝[Icc (0 : ℝ) 1] 1) K ∧
    TendstoUniformlyOn (fun r => fderiv ℝ (fun y => u (r • φ y))) (fun _ => 0)
        (𝓝[Icc (0 : ℝ) 1] 1) K ∧
    TendstoUniformlyOn (fun r => realHessian (fun y => u (r • φ y))) (fun _ => 0)
        (𝓝[Icc (0 : ℝ) 1] 1) K := by
  have hρ : ContinuousOn (fun p : ℝ × E n => p.1 • φ p.2) (Icc (0 : ℝ) 1 ×ˢ U) :=
    continuous_fst.continuousOn.smul
      (hφ.continuousOn.comp continuous_snd.continuousOn (fun _ hp => hp.2))
  have hC := hu.continuousOn.comp hρ
    (fun p hp => scaled_sphere_maps_closedBall hMaps hp.1 hp.2)
  have hFirst := continuousOn_dirichlet_sphere_pullback_firstJet hu hU hφ hMaps
  have hSecond := continuousOn_dirichlet_sphere_pullback_secondJet hu hU hφ hMaps
  have hSub : Icc (0 : ℝ) 1 ×ˢ K ⊆ Icc (0 : ℝ) 1 ×ˢ U := prod_mono Subset.rfl hKU
  have hZero (x : E n) (hx : x ∈ K) :
      (fun y => u ((1 : ℝ) • φ y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds (hKU hx)] with y hy
    simpa only [one_smul] using hu0 (φ y) (hMaps hy)
  refine ⟨?_, ?_, ?_⟩
  · apply (dirichlet_uniform_limit_at_one_of_continuousOn_compact hK (hC.mono hSub)).congr_right
    intro x hx
    change u ((1 : ℝ) • φ x) = 0
    simpa only [one_smul] using hu0 (φ x) (hMaps (hKU hx))
  · apply (dirichlet_uniform_limit_at_one_of_continuousOn_compact hK (hFirst.mono hSub)).congr_right
    intro x hx
    change fderiv ℝ (fun y => u ((1 : ℝ) • φ y)) x = 0
    rw [(hZero x hx).fderiv_eq, fderiv_const_apply]
  · apply (dirichlet_uniform_limit_at_one_of_continuousOn_compact hK (hSecond.mono hSub)).congr_right
    intro x hx
    change realHessian (fun y => u ((1 : ℝ) • φ y)) x = 0
    rw [realHessian, (hZero x hx).fderiv.fderiv_eq]
    simp only [fderiv_fun_const, fderiv_zero, Pi.zero_apply]

end KEBall
