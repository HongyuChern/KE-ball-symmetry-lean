import KEBall.BedfordTaylorFiberCollarEnergy
import KEBall.BedfordTaylorFiberCurvatureApproximation

/-!
# Passing the fiber energy to the Bedford–Taylor limit on base tests
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Topology

namespace KEBall.BedfordTaylor

open MoserTrudinger
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsDecreasingApproximation IsLocallyBoundedPshOn
  IsSmoothPshOn isSmoothPshOn_of_psh)

theorem fiberEnergyCylinder_mono {n : ℕ} {R S ρ σ : ℝ} (hR : R ≤ S) (hρ : ρ ≤ σ) :
    fiberEnergyCylinder n R ρ ≤ fiberEnergyCylinder n S σ := fun _ hx =>
  mem_fiberEnergyCylinder.mpr ⟨(mem_fiberEnergyCylinder.mp hx).1.trans_le hR,
    (mem_fiberEnergyCylinder.mp hx).2.trans_le hρ⟩

theorem fiberEnergyCylinder_le_complexProductCylinder {n : ℕ} (R : ℝ) {ρ : ℝ}
    (hρ : ρ ≤ 1) : fiberEnergyCylinder n R ρ ≤ complexProductCylinder n 1 :=
  fun _ hx => mem_complexProductCylinder.mpr ((mem_fiberEnergyCylinder.mp hx).2.trans_le hρ)

/-- Signed energy of a locally bounded fiber, in the normalization of
the smooth fiber energy. It is extended by zero outside the base. -/
noncomputable def bedfordTaylorFiberEnergy {n : ℕ} {R ρ : ℝ} {p : ComplexModel (n + 1) → ℝ}
    (hp : IsLocallyBoundedPshOn (fiberEnergyCylinder n R ρ) p) (w : E 1) : ℝ :=
  if hw : ‖complexCoordinates 1 w‖ < ρ then
    (∫ z, complexFiberSlice p (complexCoordinates 1 w) z
      ∂topMeasure (locallyBoundedPsh_complexFiberSlice hp hw)) / (n + 1 : ℝ)
  else 0

set_option maxHeartbeats 900000 in
/-- The smooth fiber energies converge on integrable tests supported in
a smaller base ball. The collar bounds the vertical masses uniformly. -/
theorem tendsto_integral_fiberEnergy_mul_of_quadratic_collar {n : ℕ} (hn : 0 < n)
    {r ρ A D : ℝ} (hrρ : r < ρ) (hρ : ρ ≤ 1) (hA : 0 < A)
    {p : ComplexModel (n + 1) → ℝ} {q : ℕ → ComplexModel (n + 1) → ℝ}
    (hp : IsLocallyBoundedPshOn (complexProductCylinder n 1) p)
    (hApp : IsDecreasingApproximation (fiberEnergyCylinder n 3 ρ) p q)
    (hSmooth : ∀ j, ContDiff ℝ ∞ (q j))
    (hpEq : ∀ x ∈ fiberEnergyCylinder n 3 ρ, (3 / 2 : ℝ) < ‖(complexProductCoordinates n 1 x).1‖ →
      p x = A * ‖(complexProductCoordinates n 1 x).1‖ ^ 2 + D)
    {a d : ℕ → ℝ} (ha : ∀ j, 0 < a j ∧ a j ≤ A + 1)
    (haLim : Tendsto a atTop (𝓝 A)) (hdLim : Tendsto d atTop (𝓝 D))
    (hqEq : ∀ j x, x ∈ fiberEnergyCylinder n 3 ρ →
      (3 / 2 : ℝ) < ‖(complexProductCoordinates n 1 x).1‖ →
      q j x = a j * ‖(complexProductCoordinates n 1 x).1‖ ^ 2 + d j)
    {ψ : E 1 → ℝ} (hψ : Integrable ψ) (hψ0 : ∀ w, w ∉ ball (0 : E 1) r → ψ w = 0) :
    Integrable (fun w => bedfordTaylorFiberEnergy
      (IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)) w * ψ w) ∧
    Tendsto (fun j => ∫ w, fiberEnergy (q j ∘ fiberDilationCoordinates n 2) w * ψ w)
      atTop (𝓝 (∫ w, bedfordTaylorFiberEnergy
        (IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)) w * ψ w)) := by
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let W := fiberEnergyCylinder n 3 ρ
  let U := fiberEnergyCylinder n 2 ρ
  let B : Opens (ComplexModel n) := ballDomain 0 2
  let K := e ⁻¹' (closedBall 0 2 ×ˢ closedBall 0 r)
  have hK : IsCompact K := e.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hKW : K ⊆ W := fun _ hx =>
    mem_fiberEnergyCylinder.mpr ⟨(mem_closedBall_zero_iff.mp hx.1).trans_lt (by norm_num),
      (mem_closedBall_zero_iff.mp hx.2).trans_lt hrρ⟩
  let hpW := IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 3 hρ)
  let hpU := IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)
  let hqW (j : ℕ) := isLocallyBoundedPshOn_of_isSmoothPshOn (hApp.1 j)
  let hUW : U ≤ W := fiberEnergyCylinder_mono (by norm_num) le_rfl
  let hqU (j : ℕ) := IsLocallyBoundedPshOn.mono (hqW j) hUW
  obtain ⟨P, hP, hpBound⟩ := hpW.exists_compact_abs_bound hK hKW
  obtain ⟨Q, hQ, hqBound⟩ := exists_compact_abs_bound_of_antitone hpW hqW
    hApp.2.1 hApp.2.2 hK hKW
  let C := max P Q
  have hC : 0 ≤ C := hP.trans (le_max_left _ _)
  have hW' (w : E 1) (hw : w ∈ ball (0 : E 1) r) : ‖c w‖ < ρ :=
    (c.norm_map w).trans_lt ((mem_ball_zero_iff.mp hw).trans hrρ)
  have hBase (w : E 1) (hw : w ∈ ball (0 : E 1) r) : ‖c w‖ < 1 :=
    (hW' w hw).trans_le hρ
  have hFiberK (w : E 1) (hw : w ∈ ball (0 : E 1) r) (z : ComplexModel n)
      (hz : z ∈ ball (0 : ComplexModel n) 2) : e.symm (z, c w) ∈ K := by
    change e (e.symm (z, c w)) ∈ closedBall 0 2 ×ˢ closedBall 0 r
    rw [e.apply_symm_apply]
    refine ⟨ball_subset_closedBall hz, mem_closedBall_zero_iff.mpr ?_⟩
    rw [c.norm_map]
    exact (mem_ball_zero_iff.mp hw).le
  let hV (w : E 1) (hw : w ∈ ball (0 : E 1) r) := locallyBoundedPsh_complexFiberSlice hpU (hBase w hw)
  let hS (j : ℕ) (w : E 1) (hw : w ∈ ball (0 : E 1) r) :
      IsSmoothPshOn B (complexFiberSlice (q j) (c w)) :=
    isSmoothPshOn_of_psh (contDiff_complexFiberSlice (hSmooth j) (c w)).contDiffOn
      (locallyBoundedPsh_complexFiberSlice (hqU j) (hW' w hw)).1
  let hS' (j : ℕ) (w : E 1) (hw : w ∈ ball (0 : E 1) r) :=
    isLocallyBoundedPshOn_of_isSmoothPshOn (hS j w hw)
  have hPBound (w : E 1) (hw : w ∈ ball (0 : E 1) r) (z : ComplexModel n)
      (hz : z ∈ ball (0 : ComplexModel n) 2) : ‖complexFiberSlice p (c w) z‖ ≤ C :=
    (by simpa only [complexFiberSlice, Real.norm_eq_abs] using hpBound _ (hFiberK w hw z hz) :
      ‖complexFiberSlice p (c w) z‖ ≤ P).trans (le_max_left _ _)
  have hQBound (j : ℕ) (w : E 1) (hw : w ∈ ball (0 : E 1) r) (z : ComplexModel n)
      (hz : z ∈ ball (0 : ComplexModel n) 2) : ‖complexFiberSlice (q j) (c w) z‖ ≤ C :=
    (by simpa only [complexFiberSlice, Real.norm_eq_abs] using hqBound j _ (hFiberK w hw z hz) :
      ‖complexFiberSlice (q j) (c w) z‖ ≤ Q).trans (le_max_right _ _)
  have hPE (w : E 1) (hw : w ∈ ball (0 : E 1) r) (z : ComplexModel n)
      (hz : z ∈ ball (0 : ComplexModel n) 2) (hZ : (3 / 2 : ℝ) < ‖z‖) :
      complexFiberSlice p (c w) z = A * ‖z‖ ^ 2 + D := by
    have h := hpEq (e.symm (z, c w)) (hKW (hFiberK w hw z hz))
    rw [e.apply_symm_apply] at h
    exact h hZ
  have hQE (j : ℕ) (w : E 1) (hw : w ∈ ball (0 : E 1) r) (z : ComplexModel n)
      (hz : z ∈ ball (0 : ComplexModel n) 2) (hZ : (3 / 2 : ℝ) < ‖z‖) :
      complexFiberSlice (q j) (c w) z = a j * ‖z‖ ^ 2 + d j := by
    have h := hqEq j (e.symm (z, c w)) (hKW (hFiberK w hw z hz))
    rw [e.apply_symm_apply] at h
    exact h hZ
  let S := ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) *
    (volume : Measure (ComplexModel n)) (ball 0 2)
  let M := C * ((A + 1) ^ n * S.toReal) / (n + 1 : ℝ)
  have hPt (j : ℕ) (w : E 1) (hw : w ∈ ball (0 : E 1) r) :
      fiberEnergy (q j ∘ fiberDilationCoordinates n 2) w =
        (∫ z, complexFiberSlice (q j) (c w) z ∂topMeasure (hS' j w hw)) / (n + 1 : ℝ) :=
    fiberEnergy_fiberDilationCoordinates (hSmooth j) (by norm_num) w (hS j w hw)
  have hBnd (j : ℕ) (w : E 1) (hw : w ∈ ball (0 : E 1) r) :
      ‖fiberEnergy (q j ∘ fiberDilationCoordinates n 2) w‖ ≤ M := by
    have hMass := topMeasure_univ_eq_of_quadratic_collar (by norm_num : (3 / 2 : ℝ) < 2)
      (ha j).1 (hS' j w hw) (hQE j w hw)
    have hFin := topMeasure_univ_lt_top_of_quadratic_collar (by norm_num : (3 / 2 : ℝ) < 2)
      (ha j).1 (hS' j w hw) (hQE j w hw)
    let : IsFiniteMeasure (topMeasure (hS' j w hw)) := ⟨hFin⟩
    have hInt := norm_integral_le_of_norm_le_const ((ae_mem_domain_topMeasure (hS' j w hw)).mono
      (hQBound j w hw))
    rw [measureReal_def, hMass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (ha j).1.le _)] at hInt
    rw [hPt j w hw, norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ))]
    apply div_le_div_of_nonneg_right (hInt.trans ?_) (by positivity)
    have hpow := pow_le_pow_left₀ (ha j).1.le (ha j).2 n
    dsimp only [S]
    gcongr
  have hConv (w : E 1) (hw : w ∈ ball (0 : E 1) r) :
      Tendsto (fun j => fiberEnergy (q j ∘ fiberDilationCoordinates n 2) w) atTop
        (𝓝 (bedfordTaylorFiberEnergy hpU w)) := by
    simp only [hPt _ w hw, bedfordTaylorFiberEnergy,
      dif_pos (show ‖complexCoordinates 1 w‖ < 1 from hBase w hw)]
    have h := tendsto_integral_topMeasure_of_quadratic_collar (by norm_num : (3 / 2 : ℝ) < 2) hA
      (hV w hw) (fun j => hS' j w hw) (hPE w hw) (fun j => (ha j).1) haLim hdLim
      (fun j => hQE j w hw)
      (fun z hz => hApp.2.1 _ (hKW (hFiberK w hw z hz)))
      (fun z hz => hApp.2.2 _ (hKW (hFiberK w hw z hz)))
      (hPBound w hw) (fun j => hQBound j w hw)
    exact h.div_const (n + 1 : ℝ)
  let F (j : ℕ) (w : E 1) := fiberEnergy (q j ∘ fiberDilationCoordinates n 2) w * ψ w
  let G (w : E 1) := bedfordTaylorFiberEnergy hpU w * ψ w
  have hMeas (j : ℕ) : AEStronglyMeasurable (F j) volume :=
    (fiberEnergy_contDiff hn ((hSmooth j).comp
      (fiberDilationCoordinates n 2).contDiff)).continuous.aestronglyMeasurable.mul hψ.aestronglyMeasurable
  have hDom : Integrable (fun w => M * ‖ψ w‖) := hψ.norm.const_mul _
  have hBound (j : ℕ) (w : E 1) : ‖F j w‖ ≤ M * ‖ψ w‖ := by
    by_cases hw : w ∈ ball (0 : E 1) r
    · dsimp only [F]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hBnd j w hw) (norm_nonneg _)
    · simp only [F, hψ0 w hw, mul_zero, norm_zero, le_refl]
  have hTendsto (w : E 1) : Tendsto (fun j => F j w) atTop (𝓝 (G w)) := by
    by_cases hw : w ∈ ball (0 : E 1) r
    · exact (hConv w hw).mul_const (ψ w)
    · simp only [F, G, hψ0 w hw, mul_zero]
      exact tendsto_const_nhds
  have hGLim := aestronglyMeasurable_of_tendsto_ae atTop hMeas (Eventually.of_forall hTendsto)
  refine ⟨hDom.mono' hGLim (Eventually.of_forall fun w =>
    le_of_tendsto (hTendsto w).norm (Eventually.of_forall fun j => hBound j w)), ?_⟩
  exact tendsto_integral_of_dominated_convergence (fun w => M * ‖ψ w‖)
    hMeas hDom (fun j => Eventually.of_forall (hBound j)) (Eventually.of_forall hTendsto)

end KEBall.BedfordTaylor
