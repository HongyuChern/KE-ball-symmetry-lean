import KEBall.MoserTrudingerWeakGibbsSmooth

/-!
# Smooth representatives of weak Gibbs maximizers

The weak equation constrains the potential on the closed ball only.
Regularity therefore has to produce a smooth extension of that restriction;
it cannot constrain the previously arbitrary values outside the ball.
The original variational targets and the original conditional connector are
unchanged.  This module supplies the extension-invariant connector.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere

/-- Membership in the bounded Cegrell class depends on the restriction to
the open domain, including its interior boundary limits. -/
theorem IsE0.congr_of_eqOn {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} (hu : IsE0 Ω u) (he : EqOn u v Ω) :
    IsE0 Ω v := by
  have hp : PlurisubharmonicOn (fun x => (v x : EReal)) Ω := by
    intro x hx
    apply (hu.psh x hx).congr
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact congrArg (fun t : ℝ => (t : EReal)) (he hy)
  have hb : ∃ C : ℝ, ∀ x ∈ Ω, |v x| ≤ C := by
    obtain ⟨C, hC⟩ := hu.bounded
    exact ⟨C, fun x hx => (he hx) ▸ hC x hx⟩
  refine ⟨hp, hb, ?_, ?_⟩
  · intro z hz
    apply (hu.boundary z hz).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact he hx
  · have hv : IsLocallyBoundedPshOn Ω v := by
      refine ⟨hp, ?_⟩
      obtain ⟨C, hC⟩ := hb
      exact fun x hx => ⟨Ω, hx, le_rfl, C, hC⟩
    rw [← topMeasure_congr hu.locallyBoundedPsh hv he]
    exact hu.finiteMass

end KEBall.Cegrell

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

theorem finiteEnergyFunctional_congr_onBall (hn : 0 < n)
    {u v : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u)
    (hv : IsE1 (complexUnitBall n) v) (he : EqOn u v (complexUnitBall n))
    (γ : ℝ) : finiteEnergyFunctional γ hu = finiteEnergyFunctional γ hv := by
  have hW : finiteEnergyWeight u = finiteEnergyWeight v := by
    funext x
    unfold finiteEnergyWeight
    split_ifs with hx
    · have hz : complexCoordinates n x ∈ complexUnitBall n := by
        change x ∈ (complexCoordinates n) ⁻¹' (complexUnitBall n : Set (ComplexModel n))
        rwa [preimage_complexUnitBall]
      rw [he hz]
    · rfl
  have hI : exponentialIntegral γ u = exponentialIntegral γ v := by
    simp only [exponentialIntegral, hW]
  simp only [finiteEnergyFunctional, hI, energy_congr hn hu hv he]

/-- Changing only the exterior representative preserves the genuine weak
Bedford–Taylor equation and the boundary values. -/
theorem IsWeakGibbsSolution.congr_closedBall {γ : ℝ} {v w : E n → ℝ}
    (hv : IsWeakGibbsSolution n γ v) (he : EqOn v w (closedUnitBall n)) :
    IsWeakGibbsSolution n γ w := by
  have heC : EqOn (v ∘ (complexCoordinates n).symm)
      (w ∘ (complexCoordinates n).symm) (complexUnitBall n) := by
    intro z hz
    apply he
    apply ball_subset_closedBall
    exact mem_ball_zero_iff.mpr
      (((complexCoordinates n).symm.norm_map z).trans_lt (mem_ball_zero_iff.mp hz))
  have hwE := hv.memE0.congr_of_eqOn heC
  have hZ : normalizingIntegral γ v = normalizingIntegral γ w := by
    unfold normalizingIntegral
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    change Real.exp (-γ * v x) = Real.exp (-γ * w x)
    rw [he (ball_subset_closedBall hx)]
  refine ⟨hv.gamma_pos, hv.continuousOn.congr he.symm, ?_, hwE, ?_⟩
  · intro x hx
    rw [← he (sphere_subset_closedBall hx)]
    exact hv.zero_on_sphere x hx
  · rw [← topMeasure_congr hv.memE0.locallyBoundedPsh hwE.locallyBoundedPsh heC,
      hv.measure_eq]
    apply congrArg (Measure.map (complexCoordinates n))
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    simp only [gibbsDensity, hZ, he (ball_subset_closedBall hx)]

/-- Closed-ball regularity is used in its correct extension form.  The
comparison still ranges over the entire actual Cegrell finite-energy class. -/
theorem subcriticalSmoothAttainment_of_smoothGibbs_and_extension (hn : 2 ≤ n)
    (hSolve : ∀ (d : ℕ) (γ : ℝ), 1 < d → 0 < γ → γ < (d + 1 : ℝ) →
      SmoothGibbsDirichletSolvable d γ)
    (hRegular : ∀ {γ : ℝ} {v : E n → ℝ}, γ < (n + 1 : ℝ) →
      IsWeakGibbsSolution n γ v →
        ∃ w : E n → ℝ, EqOn v w (closedUnitBall n) ∧ SmoothNear (closedUnitBall n) w) :
    SubcriticalSmoothAttainment n := by
  intro γ hγ
  let β := (γ + (n + 1 : ℝ)) / 2
  have hγβ : γ < β := by dsimp [β]; linarith only [hγ.2]
  have hβn : β < (n + 1 : ℝ) := by dsimp [β]; linarith only [hγ.2]
  have hn₀ : 0 < n := by omega
  obtain ⟨C, hC⟩ := exists_finiteEnergyFunctional_bound_of_smoothGibbs hSolve n hn₀ β
    (hγ.1.trans hγβ) hβn
  obtain ⟨v, hv, hMax⟩ := exists_weakGibbs_maximizer_of_smoothGibbs hn₀ hγ.1 hγβ
    (fun hw => hC _ hw) (hSolve n γ (by omega) hγ.1 hγ.2)
  obtain ⟨w, he, hw⟩ := hRegular hγ.2 hv
  have hwG := hv.congr_closedBall he
  have hwS := hwG.isMeanFieldSolution_of_smoothNear hn₀ hw
  refine ⟨w, hwS, fun hu => (hMax hu).trans_eq ?_⟩
  apply finiteEnergyFunctional_congr_onBall hn₀
  intro z hz
  apply congrArg (fun t : ℝ => (t : EReal))
  apply he
  apply ball_subset_closedBall
  exact mem_ball_zero_iff.mpr
    (((complexCoordinates n).symm.norm_map z).trans_lt (mem_ball_zero_iff.mp hz))

end KEBall.MoserTrudinger
