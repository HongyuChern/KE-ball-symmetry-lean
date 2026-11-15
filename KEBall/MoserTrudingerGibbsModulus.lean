import KEBall.UniformModulusCompactness
import KEBall.MoserTrudingerWeakGibbsPairs

/-! Uniform continuity of actual Gibbs inverse images from energy compactness
and the Dirichlet density stability theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}
local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)

/-- The images under the actual smooth Gibbs Dirichlet solve have a common
modulus whenever the inputs have common energy and pointwise amplitude bounds.
No gradient bound is assumed on either family. -/
theorem exists_uniform_modulus_of_smoothGibbsPairs (hn : 0 < n)
    {γ M B : ℝ} (hγ : 0 ≤ γ) {u v : ℕ → E n → ℝ}
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (hv : ∀ j, ContDiff ℝ ∞ (v j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (hv0 : ∀ j x, x ∈ unitSphere n → v j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hvP : ∀ j x, x ∈ unitBall n → (complexHessian (v j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (v j) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j, ∀ᵐ x ∂ν[n], u j x ∈ Icc (-B) 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℕ,
      ∀ x ∈ closedUnitBall n, ∀ y ∈ closedUnitBall n,
        dist x y < δ → dist (v j x) (v j y) < ε := by
  apply exists_uniform_modulus_of_subseq_uniform_limit (isCompact_closedBall _ _)
  intro i
  let e := complexCoordinates n
  let uNear (j : ℕ) : SmoothNear (closedUnitBall n) (u j) :=
    ⟨univ, isOpen_univ, subset_univ _, (hu j).contDiffOn⟩
  let vNear (j : ℕ) : SmoothNear (closedUnitBall n) (v j) :=
    ⟨univ, isOpen_univ, subset_univ _, (hv j).contDiffOn⟩
  have huE (j : ℕ) : IsE0 (complexUnitBall n) (u j ∘ e.symm) :=
    isE0_onBall_of_smooth_real_model (uNear j)
      (fun x hx => (huP j x hx).posSemidef) (hu0 j)
  have hMenn (j : ℕ) : energy (huE j).isE1 ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal (energy_lt_top hn (huE j).isE1).ne,
      energy_realModelPotential hn (uNear j) (huE j)]
    exact ENNReal.ofReal_le_ofReal (hM j)
  obtain ⟨p, hp, φ, hφ, _, _, hPL⟩ := exists_subseq_tendsto_of_energy_le hn
    (fun j => (huE (i j)).isE1) ENNReal.ofReal_lt_top (fun j => hMenn (i j))
  let a (j : ℕ) := u (i (φ j))
  let b (j : ℕ) := v (i (φ j))
  let w (x : E n) := (p (e x)).toReal
  have haL : ∀ᵐ x ∂ν[n], Tendsto (fun j => a j x) atTop (𝓝 (w x)) := by
    filter_upwards [ae_coordinates_of_ae_complexBall hPL,
      ae_coordinates_of_ae_complexBall (hp.ae_finite hn)] with x hx hFinite
    have h := (EReal.tendsto_toReal hFinite.1 hFinite.2).comp hx
    change Tendsto (fun j => ((u (i (φ j)) (e.symm (e x)) : ℝ) : EReal).toReal)
      atTop (𝓝 (w x)) at h
    simpa only [e.symm_apply_apply, EReal.toReal_coe, a] using h
  have haM (j : ℕ) : AEMeasurable (a j) ν[n] :=
    (hu (i (φ j))).continuous.measurable.aemeasurable
  have hwM : AEMeasurable w ν[n] := aemeasurable_of_tendsto_metrizable_ae' haM haL
  obtain ⟨_, _, hDB, hDL⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn hγ haM hwM
    (fun j => huB (i (φ j))) haL
  have hfC (j : ℕ) : ContinuousOn (gibbsDensity γ (a j)) (closedUnitBall n) :=
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hu (i (φ j))).continuous.continuousOn)).div_const _
  obtain ⟨r, hrU, hrC, _⟩ := exists_dirichletLimit_of_ae_of_bounded_density hn
    (u := b) (fun j => vNear (i (φ j))) hfC (gibbsDensity_aemeasurable hwM)
    (fun j => hv0 (i (φ j))) (fun j => hvP (i (φ j)))
    (fun j => hEq (i (φ j))) hDB hDL
  exact ⟨φ, hφ, r, hrC, hrU⟩

end KEBall.MoserTrudinger
