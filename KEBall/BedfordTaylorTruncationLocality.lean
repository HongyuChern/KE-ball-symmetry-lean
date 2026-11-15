import KEBall.BedfordTaylorMaxLocality
import KEBall.BedfordTaylorSmoothCriterion

/-!
# Locality of the bounded Monge–Ampère operator under truncation
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

theorem locallyBoundedPsh_const (c : ℝ) :
    IsLocallyBoundedPshOn Ω (fun _ => c) :=
  ⟨fun x _ => plurisubharmonicAt_const _ (by simp) x,
    fun _ hx => ⟨Ω, hx, le_rfl, |c|, fun _ _ => le_rfl⟩⟩

theorem locallyBoundedPsh_max_const (hu : IsLocallyBoundedPshOn Ω u) (c : ℝ) :
    IsLocallyBoundedPshOn Ω (fun x => max (u x) c) :=
  locallyBoundedPsh_max hu (locallyBoundedPsh_const c)

theorem locallyBoundedPsh_add_const (hu : IsLocallyBoundedPshOn Ω u) (c : ℝ) :
    IsLocallyBoundedPshOn Ω (fun x => u x + c) := by
  have hc : PlurisubharmonicOn (fun _ : ComplexModel n => (c : EReal)) Ω :=
    fun x _ => plurisubharmonicAt_const _ (by simp) x
  refine ⟨?_, ?_⟩
  · simpa only [EReal.coe_add] using hu.1.add hc
  · intro x hx
    obtain ⟨W, hxW, hWΩ, M, hM⟩ := hu.2 x hx
    exact ⟨W, hxW, hWΩ, M + |c|, fun y hy => (abs_add_le _ _).trans
      (add_le_add_left (hM y hy) _)⟩

theorem integral_weighted_topMeasure_truncation_eq (hu : IsLocallyBoundedPshOn Ω u)
    (c : ℝ) (φ : 𝓓(Ω, ℝ)) :
    (∫ x, φ x * (max (u x) c - c) ∂topMeasure hu) =
      ∫ x, φ x * (max (u x) c - c) ∂topMeasure (locallyBoundedPsh_max_const hu c) :=
  integral_weighted_topMeasure_max_eq hu (locallyBoundedPsh_const c) φ

theorem measurableSet_gt_on_domain (hu : IsLocallyBoundedPshOn Ω u) (c : ℝ) :
    MeasurableSet {x ∈ Ω | c < u x} :=
  measurableSet_lt_of_locallyBoundedPsh (locallyBoundedPsh_const c) hu

/-- The bounded Monge–Ampère measure is local on a Borel strict superlevel set. -/
theorem topMeasure_restrict_gt_truncation (hu : IsLocallyBoundedPshOn Ω u) (c : ℝ) :
    let G : Set (ComplexModel n) := {x ∈ Ω | c < u x}
    (topMeasure hu).restrict G = (topMeasure (locallyBoundedPsh_max_const hu c)).restrict G :=
  topMeasure_restrict_gt_max hu (locallyBoundedPsh_const c)

private theorem complexHessian_add_const (x : ComplexModel n) (c : ℝ) :
    PshLines.FirstPass.MongeAmpere.complexHessian (fun z => u z + c) x =
      PshLines.FirstPass.MongeAmpere.complexHessian u x := by
  have hd : fderiv ℝ (fun z => u z + c) = fderiv ℝ u :=
    funext fun _ => fderiv_add_const c
  ext j k : 1
  simp only [PshLines.FirstPass.MongeAmpere.complexHessian, PshLines.realHessian_eq_fderiv, hd]

private theorem smoothPsh_add_const (hu : IsSmoothPshOn Ω u) (c : ℝ) :
    IsSmoothPshOn Ω (fun x => u x + c) := by
  apply isSmoothPshOn_of_coordinateHessian (hu.1.add contDiffOn_const)
  intro x hx
  rw [complexHessian_add_const x c]
  exact hu.2.2 x hx

private theorem smoothMeasure_add_const (hu : IsSmoothPshOn Ω u) (c : ℝ) :
    smoothMeasure Ω (fun x => u x + c) (smoothPsh_add_const hu c) = smoothMeasure Ω u hu := by
  unfold smoothMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  rw [smoothDensity, smoothDensity,
    complexHessian_add_const x c]

/-- The Bedford–Taylor top measure is invariant under addition of a constant. -/
theorem topMeasure_add_const (hu : IsLocallyBoundedPshOn Ω u) (c : ℝ) :
    topMeasure (locallyBoundedPsh_add_const hu c) = topMeasure hu := by
  apply ambientMeasure_eq_of_smooth_test (topMeasure_compl _) (topMeasure_compl hu)
    (fun _ hK hKΩ => topMeasure_finite_on_compact _ hK hKΩ)
    (fun _ hK hKΩ => topMeasure_finite_on_compact hu hK hKΩ)
  intro φ
  obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let W : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hrel : RelativelyCompactIn W Ω := ⟨hVc, hVΩ⟩
  obtain ⟨p, hp⟩ := exists_decreasingMollifierApproximation hu hrel
  let hs := fun j => smoothPsh_add_const (hp.1 j) c
  have hanti (x : ComplexModel n) (hx : x ∈ W) : Antitone (fun j => p j x + c) :=
    fun _ _ hj => add_le_add_left (hp.2.1 x hx hj) _
  have hlim (x : ComplexModel n) (hx : x ∈ W) :
      Tendsto (fun j => p j x + c) atTop (𝓝 (u x + c)) := (hp.2.2 x hx).add_const c
  have h₁ := (isLocalBedfordTaylorMeasure_top (locallyBoundedPsh_add_const hu c)).2.2.2 W hrel
  have h₂ := (isLocalBedfordTaylorMeasure_top hu).2.2.2 W hrel
  have h₁' := h₁.2 (fun j x => p j x + c) ⟨hs, hanti, hlim⟩
    φ φ.continuous φ.hasCompactSupport hφV
  have h₂' := h₂.2 p hp φ φ.continuous φ.hasCompactSupport hφV
  exact tendsto_nhds_unique h₁' (h₂'.congr fun j => by
    rw [smoothMeasure_add_const (hp.1 j) c])

end KEBall.BedfordTaylor
