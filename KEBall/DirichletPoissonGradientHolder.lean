import KEBall.DirichletPoissonGradient

/-! Uniform first-derivative continuity from the actual Poisson equation.
The estimate uses the first derivative and the Laplacian, but no bound for
the full real Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

open Filter MeasureTheory Metric Set
open scoped ContDiff Laplacian NNReal Topology

noncomputable section

namespace KEBall

open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Analysis.Schauder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

theorem norm_fderiv_sub_le_sqrt_of_bounded_poisson_scale
    (u : BoundedContinuousFunction V ℝ)
    (du : BoundedContinuousFunction V (V →L[ℝ] ℝ))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : V → ℝ) (du x) x)
    (hdu : ∀ x, HasFDerivAt (du : V → V →L[ℝ] ℝ) (d2u x) x)
    {G L s : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) (hs : 0 < s)
    (hGrad : ‖du‖ ≤ G) (hLap : ‖coreLap d2u‖ ≤ L) (x y : V) :
    ‖fderiv ℝ (u : V → ℝ) x - fderiv ℝ (u : V → ℝ) y‖ ≤
      heatC1 V * (G / s + 4 * L * s) * Real.sqrt ‖x - y‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  let d : ℝ := ‖x - y‖
  let t : ℝ := s ^ 2 * d
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have ht : 0 < t := mul_pos (sq_pos_of_pos hs) hd
  have hScale : Real.sqrt t = s * Real.sqrt d := by
    dsimp only [t]
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  let B : ℝ≥0 := ⟨L, hL⟩
  let f : ℝ → BoundedContinuousFunction V ℝ := fun _ => coreLap d2u
  have hbound : ∀ s ∈ Icc (0 : ℝ) t, ‖f s‖ ≤ B := fun _ _ => hLap
  have hsource : ContinuousOn (fun p : ℝ × V => f p.1 p.2)
      (Ioo (0 : ℝ) t ×ˢ (univ : Set V)) :=
    ((coreLap d2u).continuous.comp continuous_snd).continuousOn
  have hm0 := fun z => heatSup_timeSource_aestronglyMeasurable_of_continuousOn
    ht.le f hsource z
  have hm1 := fun z => heatSupGradient_timeSource_aestronglyMeasurable_of_continuousOn
    ht.le f hsource z
  have hulip : LipschitzWith ‖du‖₊ (u : V → ℝ) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact fun z => (hu z).differentiableAt
    · intro z
      rw [(hu z).fderiv]
      exact_mod_cast du.norm_coe_le_norm z
  have huzero : HolderWith (2 * ‖u‖₊) 0 (u : V → ℝ) :=
    holderWith_zero_of_norm_le u.norm_coe_le_norm
  have huhalf : HolderWith (max (2 * ‖u‖₊) ‖du‖₊) (1 / 2 : ℝ≥0) (u : V → ℝ) :=
    huzero.of_le_of_le hulip.holderWith (by positivity) (by norm_num)
  have hrep : (u : V → ℝ) = (fun z => heatSup t u z) - heatDuhamel t f := by
    funext z
    rw [Pi.sub_apply, heatDuhamel_const_eq_integral_heatSup]
    rw [heatSup_primitive ht u du d2u hu hdu huhalf z]
    ring
  have hComm (z : V) : fderiv ℝ (fun y => heatSup t u y) z = heatSup t du z := by
    have hscaled := heatScaled_space t u du hu z
    have hfun : (fun y => heatSup t u y) = fun y => heatScaled t u y := by
      funext y
      exact heatSup_scaled ht u y
    rw [hfun, hscaled.fderiv, ← heatSup_scaled ht du z]
  have hder (z : V) : fderiv ℝ (u : V → ℝ) z =
      heatSup t du z - heatDuhamelGradientMap t f z := by
    have hd := (heatSup_hasFDerivAt ht u z).sub
      (heatDuhamel_hasFDerivAt ht f hbound hm0 hm1 z)
    rw [← hrep] at hd
    rw [hd.fderiv, ← (heatSup_hasFDerivAt ht u z).fderiv,
      hComm z]
  have hSmooth (z : V) : ‖fderiv ℝ (fun w => heatSup t du w) z‖ ≤
      (Real.sqrt t)⁻¹ * heatC1 V * G := by
    rw [(heatSup_hasFDerivAt ht du z).fderiv]
    exact (heatSupGradient_norm_le ht du z).trans
      (mul_le_mul_of_nonneg_left hGrad
        (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t)) (heatC1_nonneg (V := V))))
  have hDiff : ‖heatSup t du x - heatSup t du y‖ ≤
      ((Real.sqrt t)⁻¹ * heatC1 V * G) * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (heatSup_hasFDerivAt ht du z).differentiableAt)
      (fun z _ => hSmooth z) (convex_univ : Convex ℝ (univ : Set V))
      (mem_univ y) (mem_univ x)
  have hPot (z : V) : ‖heatDuhamelGradientMap t f z‖ ≤
      2 * L * heatC1 V * Real.sqrt t :=
    heatDuhamelGradientMap_norm_le ht f hbound z (hm1 z)
  rw [hder x, hder y]
  calc
    _ = ‖(heatSup t du x - heatSup t du y) +
        (heatDuhamelGradientMap t f y - heatDuhamelGradientMap t f x)‖ := by
      congr 1
      abel
    _ ≤ ‖heatSup t du x - heatSup t du y‖ +
        (‖heatDuhamelGradientMap t f y‖ + ‖heatDuhamelGradientMap t f x‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ ((Real.sqrt t)⁻¹ * heatC1 V * G) * d +
        (2 * L * heatC1 V * Real.sqrt t + 2 * L * heatC1 V * Real.sqrt t) :=
      add_le_add hDiff (add_le_add (hPot y) (hPot x))
    _ = heatC1 V * (G / s + 4 * L * s) * Real.sqrt d := by
      have hCancel : (Real.sqrt t)⁻¹ * d = Real.sqrt d / s := by
        calc
          _ = (d / Real.sqrt d) / s := by rw [hScale, mul_inv_rev]; ring
          _ = _ := by rw [Real.div_sqrt]
      calc
        _ = heatC1 V * G * ((Real.sqrt t)⁻¹ * d) +
            4 * L * heatC1 V * Real.sqrt t := by ring
        _ = _ := by rw [hCancel, hScale]; ring

theorem norm_fderiv_sub_le_sqrt_of_bounded_poisson
    (u : BoundedContinuousFunction V ℝ)
    (du : BoundedContinuousFunction V (V →L[ℝ] ℝ))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : V → ℝ) (du x) x)
    (hdu : ∀ x, HasFDerivAt (du : V → V →L[ℝ] ℝ) (d2u x) x)
    {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hGrad : ‖du‖ ≤ G) (hLap : ‖coreLap d2u‖ ≤ L) (x y : V) :
    ‖fderiv ℝ (u : V → ℝ) x - fderiv ℝ (u : V → ℝ) y‖ ≤
      heatC1 V * (G + 4 * L) * Real.sqrt ‖x - y‖ := by
  simpa only [div_one, mul_one] using
    norm_fderiv_sub_le_sqrt_of_bounded_poisson_scale u du d2u hu hdu
      hG hL (s := 1) zero_lt_one hGrad hLap x y

private def poissonHolderBoundedOfCompactSupport {W : Type*} [NormedAddCommGroup W]
    (f : V → W) (hf : Continuous f) (hc : HasCompactSupport f) :
    BoundedContinuousFunction V W :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hf
    (Classical.choose (hf.bounded_above_of_compact_support hc))
    (Classical.choose_spec (hf.bounded_above_of_compact_support hc))

theorem norm_fderiv_sub_le_sqrt_of_compactSupport_poisson_scale
    {u : V → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    {G L s : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) (hs : 0 < s)
    (hGrad : ∀ z, ‖fderiv ℝ u z‖ ≤ G) (hLap : ∀ z, ‖Δ u z‖ ≤ L) (x y : V) :
    ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤
      heatC1 V * (G / s + 4 * L * s) * Real.sqrt ‖x - y‖ := by
  have hu1 : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hu2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hu1.fderiv_right (by simp)
  let u0 := poissonHolderBoundedOfCompactSupport u hu.continuous hc
  let u1 := poissonHolderBoundedOfCompactSupport (fderiv ℝ u)
    hu1.continuous (hc.fderiv ℝ)
  let u2 := poissonHolderBoundedOfCompactSupport (fderiv ℝ (fderiv ℝ u))
    hu2.continuous ((hc.fderiv ℝ).fderiv ℝ)
  have hEq (z : V) : coreLap u2 z = Δ u z := by
    rw [coreLap_apply, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl
  exact norm_fderiv_sub_le_sqrt_of_bounded_poisson_scale u0 u1 u2
    (fun z => (hu.differentiable (by simp) z).hasFDerivAt)
    (fun z => (hu1.differentiable (by simp) z).hasFDerivAt)
    hG hL hs ((BoundedContinuousFunction.norm_le hG).mpr hGrad)
    ((BoundedContinuousFunction.norm_le hL).mpr (fun z => (hEq z).symm ▸ hLap z)) x y

theorem norm_fderiv_sub_le_sqrt_of_compactSupport_poisson
    {u : V → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hGrad : ∀ z, ‖fderiv ℝ u z‖ ≤ G) (hLap : ∀ z, ‖Δ u z‖ ≤ L) (x y : V) :
    ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤
      heatC1 V * (G + 4 * L) * Real.sqrt ‖x - y‖ := by
  simpa only [div_one, mul_one] using
    norm_fderiv_sub_le_sqrt_of_compactSupport_poisson_scale hu hc
      hG hL (s := 1) zero_lt_one hGrad hLap x y

end KEBall
