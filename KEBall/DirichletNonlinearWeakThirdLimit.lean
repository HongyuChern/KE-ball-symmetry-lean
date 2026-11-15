import KEBall.DirichletUniformThirdEstimate
import KEBall.DirichletLipschitzHessian

/-! The bounded third derivatives have a weak limit on the unit ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Distributions Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem smooth_integral_test_realThirdDerivative {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (ψ : 𝓓B[n]) (a b c : E n) :
    (∫ x, ψ x * realThirdDerivative u x a b c ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x a * realHessian u x b c ∂ν[n]) := by
  obtain ⟨w, hw, hwu⟩ := MoserTrudinger.exists_global_contDiff_of_smoothNear hu
  let H (x : E n) := realHessian w x b c
  have hH : ContDiff ℝ ∞ H :=
    (((hw.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).clm_apply contDiff_const
  have h := integral_dirichletTest_fieldDerivative_mul_smooth hn ψ hH (contDiff_const (c := a))
  have hZero (x : E n) : dirichletVectorDivergence e[n] (fun _ => a) x = 0 := by
    simp [dirichletVectorDivergence]
  have hD (x : E n) : fderiv ℝ H x a = realThirdDerivative w x a b c :=
    fderiv_realHessian_apply hw.contDiffAt _ _ _
  simp only [hZero, mul_zero, add_zero, hD] at h
  have hLeft :
      (∫ x, ψ x * realThirdDerivative u x a b c ∂ν[n]) =
        ∫ x, ψ x * realThirdDerivative w x a b c ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have h₁ : fderiv ℝ w =ᶠ[𝓝 x] fderiv ℝ u := (hwu x (ball_subset_closedBall hx)).fderiv
    have h₂ : realHessian w =ᶠ[𝓝 x] realHessian u := h₁.fderiv
    have he := h₂.fderiv_eq (𝕜 := ℝ)
    change ψ x * realThirdDerivative u x a b c = ψ x * realThirdDerivative w x a b c
    rw [realThirdDerivative, realThirdDerivative, he]
  have hRight :
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x a * realHessian u x b c ∂ν[n]) =
        ∫ x, fderiv ℝ (ψ : E n → ℝ) x a * H x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have h₁ : fderiv ℝ w =ᶠ[𝓝 x] fderiv ℝ u := (hwu x (ball_subset_closedBall hx)).fderiv
    have he := h₁.fderiv_eq (𝕜 := ℝ)
    simp only [H, realHessian, he]
  rw [hLeft, hRight, h]
  simp

theorem memLp_continuousOn_dirichletBall {n : ℕ} (hn : 0 < n) {F : Type*}
    [NormedAddCommGroup F] {g : E n → F} (hG : ContinuousOn g (closedUnitBall n)) : MemLp g 2 ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hG
  have hMeas := (hG.mono ball_subset_closedBall).aestronglyMeasurable (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)
  exact MemLp.of_bound hMeas C ((ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)).mono
      fun x hx => hC x (ball_subset_closedBall hx))

private theorem realThirdDerivative_pairing_weakLimit {n : ℕ} (hn : 0 < n)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m)) {C : ℝ}
    (hBound : ∀ m, (∫ x, ∑ i, ∑ j, ∑ k,
      (realThirdDerivative (u m) x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ∂ν[n]) ≤ C)
    (i j k : Fin (2 * n)) :
    ∃ F : DirichletBallL2 n ℝ, ∀ ψ : 𝓓B[n], ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun m => ∫ x, ψ x * realThirdDerivative (u (φ m)) x (e[n] i) (e[n] j) (e[n] k)
        ∂ν[n]) atTop (𝓝 (∫ x, ψ x * F x ∂ν[n])) := by
  let g (m : ℕ) (x : E n) := realThirdDerivative (u m) x (e[n] i) (e[n] j) (e[n] k)
  have hgC (m : ℕ) (i j k : Fin (2 * n)) : ContinuousOn
      (fun x => realThirdDerivative (u m) x (e[n] i) (e[n] j) (e[n] k)) (closedUnitBall n) := by
    obtain ⟨U, hU, hSub, huU⟩ := hu m
    have h₁ := huU.fderiv_of_isOpen hU (m := ∞) (by simp)
    have h₂ := h₁.fderiv_of_isOpen hU (m := ∞) (by simp)
    have h₃ := h₂.fderiv_of_isOpen hU (m := ∞) (by simp)
    exact ((((h₃.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const).continuousOn).mono hSub
  have hg (m : ℕ) : MemLp (g m) 2 ν[n] := memLp_continuousOn_dirichletBall hn (hgC m i j k)
  let Q (m : ℕ) := (hg m).toLp (g m)
  have hNorm (m : ℕ) : ‖Q m‖ ≤ Real.sqrt C := by
    have he : ‖Q m‖ ^ 2 = ∫ x, (g m x) ^ 2 ∂ν[n] := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (hg m)] with x hx
      rw [hx, Real.inner_apply, pow_two]
    let p (x : E n) := ∑ a, ∑ b, ∑ c, (realThirdDerivative (u m) x (e[n] a) (e[n] b) (e[n] c)) ^ 2
    have hP : ContinuousOn p (closedUnitBall n) :=
      continuousOn_finsetSum Finset.univ fun a _ => continuousOn_finsetSum Finset.univ fun b _ =>
        continuousOn_finsetSum Finset.univ fun c _ => (hgC m a b c).pow 2
    have hI {w : E n → ℝ} (hw : ContinuousOn w (closedUnitBall n)) : Integrable w ν[n] :=
      hw.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
        ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
    have h₁ (x : E n) : (g m x) ^ 2 ≤ p x := by
      exact (Finset.single_le_sum (f := fun c => (realThirdDerivative (u m) x (e[n] i) (e[n] j) (e[n] c)) ^ 2)
        (fun c _ => sq_nonneg _) (Finset.mem_univ k)).trans
        ((Finset.single_le_sum (f := fun b => ∑ c, (realThirdDerivative (u m) x (e[n] i) (e[n] b) (e[n] c)) ^ 2)
          (fun b _ => Finset.sum_nonneg fun c _ => sq_nonneg _) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun a => ∑ b, ∑ c,
            (realThirdDerivative (u m) x (e[n] a) (e[n] b) (e[n] c)) ^ 2)
            (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => sq_nonneg _)
            (Finset.mem_univ i)))
    exact Real.le_sqrt_of_sq_le (he.trans_le ((integral_mono (hI ((hgC m i j k).pow 2)) (hI hP) h₁).trans
      (hBound m)))
  obtain ⟨F, hF⟩ := realHilbert_exists_weakClusterPoint_of_bound hNorm
  refine ⟨F, fun ψ => ?_⟩
  let Eψ : DirichletBallL2 n ℝ →L[ℝ] ℝ := innerSL ℝ (dirichletTestToL2 ψ)
  have hEψ : Continuous (fun z : WeakSpace ℝ (DirichletBallL2 n ℝ) =>
      Eψ ((toWeakSpace ℝ (DirichletBallL2 n ℝ)).symm z)) :=
    WeakBilin.eval_continuous (topDualPairing ℝ (DirichletBallL2 n ℝ)).flip Eψ
  have h₀ := MapClusterPt.continuousAt_comp (X := WeakSpace ℝ (DirichletBallL2 n ℝ))
    hEψ.continuousAt hF
  have he (w : DirichletBallL2 n ℝ) : Eψ w = ∫ x, ψ x * w x ∂ν[n] := by
    change inner ℝ (dirichletTestToL2 ψ) w = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae ψ] with x hx
    rw [hx, Real.inner_apply]
  have hQ (m : ℕ) : Eψ (Q m) = ∫ x, ψ x * g m x ∂ν[n] := by
    rw [he]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (hg m)] with x hx
    rw [hx]
  have h₁ : MapClusterPt (Eψ F) atTop (fun m => Eψ (Q m)) := by
    change MapClusterPt (Eψ ((toWeakSpace ℝ (DirichletBallL2 n ℝ)).symm
      (toWeakSpace ℝ (DirichletBallL2 n ℝ) F))) atTop
      (fun m => Eψ ((toWeakSpace ℝ (DirichletBallL2 n ℝ)).symm
        (toWeakSpace ℝ (DirichletBallL2 n ℝ) (Q m)))) at h₀
    simpa only [LinearEquiv.symm_apply_apply] using h₀
  obtain ⟨φ, hφ, hT⟩ := h₁.tendsto_subseq
  refine ⟨φ, hφ, ?_⟩
  change Tendsto (fun m => Eψ (Q (φ m))) atTop (𝓝 (Eψ F)) at hT
  simpa only [hQ, he, g] using hT


/-- A strong (L²) limit of the real Hessian entries of smooth potentials
has square-integrable weak derivatives whenever their third derivatives
are bounded uniformly. -/
theorem exists_weak_realThirdDerivative_of_tendsto_realHessian {n : ℕ} (hn : 0 < n)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m)) {C : ℝ}
    (hBound : ∀ m, (∫ x, ∑ i, ∑ j, ∑ k,
      (realThirdDerivative (u m) x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ∂ν[n]) ≤ C)
    (H : Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ)
    (Q : ℕ → Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ)
    (hH : ∀ j k, Tendsto (fun m => Q m j k) atTop (𝓝 (H j k)))
    (hQ : ∀ m j k, Q m j k =ᵐ[ν[n]] fun x => realHessian (u m) x (e[n] j) (e[n] k)) :
    ∃ F : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ,
      ∀ (i j k : Fin (2 * n)) (ψ : 𝓓B[n]),
        (∫ x, ψ x * F i j k x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] i) * H j k x ∂ν[n]) := by
  choose F hF using realThirdDerivative_pairing_weakLimit hn hu hBound
  refine ⟨F, fun i j k ψ => ?_⟩
  obtain ⟨φ, hφ, hSub⟩ := hF i j k ψ
  let χ := dirichletTestLineDerivative (e[n] i) ψ
  let Eχ : DirichletBallL2 n ℝ →L[ℝ] ℝ := innerSL ℝ (dirichletTestToL2 χ)
  have he (w : DirichletBallL2 n ℝ) :
      Eχ w = ∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] i) * w x ∂ν[n] := by
    change inner ℝ (dirichletTestToL2 χ) w = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletTestToL2_ae χ] with x hx
    rw [hx, Real.inner_apply]
    rfl
  have hLim : Tendsto (fun m => -(Eχ (Q (φ m) j k))) atTop
      (𝓝 (-(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] i) * H j k x ∂ν[n]))) := by
    rw [← he]
    exact (Eχ.continuous.continuousAt.tendsto.comp ((hH j k).comp hφ.tendsto_atTop)).neg
  have hEq (m : ℕ) :
      -(Eχ (Q (φ m) j k)) = ∫ x, ψ x * realThirdDerivative (u (φ m)) x (e[n] i) (e[n] j) (e[n] k)
        ∂ν[n] := by
    rw [he, smooth_integral_test_realThirdDerivative hn (hu (φ m)) ψ]
    congr 1
    apply integral_congr_ae
    filter_upwards [hQ (φ m) j k] with x hx
    rw [hx]
  exact tendsto_nhds_unique hSub (hLim.congr hEq)

end KEBall
