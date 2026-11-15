import KEBall.DirichletNonlinearWeakThirdLimit

/-! Identification of the strong real Hessian limit by testing derivatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem exists_realHessian_L2_limit_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ H : Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ,
      ∃ Q : ℕ → Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ,
        (∀ i j, Tendsto (fun m => Q m i j) atTop (𝓝 (H i j))) ∧
        (∀ m i j, Q m i j =ᵐ[ν[n]] fun x => realHessian (u m) x (e[n] i) (e[n] j)) := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C, hC, hBound⟩ := exists_integral_sq_realHessian_sub_le_of_logDensityPath hn hg
  let F (m : ℕ) (i j : Fin (2 * n)) (x : E n) := realHessian (u m) x (e[n] i) (e[n] j)
  have hF (m : ℕ) (i j : Fin (2 * n)) : ContinuousOn (F m i j) (closedUnitBall n) :=
    fun x hx => (((realHessian_contDiffAt ((hu m).contDiffAt hx)).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).continuousAt.continuousWithinAt
  have hM (m : ℕ) (i j : Fin (2 * n)) : MemLp (F m i j) 2 ν[n] := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn (hF m i j)
    have hMeas := ((hF m i j).mono ball_subset_closedBall).aestronglyMeasurable (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)
    exact MemLp.of_bound hMeas B ((ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)).mono
        fun x hx => hB x (ball_subset_closedBall hx))
  let Q (m : ℕ) (i j : Fin (2 * n)) := (hM m i j).toLp _
  have hQ (m : ℕ) (i j : Fin (2 * n)) : Q m i j =ᵐ[ν[n]] F m i j := MemLp.coeFn_toLp (hM m i j)
  have hI {p : E n → ℝ} (hp : ContinuousOn p (closedUnitBall n)) : Integrable p ν[n] :=
    hp.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hPair (m k : ℕ) (i j : Fin (2 * n)) :
      ‖Q m i j - Q k i j‖ ^ 2 ≤ C * (t m - t k) ^ 2 := by
    have he : ‖Q m i j - Q k i j‖ ^ 2 =
        ∫ x, (F m i j x - F k i j x) ^ 2 ∂ν[n] := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (Q m i j) (Q k i j), hQ m i j, hQ k i j] with x h₁ h₂ h₃
      rw [h₁, Pi.sub_apply, h₂, h₃, Real.inner_apply, pow_two]
    let P (x : E n) := ∑ i, ∑ j, (F m i j x - F k i j x) ^ 2
    have hPC : ContinuousOn P (closedUnitBall n) := continuousOn_finsetSum Finset.univ fun i _ =>
      continuousOn_finsetSum Finset.univ fun j _ => ((hF m i j).sub (hF k i j)).pow 2
    have hPart (x : E n) : (F m i j x - F k i j x) ^ 2 ≤ P x :=
      (Finset.single_le_sum (f := fun l => (F m i l x - F k i l x) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun l => ∑ r, (F m l r x - F k l r x) ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    rw [he]
    have h := hBound (t k) (ht k) (t m) (ht m) (hu k) (hu m) (hu0 k) (hu0 m)
      (huP k) (huP m) (hEq k) (hEq m)
    exact (integral_mono (hI (((hF m i j).sub (hF k i j)).pow 2)) (hI hPC) hPart).trans
      (by simpa only [P, F, _root_.sub_apply] using h)
  have hCauchy (i j : Fin (2 * n)) : CauchySeq (fun m => Q m i j) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ := ε / (Real.sqrt C + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hT.cauchySeq) δ hδ
    refine ⟨N, fun m hm k hk => ?_⟩
    have hD := hN m hm k hk
    rw [Real.dist_eq] at hD
    rw [dist_eq_norm]
    have h := Real.le_sqrt_of_sq_le (hPair m k i j)
    rw [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs] at h
    apply h.trans_lt
    have hle : Real.sqrt C * |t m - t k| ≤ Real.sqrt C * δ :=
      mul_le_mul_of_nonneg_left hD.le (Real.sqrt_nonneg _)
    exact hle.trans_lt (by
      have hE : (Real.sqrt C + 1) * δ = ε := by dsimp only [δ]; field_simp
      nlinarith only [hE, hδ])
  choose H hH using fun i j => cauchySeq_tendsto_of_complete (hCauchy i j)
  exact ⟨H, Q, hH, hQ⟩


/-- The parameter-limit real Hessian has coordinate weak derivatives in
(L²), with the same strong (L²) representatives as the smooth sequence. -/
theorem exists_realHessian_L2_limit_and_weakThird_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1) (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ H : Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ,
      (∃ Q : ℕ → Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ,
        (∀ i j, Tendsto (fun m => Q m i j) atTop (𝓝 (H i j))) ∧
        (∀ m i j, Q m i j =ᵐ[ν[n]] fun x => realHessian (u m) x (e[n] i) (e[n] j))) ∧
      ∃ F : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → DirichletBallL2 n ℝ,
        ∀ (i j k : Fin (2 * n)) (ψ : 𝓓B[n]),
          (∫ x, ψ x * F i j k x ∂ν[n]) =
            -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] i) * H j k x ∂ν[n]) := by
  obtain ⟨H, Q, hH, hQ⟩ := exists_realHessian_L2_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  obtain ⟨C, _, hC⟩ := exists_integral_sq_realThirdDerivative_le_of_logDensityPath hn hg
  exact ⟨H, ⟨Q, hH, hQ⟩,
    exists_weak_realThirdDerivative_of_tendsto_realHessian hn hu
      (fun m => hC (t m) (ht m) (hu m) (hu0 m) (huP m) (hEq m)) H Q hH hQ⟩

end KEBall
