import KEBall.DirichletRealHessianStability
import KEBall.DirichletUnitaryHessian
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Uniform integrated estimates for rotations of smooth Dirichlet solutions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

private theorem SmoothNear.comp_dirichletOrthogonalFlow {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (R : E n →L[ℝ] E n) (hR : star R = -R) (t : ℝ) :
    SmoothNear (closedUnitBall n) (u ∘ orthogonalFlow R hR t) := by
  obtain ⟨U, hU, hSub, huU⟩ := hu
  let Q := orthogonalFlow R hR t
  refine ⟨Q ⁻¹' U, hU.preimage Q.continuous, ?_, ?_⟩
  · intro x hx
    exact hSub (orthogonalFlow_mapsTo_closedUnitBall R hR t hx)
  · exact huU.comp Q.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)

/-- A uniform bound on the real Hessian, the density and its first derivative
controls the squared (L²) real Hessian difference under unitary rotations. -/
theorem exists_integral_sq_realHessian_sub_le_of_orthogonalFlow {n : ℕ} (hn : 0 < n)
    {a b D L : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (hL : 0 ≤ L) :
    ∃ C ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian u x w w| ≤ D) →
      ∀ (R : E n →L[ℝ] E n) (hR : star R = -R), (∀ x, R (J x) = J (R x)) → ∀ t : ℝ,
      (∫ x in unitBall n, ∑ i, ∑ j,
        ((realHessian (u ∘ orthogonalFlow R hR t) x - realHessian u x) (e[n] i) (e[n] j)) ^ 2
          ∂volume0 n) ≤ C * ‖R‖ ^ 2 * t ^ 2 := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨K, hK, hStab⟩ := exists_integral_sq_complexHessian_sub_le_of_dirichlet_data hn ha hb hD
  refine ⟨(16 * n : ℝ) * K * L ^ 2, by positivity, ?_⟩
  intro u f hu hf hu0 huP huEq hDen hGrad hBound R hR hJ t
  let Q := orthogonalFlow R hR t
  have hQBall : MapsTo Q (unitBall n) (unitBall n) := by
    intro x hx
    simpa only [unitBall, mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hQClosed := orthogonalFlow_mapsTo_closedUnitBall R hR t
  have hv : SmoothNear (closedUnitBall n) (u ∘ Q) := hu.comp_dirichletOrthogonalFlow R hR t
  have hg : SmoothNear (closedUnitBall n) (f ∘ Q) := hf.comp_dirichletOrthogonalFlow R hR t
  have hv0 (x : E n) (hx : x ∈ unitSphere n) : (u ∘ Q) x = 0 :=
    hu0 (Q x) (orthogonalFlow_mapsTo_unitSphere R hR t hx)
  have hCov (x : E n) (hx : x ∈ unitBall n) :=
    complexHessian_posDef_and_det_comp_unitary Q (orthogonalFlow_apply_J R hR hJ t)
      ((hu.contDiffAt (ball_subset_closedBall (hQBall hx))).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hvP (x : E n) (hx : x ∈ unitBall n) : (complexHessian (u ∘ Q) x).PosDef :=
    (hCov x hx).1.mpr (huP (Q x) (hQBall hx))
  have hvEq (x : E n) (hx : x ∈ unitBall n) :
      (complexHessian (u ∘ Q) x).det.re = (f ∘ Q) x :=
    (congrArg Complex.re (hCov x hx).2).trans (huEq (Q x) (hQBall hx))
  have hBound' (x : E n) (hx : x ∈ closedUnitBall n) (w : E n) (hw : ‖w‖ = 1) :
      |realHessian (u ∘ Q) x w w| ≤ D := by
    rw [realHessian_comp_linearIsometryEquiv]
    exact hBound (Q x) (hQClosed hx) (Q w) (by rwa [LinearIsometryEquiv.norm_map])
  have h := hStab hu hv hf hg hu0 hv0 huP hvP huEq hvEq hDen
    (fun x hx => hDen (Q x) (hQBall hx)) hBound hBound'
  let μ := (volume0 n).restrict (unitBall n)
  have hfC : ContinuousOn f (closedUnitBall n) :=
    fun x hx => (hf.contDiffAt hx).continuousAt.continuousWithinAt
  have hgC : ContinuousOn (f ∘ Q) (closedUnitBall n) := hfC.comp Q.continuous.continuousOn hQClosed
  have hIntegrable : Integrable (fun x => ((f ∘ Q) x - f x) ^ 2) μ := by
    have hC : ContinuousOn (fun x => ((f ∘ Q) x - f x) ^ 2) (closedUnitBall n) := (hgC.sub hfC).pow 2
    exact hC.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hDensity (x : E n) (hx : x ∈ unitBall n) : ‖f (Q x) - f x‖ ≤ L * (‖R‖ * |t|) := by
    have hx' := ball_subset_closedBall hx
    have hd := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun y hy => (hf.contDiffAt hy).differentiableAt (by simp)) hGrad
      (convex_closedBall (0 : E n) 1) hx' (hQClosed hx')
    refine hd.trans (mul_le_mul_of_nonneg_left ?_ hL)
    let A := Q.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E n)
    change ‖A x‖ ≤ ‖R‖ * |t|
    exact (A.le_opNorm x).trans ((mul_le_mul_of_nonneg_right
      (norm_orthogonalFlow_sub_id_le R hR t) (norm_nonneg _)).trans
        (mul_le_of_le_one_right (by positivity) (mem_ball_zero_iff.mp hx).le))
  have hPoint : (fun x => ((f ∘ Q) x - f x) ^ 2) ≤ᵐ[μ] fun _ => L ^ 2 * ‖R‖ ^ 2 * t ^ 2 := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have he := pow_le_pow_left₀ (norm_nonneg _) (hDensity x hx) 2
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow, ← mul_assoc, Function.comp_apply] using he
  have hInt := integral_mono_ae hIntegrable (integrable_const (L ^ 2 * ‖R‖ ^ 2 * t ^ 2)) hPoint
  rw [integral_const, probReal_univ, one_smul] at hInt
  refine (integral_sq_realHessian_sub_le_complex hn hu hv hu0 hv0).trans ?_
  exact (mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hInt hK))
    (by positivity)).trans_eq (by ring)

private theorem hasDerivAt_rotated_realHessian {n : ℕ}
    {u : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ ∞ u x)
    (R : E n →L[ℝ] E n) (hR : star R = -R) (a b : E n) :
    HasDerivAt (fun t => realHessian (u ∘ orthogonalFlow R hR t) x a b)
      (realThirdDerivative u x (R x) a b + realHessian u x (R a) b +
        realHessian u x a (R b)) 0 := by
  simp_rw [realHessian_comp_linearIsometryEquiv]
  have hd := (realHessian_contDiffAt hu).differentiableAt (by simp)
  have hh : HasFDerivAt (realHessian u) (fderiv ℝ (realHessian u) x) (orthogonalFlow R hR 0 x) := by
    rw [orthogonalFlow_zero_apply]
    exact hd.hasFDerivAt
  let Q (z : E n) : ℝ → E n := fun t => orthogonalFlow R hR t z
  have hQ (z : E n) : HasDerivAt (Q z) (R z) 0 := hasDerivAt_orthogonalFlow_apply_zero R hR z
  have h₁ : HasDerivAt (fun t : ℝ => realHessian u (orthogonalFlow R hR t x))
      (realThirdDerivative u x (R x)) 0 := by
    change HasFDerivAt (realHessian u) (fderiv ℝ (realHessian u) x) (Q x 0) at hh
    have hc := HasFDerivAt.comp_hasDerivAt (F := E n) (E := E n →L[ℝ] E n →L[ℝ] ℝ) (f := Q x) (0 : ℝ) hh (hQ x)
    exact hc
  have h₂ := (h₁.clm_apply (hasDerivAt_orthogonalFlow_apply_zero R hR a)).clm_apply
    (hasDerivAt_orthogonalFlow_apply_zero R hR b)
  simpa only [orthogonalFlow_zero_apply, _root_.add_apply, realThirdDerivative] using h₂

/-- For a smooth uniformly elliptic solution, the Hessian of its derivative
along any skew-Hermitian rotation has a uniform square integral. -/
theorem exists_integral_sq_realHessian_angularDerivative_le {n : ℕ} (hn : 0 < n)
    {a b D L : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (hL : 0 ≤ L) :
    ∃ C ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian u x w w| ≤ D) →
      ∀ (R : E n →L[ℝ] E n), star R = -R → (∀ x, R (J x) = J (R x)) →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (realHessian (fun y => fderiv ℝ u y (R y)) x (e[n] i) (e[n] j)) ^ 2
          ∂volume0 n) ≤ C * ‖R‖ ^ 2 := by
  obtain ⟨C, hC, hStab⟩ := exists_integral_sq_realHessian_sub_le_of_orthogonalFlow hn ha hb hD hL
  refine ⟨C, hC, ?_⟩
  intro u f hu hf hu0 huP huEq hDen hGrad hBound R hR hJ
  let μ := (volume0 n).restrict (unitBall n)
  let t (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  let v (s : ℝ) := u ∘ orthogonalFlow R hR s
  let w (x : E n) := fderiv ℝ u x (R x)
  let p (m : ℕ) (x : E n) := ∑ i, ∑ j,
    ((t m)⁻¹ * (realHessian (v (t m)) x (e[n] i) (e[n] j) -
      realHessian u x (e[n] i) (e[n] j))) ^ 2
  let q (x : E n) := ∑ i, ∑ j, (realHessian w x (e[n] i) (e[n] j)) ^ 2
  have ht (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  have htLim : Tendsto t atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => (ht m).ne'⟩
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hu : SmoothNear (closedUnitBall n) u := ⟨U, hU, hSub, huU⟩
  have hw : SmoothNear (closedUnitBall n) w :=
    ⟨U, hU, hSub, (huU.fderiv_of_isOpen hU (by simp)).clm_apply R.contDiff.contDiffOn⟩
  have hEntry {F : E n → ℝ} (hF : SmoothNear (closedUnitBall n) F) (i j : Fin (2 * n)) :
      ContinuousOn (fun x => realHessian F x (e[n] i) (e[n] j)) (closedUnitBall n) :=
    fun x hx => (((realHessian_contDiffAt (hF.contDiffAt hx)).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).continuousAt.continuousWithinAt
  have hPC (m : ℕ) : ContinuousOn (p m) (closedUnitBall n) := by
    have hV : SmoothNear (closedUnitBall n) (v (t m)) := hu.comp_dirichletOrthogonalFlow R hR (t m)
    exact continuousOn_finsetSum Finset.univ fun i _ => continuousOn_finsetSum Finset.univ fun j _ =>
      (continuousOn_const.mul ((hEntry hV i j).sub (hEntry hu i j))).pow 2
  have hQC : ContinuousOn q (closedUnitBall n) := continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_finsetSum Finset.univ fun j _ => (hEntry hw i j).pow 2
  have hI {F : E n → ℝ} (hF : ContinuousOn F (closedUnitBall n)) : Integrable F μ :=
    hF.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hBound' (m : ℕ) : (∫ x, p m x ∂μ) ≤ C * ‖R‖ ^ 2 := by
    have hStab' := hStab hu hf hu0 huP huEq hDen hGrad hBound R hR hJ (t m)
    have he :
        (∫ x, p m x ∂μ) = (t m)⁻¹ ^ 2 *
          ∫ x, ∑ i, ∑ j, ((realHessian (v (t m)) x - realHessian u x) (e[n] i) (e[n] j)) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [p, mul_pow, Finset.mul_sum, _root_.sub_apply]
    rw [he]
    refine (mul_le_mul_of_nonneg_left hStab' (sq_nonneg _)).trans_eq ?_
    rw [← mul_assoc, mul_comm ((t m)⁻¹ ^ 2), mul_assoc, ← mul_pow, inv_mul_cancel₀ (ht m).ne',
      one_pow, mul_one]
  have hLimit (x : E n) (hx : x ∈ unitBall n) : Tendsto (fun m => p m x) atTop (𝓝 (q x)) := by
    have hxU := hSub (ball_subset_closedBall hx)
    have hxAt := huU.contDiffAt (hU.mem_nhds hxU)
    have he (i j : Fin (2 * n)) :
        Tendsto (fun m => (t m)⁻¹ * (realHessian (v (t m)) x (e[n] i) (e[n] j) -
          realHessian u x (e[n] i) (e[n] j))) atTop
          (𝓝 (realHessian w x (e[n] i) (e[n] j))) := by
      have h := (hasDerivAt_rotated_realHessian hxAt R hR (e[n] i) (e[n] j)).tendsto_slope_zero
      have hZero : u ∘ orthogonalFlow R hR 0 = u := funext fun y => by
        simp only [Function.comp_apply, orthogonalFlow_zero_apply]
      rw [realHessian_linearFieldDerivative hU huU hxU R]
      have h' := h.comp htLim
      change Tendsto (fun m => (t m)⁻¹ •
        (realHessian (v (0 + t m)) x (e[n] i) (e[n] j) -
          realHessian (u ∘ orthogonalFlow R hR 0) x (e[n] i) (e[n] j))) atTop _ at h'
      simpa only [zero_add, hZero, smul_eq_mul] using h'
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => (he i j).pow 2
  have hF (m : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (p m x)) μ :=
    (((hPC m).mono ball_subset_closedBall).aemeasurable measurableSet_ball).ennreal_ofReal
  have hPnonneg (m : ℕ) (x : E n) : 0 ≤ p m x := by dsimp [p]; positivity
  have hQnonneg (x : E n) : 0 ≤ q x := by dsimp [q]; positivity
  have hFatou := lintegral_liminf_le' (u := atTop) hF
  have hLimInt : (∫⁻ x, liminf (fun m => ENNReal.ofReal (p m x)) atTop ∂μ) =
      ∫⁻ x, ENNReal.ofReal (q x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    exact ((ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hLimit x hx)) :
      Tendsto (fun m => ENNReal.ofReal (p m x)) atTop (𝓝 (ENNReal.ofReal (q x)))).liminf_eq
  have hLe (m : ℕ) : (∫⁻ x, ENNReal.ofReal (p m x) ∂μ) ≤ ENNReal.ofReal (C * ‖R‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hI (hPC m)) (Eventually.of_forall (hPnonneg m))]
    exact ENNReal.ofReal_le_ofReal (hBound' m)
  have hFin : liminf (fun m => ∫⁻ x, ENNReal.ofReal (p m x) ∂μ) atTop ≤
      ENNReal.ofReal (C * ‖R‖ ^ 2) := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    exact iSup_le fun m => (iInf_le_of_le m (iInf_le_of_le le_rfl (hLe m)))
  rw [hLimInt, ← ofReal_integral_eq_lintegral_ofReal (hI hQC) (Eventually.of_forall hQnonneg)] at hFatou
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hFatou.trans hFin)

end KEBall
