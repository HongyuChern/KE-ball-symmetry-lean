import KEBall.BedfordTaylorSmoothLocalCurvature
import KEBall.BedfordTaylorQuadraticPerturbation

/-!
# Smooth decreasing approximations for the distributional fiber curvature
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn
  IsDecreasingApproximation RelativelyCompactIn isSmoothPshOn_of_psh isSmoothPshOn_norm_sq)
open PshLines.Regularization.HolomorphicPullback

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

/-- A fiber slice of a potential in the ambient Euclidean complex model. -/
noncomputable def complexFiberSlice {n : ℕ} (p : ComplexModel (n + 1) → ℝ) (w : ComplexModel 1) :
    ComplexModel n → ℝ :=
  fun z => p ((complexProductCoordinates n 1).symm (z, w))

theorem locallyBoundedPsh_complexFiberSlice {n : ℕ} {R ρ : ℝ}
    {p : ComplexModel (n + 1) → ℝ} (hp : IsLocallyBoundedPshOn (fiberEnergyCylinder n R ρ) p)
    {w : ComplexModel 1} (hw : ‖w‖ < ρ) :
    IsLocallyBoundedPshOn (ballDomain 0 R) (complexFiberSlice p w) := by
  let e := complexProductCoordinates n 1
  let F (z : ComplexModel n) := e.symm (z, w)
  have hF : Differentiable ℂ F := e.symm.differentiable.comp
    (differentiable_id.prodMk (differentiable_const w))
  apply locallyBoundedPsh_comp_holomorphic hp hF.differentiableOn
  intro z hz
  apply mem_fiberEnergyCylinder.mpr
  change ‖(e (e.symm (z, w))).1‖ < R ∧ ‖(e (e.symm (z, w))).2‖ < ρ
  rw [e.apply_symm_apply]
  exact ⟨mem_ball_zero_iff.mp hz, hw⟩

theorem contDiff_complexFiberSlice {n : ℕ} {p : ComplexModel (n + 1) → ℝ}
    (hp : ContDiff ℝ ∞ p) (w : ComplexModel 1) : ContDiff ℝ ∞ (complexFiberSlice p w) :=
  hp.comp (((complexProductCoordinates n 1).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
    (contDiff_id.prodMk contDiff_const))

theorem relativelyCompact_fiberEnergyCylinder {n : ℕ} (R : ℝ) {ρ : ℝ} (hρ : ρ < 1) :
    RelativelyCompactIn (fiberEnergyCylinder n R ρ) (complexProductCylinder n 1) := by
  let e := complexProductCoordinates n 1
  let K := e ⁻¹' (closedBall 0 R ×ˢ closedBall 0 ρ)
  have hK : IsCompact K := e.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hsub : closure (fiberEnergyCylinder n R ρ : Set (ComplexModel (n + 1))) ⊆ K :=
    closure_minimal (preimage_mono (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)) hK.isClosed
  refine ⟨hK.of_isClosed_subset isClosed_closure hsub, hsub.trans ?_⟩
  intro x hx
  exact mem_complexProductCylinder.mpr ((mem_closedBall_zero_iff.mp hx.2).trans_lt hρ)

private theorem locallyBoundedPsh_fiberNormSq {n : ℕ} (W : Opens (ComplexModel (n + 1))) :
    IsLocallyBoundedPshOn W (fun x => ‖(complexProductCoordinates n 1 x).1‖ ^ 2) := by
  let e := complexProductCoordinates n 1
  exact locallyBoundedPsh_comp_holomorphic
    (isLocallyBoundedPshOn_of_isSmoothPshOn
      (isSmoothPshOn_norm_sq (⊤ : Opens (ComplexModel n))))
    (F := fun x => (e x).1) e.differentiable.differentiableOn.fst (fun _ _ => by simp)

private theorem posDef_fiberDilation_add_normSq {n : ℕ} {q : ComplexModel (n + 1) → ℝ}
    (hq : ContDiff ℝ ∞ q) {R ρ δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hs : IsSmoothPshOn (fiberEnergyCylinder n R ρ) q)
    (c : ℝ) (w : E 1) (hw : w ∈ ball (0 : E 1) ρ) (z : E n) (hz : z ∈ unitBall n) :
    (KEBall.complexHessian (fun y => q (fiberDilationCoordinates n R (y, w)) +
      δ * ‖(complexProductCoordinates n 1 (fiberDilationCoordinates n R (y, w))).1‖ ^ 2 - c) z).PosDef := by
  let e := complexProductCoordinates n 1
  let f (x : ComplexModel (n + 1)) := q x + δ * ‖(e x).1‖ ^ 2 - c
  let er := e.toContinuousLinearMap.restrictScalars ℝ
  have hf : ContDiff ℝ ∞ f := (hq.add (contDiff_const.mul
    ((contDiff_norm_sq ℝ).comp er.contDiff.fst))).sub contDiff_const
  let w' := complexCoordinates 1 w
  let z' := R • complexCoordinates n z
  let q' := complexFiberSlice q w'
  let b (y : ComplexModel n) := ‖y‖ ^ 2
  have hqw : ‖w'‖ < ρ := by
    dsimp only [w']
    rw [LinearIsometryEquiv.norm_map]
    exact mem_ball_zero_iff.mp hw
  have hz' : z' ∈ (ballDomain (0 : ComplexModel n) R : Set (ComplexModel n)) := by
    apply mem_ball_zero_iff.mpr
    dsimp only [z']
    rw [norm_smul, Real.norm_of_nonneg hR.le, LinearIsometryEquiv.norm_map]
    exact mul_lt_of_lt_one_right hR (mem_ball_zero_iff.mp hz)
  have hq'S : IsSmoothPshOn (ballDomain (0 : ComplexModel n) R) q' :=
    isSmoothPshOn_of_psh (contDiff_complexFiberSlice hq w').contDiffOn
      (locallyBoundedPsh_complexFiberSlice (isLocallyBoundedPshOn_of_isSmoothPshOn hs) hqw).1
  have hFE : complexFiberSlice f w' = (q' + δ • b) + (fun _ => -c) := by
    funext y
    change q (e.symm (y, w')) + δ * ‖(e (e.symm (y, w'))).1‖ ^ 2 - c =
      q (e.symm (y, w')) + δ * ‖y‖ ^ 2 + -c
    rw [e.apply_symm_apply, sub_eq_add_neg]
  have h2 : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hq2 : ContDiffAt ℝ 2 q' z' := ((contDiff_complexFiberSlice hq w').of_le h2).contDiffAt
  have hb2 : ContDiffAt ℝ 2 b z' := (contDiff_norm_sq ℝ).contDiffAt
  have hbδ : ContDiffAt ℝ 2 (δ • b) z' := hb2.const_smul δ
  have hadd : ContDiffAt ℝ 2 (q' + δ • b) z' := hq2.add hbδ
  have hfP : (modelHessian (complexFiberSlice f w') z').PosDef := by
    rw [hFE, PshLines.FirstPass.MongeAmpere.complexHessian_add hadd contDiffAt_const,
      PshLines.FirstPass.MongeAmpere.complexHessian_const, add_zero,
      PshLines.FirstPass.MongeAmpere.complexHessian_add hq2 hbδ,
      PshLines.FirstPass.MongeAmpere.complexHessian_smul hb2 δ,
      show modelHessian b z' = 1 from PshLines.FirstPass.MongeAmpere.complexHessian_norm_sq z']
    have hp : ((δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.posDef_diagonal_iff]
      exact fun _ => by exact_mod_cast hδ
    exact Matrix.PosDef.posSemidef_add (hq'S.2.2 z' hz') hp
  change (KEBall.complexHessian (fun y => f (fiberDilationCoordinates n R (y, w))) z).PosDef
  rw [fiberComplexHessian_fiberDilationCoordinates hf]
  change (((R : ℂ) ^ 2) • modelHessian (complexFiberSlice f w') z').PosDef
  rw [← Complex.ofReal_pow]
  change ((R ^ 2 : ℝ) • modelHessian (complexFiberSlice f w') z').PosDef
  exact hfP.smul (pow_pos hR _)

set_option maxHeartbeats 750000 in
/-- A decreasing smooth approximation on a larger cylinder keeps a common
quadratic collar and has strictly positive vertical Hessians. -/
theorem exists_productFiber_curvatureApproximation {n : ℕ} {ρ A : ℝ}
    (hρ : ρ < 1) (hA : 0 < A) {v : ComplexModel (n + 1) → ℝ}
    (hp : IsLocallyBoundedPshOn (complexProductCylinder n 1)
      (gluedMax (complexProductBall n 1 : Set (ComplexModel (n + 1))) v
        (fun x => A * productFiberQuadratic n 1 x))) :
    let p := gluedMax (complexProductBall n 1 : Set (ComplexModel (n + 1))) v
      (fun x => A * productFiberQuadratic n 1 x)
    let W := fiberEnergyCylinder n 3 ρ
    ∃ (q : ℕ → ComplexModel (n + 1) → ℝ) (a d : ℕ → ℝ),
      IsDecreasingApproximation W p q ∧ (∀ j, ContDiff ℝ ∞ (q j)) ∧
      (∀ j, 0 < a j ∧ a j ≤ A + 1) ∧ Tendsto a atTop (𝓝 A) ∧
      Tendsto d atTop (𝓝 (-A)) ∧
      (∀ j x, x ∈ W → (3 / 2 : ℝ) ≤ ‖(complexProductCoordinates n 1 x).1‖ →
        q j x = a j * ‖(complexProductCoordinates n 1 x).1‖ ^ 2 + d j) ∧
      ∀ j c w, w ∈ ball (0 : E 1) ρ → ∀ z ∈ unitBall n,
        (KEBall.complexHessian (fun y => q j (fiberDilationCoordinates n 2 (y, w)) - c) z).PosDef := by
  let e := complexProductCoordinates n 1
  let p := gluedMax (complexProductBall n 1 : Set (ComplexModel (n + 1))) v
    (fun x => A * productFiberQuadratic n 1 x)
  let W := fiberEnergyCylinder n 3 ρ
  let U := fiberEnergyCylinder n 2 ρ
  have hUW : U ≤ W := fun _ hx =>
    mem_fiberEnergyCylinder.mpr ⟨(mem_fiberEnergyCylinder.mp hx).1.trans (by norm_num),
      (mem_fiberEnergyCylinder.mp hx).2⟩
  obtain ⟨f, hf, _, _, s, hs, K, hK, hKΩ, _, hForm, hBall⟩ :=
    exists_order_preserving_smoothApproximation_centered (relativelyCompact_fiberEnergyCylinder (n := n) 3 hρ)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * s)
  let δ (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  let q₀ (j : ℕ) := f p (j + k)
  let b (x : ComplexModel (n + 1)) := ‖(e x).1‖ ^ 2
  let q (j : ℕ) (x : ComplexModel (n + 1)) := q₀ j x + δ j * b x
  let a (j : ℕ) := A + δ j
  let d (j : ℕ) := A * (productFiberKernelSecondMoment n 1 s hs (j + k) - 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδLe (j : ℕ) : δ j ≤ 1 := by
    exact (div_le_self zero_le_one (le_add_of_nonneg_left (Nat.cast_nonneg j)))
  have hδAnti : Antitone δ := fun i j hij => one_div_le_one_div_of_le (by positivity)
    (add_le_add (Nat.cast_le.mpr hij) le_rfl)
  have hδLim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hq₀S (j : ℕ) : IsSmoothPshOn W (q₀ j) := (hf p hp).1 (j + k)
  have hPInt : LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact
      (PshLines.FirstPass.MongeAmpere.locallyIntegrableOn_of_plurisubharmonicOn_real hp.1)
      hK hKΩ).locallyIntegrable
  have hq₀ (j : ℕ) : ContDiff ℝ ∞ (q₀ j) := by
    rw [show q₀ j = _ from hForm p (j + k)]
    exact contDiff_translationPairing hPInt (explicitRadialKernel_hasCompactSupport s hs _)
      (explicitRadialKernel_contDiff s hs _)
  have hb : ContDiff ℝ ∞ b :=
    (contDiff_norm_sq ℝ).comp (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.fst
  have hq (j : ℕ) : ContDiff ℝ ∞ (q j) := (hq₀ j).add (contDiff_const.mul hb)
  have hqS (j : ℕ) : IsSmoothPshOn W (q j) :=
    isSmoothPshOn_of_psh (hq j).contDiffOn (locallyBoundedPsh_add
      (isLocallyBoundedPshOn_of_isSmoothPshOn (hq₀S j))
      (locallyBoundedPsh_const_mul (locallyBoundedPsh_fiberNormSq W) (hδ j))).1
  refine ⟨q, a, d, ⟨hqS, ?_, ?_⟩, hq, fun j => ⟨by dsimp [a]; positivity, add_le_add le_rfl (hδLe j)⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x hx i j hij
    exact add_le_add ((hf p hp).2.1 x hx (Nat.add_le_add_right hij k))
      (mul_le_mul_of_nonneg_right (hδAnti hij) (sq_nonneg _))
  · intro x hx
    have he := ((hf p hp).2.2 x hx).comp (tendsto_add_atTop_nat k)
    simpa only [q, q₀, Function.comp_apply, zero_mul, add_zero] using he.add (hδLim.mul_const (b x))
  · simpa only [a, add_zero] using (tendsto_const_nhds (x := A)).add hδLim
  · have he := (tendsto_productFiberKernelSecondMoment n 1 hs).comp (tendsto_add_atTop_nat k)
    simpa only [d, Function.comp_apply, zero_sub, mul_neg, mul_one] using
      (he.sub_const (1 : ℝ)).const_mul A
  · intro j x hx hxr
    have hjk : (2 * s) ≤ ((j + k : ℕ) : ℝ) + 1 := by
      push_cast
      linarith only [hk, Nat.cast_nonneg (α := ℝ) j]
    have hsR : s / (((j + k : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith only [hjk]
    have hxR : 1 + s / (((j + k : ℕ) : ℝ) + 1) ≤ ‖(e x).1‖ := by linarith only [hxr, hsR]
    have he := translationPairing_gluedMax_fiberQuadratic_eq (v := v) (A := A) hs (j + k) (hBall x hx) hxR
    have hqEq : q₀ j x = A * (productFiberQuadratic n 1 x +
        productFiberKernelSecondMoment n 1 s hs (j + k)) := by
      rw [show q₀ j = _ from hForm p (j + k)]
      exact he
    change q₀ j x + δ j * b x = _
    rw [hqEq]
    unfold productFiberQuadratic a b d
    ring
  · intro j c w hw z hz
    have hU : IsSmoothPshOn U (q₀ j) :=
      ⟨(hq₀S j).1.mono hUW, (hq₀S j).2.1.mono hUW, fun x hx => (hq₀S j).2.2 x (hUW hx)⟩
    exact posDef_fiberDilation_add_normSq (hq₀ j) (by norm_num) (hδ j) hU c w hw z hz

end KEBall.BedfordTaylor
