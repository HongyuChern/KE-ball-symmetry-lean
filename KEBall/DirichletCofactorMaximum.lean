import KEBall.DirichletSmoothLinearizedSolution
import KEBall.DirichletGradient

/-! Uniqueness of smooth solutions to the cofactor Dirichlet equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

private theorem smoothNear_sub_const_mul {n : ℕ} {v u : E n → ℝ}
    (hv : SmoothNear (closedUnitBall n) v) (hu : SmoothNear (closedUnitBall n) u) (a : ℝ) :
    SmoothNear (closedUnitBall n) (fun x => v x - a * u x) := by
  obtain ⟨V, hV, hVK, hv⟩ := hv
  obtain ⟨U, hU, hUK, hu⟩ := hu
  exact ⟨V ∩ U, hV.inter hU, subset_inter hVK hUK,
    (hv.mono inter_subset_left).sub (contDiffOn_const.mul (hu.mono inter_subset_right))⟩

/-- Weak maximum principle for the actual complex Laplacian of a smooth
strictly plurisubharmonic potential with zero Dirichlet boundary. -/
theorem le_boundary_bound_of_complexLaplacian_nonneg {n : ℕ} (hn : 0 < n)
    {u w : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hw : SmoothNear (closedUnitBall n) w)
    (hL : ∀ x ∈ unitBall n, 0 ≤ complexLaplacian u w x)
    {C : ℝ} (hC : ∀ x ∈ unitSphere n, w x ≤ C) :
    ∀ x ∈ closedUnitBall n, w x ≤ C := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hPerturb (ε : ℝ) (hε : 0 < ε) :
      ∀ x ∈ closedUnitBall n, w x - (-ε) * u x ≤ C := by
    apply le_boundary_bound_of_complexLaplacian_pos (u := u)
      (smoothNear_sub_const_mul hw hu (-ε)) huP _ _
    · intro x hx
      have hx' := ball_subset_closedBall hx
      have huAt := hu.contDiffAt hx'
      have hdet : IsUnit (complexHessian u x).det :=
        isUnit_iff_ne_zero.mpr (fun h => (posDef_det_re_pos (huP x hx)).ne' (by simp [h]))
      rw [complexLaplacian_sub_at u (hw.contDiffAt hx') (contDiffAt_const.mul huAt),
        complexLaplacian_const_mul_at u huAt, complexLaplacian_self_of_isUnit hdet]
      linarith only [hL x hx, mul_pos hε hn']
    · intro x hx
      simpa only [hu0 x hx, mul_zero, sub_zero] using hC x hx
  intro x hx
  have hLim : Tendsto (fun ε : ℝ => w x - (-ε) * u x) (𝓝[>] (0 : ℝ)) (𝓝 (w x)) := by
    have hT : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [neg_zero, zero_mul, sub_zero] using
      tendsto_const_nhds.sub (hT.neg.mul tendsto_const_nhds)
  have hEv : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), w x - (-ε) * u x ≤ C :=
    Filter.Eventually.mono self_mem_nhdsWithin (fun ε hε => hPerturb ε hε x hx)
  exact le_of_tendsto hLim hEv

/-- Smooth solutions with the same cofactor forcing and the same boundary
values agree on the closed ball. -/
theorem eqOn_of_cofactorContraction_eq {n : ℕ} (hn : 0 < n)
    {u v w : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hv : SmoothNear (closedUnitBall n) v) (hw : SmoothNear (closedUnitBall n) w)
    (hBoundary : EqOn v w (unitSphere n))
    (hEq : EqOn (MoserTrudinger.cofactorContraction u v)
      (MoserTrudinger.cofactorContraction u w) (unitBall n)) :
    EqOn v w (closedUnitBall n) := by
  have hLap (x : E n) (hx : x ∈ unitBall n) :
      complexLaplacian u v x = complexLaplacian u w x := by
    have he := hEq hx
    simp only [cofactorContraction_eq_det_mul_complexLaplacian (huP x hx)] at he
    exact mul_left_cancel₀ (posDef_det_re_pos (huP x hx)).ne' he
  have hLe {v w : E n → ℝ} (hv : SmoothNear (closedUnitBall n) v)
      (hw : SmoothNear (closedUnitBall n) w) (hB : EqOn v w (unitSphere n))
      (hE : ∀ x ∈ unitBall n, complexLaplacian u v x = complexLaplacian u w x) :
      ∀ x ∈ closedUnitBall n, v x ≤ w x := by
    have hD : SmoothNear (closedUnitBall n) (fun x => v x - w x) := by
      simpa only [one_mul] using smoothNear_sub_const_mul hv hw 1
    have hL (x : E n) (hx : x ∈ unitBall n) :
        0 ≤ complexLaplacian u (fun y => v y - w y) x := by
      rw [complexLaplacian_sub_at u (hv.contDiffAt (ball_subset_closedBall hx))
        (hw.contDiffAt (ball_subset_closedBall hx)), hE x hx, sub_self]
    have h := le_boundary_bound_of_complexLaplacian_nonneg hn hu hu0 huP hD hL
      (C := 0) (fun x hx => sub_nonpos.mpr (hB hx).le)
    exact fun x hx => sub_nonpos.mp (h x hx)
  intro x hx
  exact le_antisymm (hLe hv hw hBoundary hLap x hx)
    (hLe hw hv hBoundary.symm (fun y hy => (hLap y hy).symm) x hx)

/-- The cofactor maximum estimate with bounded forcing and boundary data. -/
theorem abs_le_of_cofactorContraction_abs_le_of_boundary {n : ℕ} (hn : 0 < n)
    {u v : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hv : SmoothNear (closedUnitBall n) v)
    {B : ℝ} (hvB : ∀ x ∈ unitSphere n, |v x| ≤ B)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hForcing : ∀ x ∈ unitBall n, |MoserTrudinger.cofactorContraction u v x| ≤ M) :
    ∀ x ∈ closedUnitBall n, |v x| ≤ B + (M / (a * n)) * (-u x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let c := M / (a * n)
  have hc : 0 ≤ c := div_nonneg hM (mul_nonneg ha.le hn'.le)
  have hca : c * (a * n) = M := div_mul_cancel₀ _ (mul_pos ha hn').ne'
  have hSign (s : ℝ) (hs : |s| = 1) : ∀ x ∈ closedUnitBall n, s * v x ≤ B + c * (-u x) := by
    have hSV : SmoothNear (closedUnitBall n) (fun x => s * v x) := by
      obtain ⟨V, hV, hVK, hvV⟩ := hv
      exact ⟨V, hV, hVK, contDiffOn_const.mul hvV⟩
    let w (x : E n) := s * v x - (-c) * u x
    have hw : SmoothNear (closedUnitBall n) w := smoothNear_sub_const_mul hSV hu (-c)
    have hL (x : E n) (hx : x ∈ unitBall n) : 0 ≤ complexLaplacian u w x := by
      have hx' := ball_subset_closedBall hx
      have huAt := hu.contDiffAt hx'
      have hdet : IsUnit (complexHessian u x).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp (huP x hx).isUnit
      let d := (complexHessian u x).det.re
      have hd : 0 < d := ha.trans_le (hDensity x hx)
      have hForced := hForcing x hx
      rw [cofactorContraction_eq_det_mul_complexLaplacian (huP x hx)] at hForced
      change |d * complexLaplacian u v x| ≤ M at hForced
      have hSigned : -M ≤ s * (d * complexLaplacian u v x) := by
        apply (abs_le.mp ?_).1
        rwa [abs_mul, hs, one_mul]
      have hBarrier : M ≤ d * (c * n) := by
        calc
          M = c * (a * n) := hca.symm
          _ = a * (c * n) := by ring
          _ ≤ d * (c * n) :=
            mul_le_mul_of_nonneg_right (hDensity x hx) (mul_nonneg hc hn'.le)
      change 0 ≤ complexLaplacian u (fun y => s * v y - (-c) * u y) x
      rw [complexLaplacian_sub_at u (hSV.contDiffAt hx') (contDiffAt_const.mul huAt),
        complexLaplacian_const_mul_at u (hv.contDiffAt hx'), complexLaplacian_const_mul_at u huAt,
        complexLaplacian_self_of_isUnit hdet]
      apply nonneg_of_mul_nonneg_right _ hd
      nlinarith only [hSigned, hBarrier]
    have hBound := le_boundary_bound_of_complexLaplacian_nonneg hn hu hu0 huP hw hL
      (C := B) (fun x hx => by
        dsimp only [w]
        rw [hu0 x hx, mul_zero, sub_zero]
        exact (le_abs_self _).trans (by simpa only [abs_mul, hs, one_mul] using hvB x hx))
    intro x hx
    have h := hBound x hx
    dsimp [w] at h
    linarith only [h]
  intro x hx
  rw [abs_le]
  have h₁ := hSign 1 (by norm_num) x hx
  have h₂ := hSign (-1) (by norm_num) x hx
  exact ⟨by linarith only [h₂], by simpa only [one_mul] using h₁⟩

/-- The inverse cofactor operator with zero boundary data is bounded
pointwise by a multiple of the negative background potential. -/
theorem abs_le_of_cofactorContraction_abs_le {n : ℕ} (hn : 0 < n)
    {u v : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hv : SmoothNear (closedUnitBall n) v)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hForcing : ∀ x ∈ unitBall n, |MoserTrudinger.cofactorContraction u v x| ≤ M) :
    ∀ x ∈ closedUnitBall n, |v x| ≤ (M / (a * n)) * (-u x) := by
  simpa only [zero_add] using abs_le_of_cofactorContraction_abs_le_of_boundary hn hu hu0 huP hv
    (B := 0) (fun x hx => by simp [hv0 x hx]) ha hM hDensity hForcing

/-- Every smooth forcing has a smooth zero-boundary cofactor solution.
Its restriction to the closed ball is unique. -/
theorem exists_uniqueOn_closedUnitBall_cofactor_solution {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x)
    {G : E n → ℝ} (hG : SmoothNear (closedUnitBall n) G) :
    ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      EqOn (MoserTrudinger.cofactorContraction u v) (fun x => -G x) (unitBall n) ∧
      ∀ w : E n → ℝ, SmoothNear (closedUnitBall n) w →
        (∀ x ∈ unitSphere n, w x = 0) →
        EqOn (MoserTrudinger.cofactorContraction u w) (fun x => -G x) (unitBall n) →
        EqOn w v (closedUnitBall n) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hCont : ContinuousOn G (closedUnitBall n) :=
    fun x hx => (hG.contDiffAt hx).continuousAt.continuousWithinAt
  have hComp : IsCompact (closedUnitBall n) := isCompact_closedBall _ _
  have hMeas : MeasurableSet (unitBall n) := measurableSet_ball
  have hSub : unitBall n ⊆ closedUnitBall n := ball_subset_closedBall
  obtain ⟨C, hC⟩ := hComp.exists_bound_of_continuousOn hCont
  have hLp : MemLp G 2 ((volume0 n).restrict (unitBall n)) := by
    refine MemLp.of_bound (hCont.aestronglyMeasurable_of_subset_isCompact hComp hMeas hSub) C ?_
    filter_upwards [ae_restrict_mem (μ := volume0 n) hMeas] with x hx
    exact hC x (hSub hx)
  obtain ⟨_, v, _, hv, _, hv0, hEq⟩ :=
    exists_smoothNear_closedUnitBall_cofactor_solution hn hu huP ha hl hDensity hElliptic
      (hLp.toLp G) hG (MemLp.coeFn_toLp hLp)
  refine ⟨v, hv, hv0, hEq, fun w hw hw0 hEqW => ?_⟩
  exact eqOn_of_cofactorContraction_eq hn hu hu0 huP hw hv
    (fun x hx => (hw0 x hx).trans (hv0 x hx).symm)
    (fun x hx => (hEqW hx).trans (hEq hx).symm)

end KEBall
