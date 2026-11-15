import KEBall.MoserTrudingerWeakAttainmentUnconditional
import KEBall.MoserTrudingerGibbsUniform

/-! The actual smooth Gibbs inverse iteration, with unconditional uniform C0 bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology
namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell

theorem exists_smoothGibbsIteration_unconditional {n : ℕ} (hn : 2≤n) (γ : ℝ)
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x ∈ unitSphere n, v x=0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    ∃ u : ℕ → E n → ℝ, u 0=v ∧
      (∀ j, ContDiff ℝ ∞ (u j)) ∧
      (∀ j x, x∈unitSphere n → u j x=0) ∧
      (∀ j x, x∈unitBall n → (complexHessian (u j) x).PosDef) ∧
      ∀ j x, x∈unitBall n →
        (complexHessian (u (j+1)) x).det.re=gibbsDensity γ (u j) x := by
  classical
  let A := {w : E n → ℝ // ContDiff ℝ ∞ w ∧
    (∀ x∈unitSphere n, w x=0) ∧ (∀ x∈unitBall n, (complexHessian w x).PosDef)}
  have hSolve (a : A) := smoothGibbsDirichletSolvable_unconditional hn γ
    a.1 a.2.1 a.2.2.1 a.2.2.2
  let next (a : A) : A := ⟨Classical.choose (hSolve a),
    (Classical.choose_spec (hSolve a)).1,
    (Classical.choose_spec (hSolve a)).2.1,
    (Classical.choose_spec (hSolve a)).2.2.1⟩
  have hNext (a : A) (x : E n) (hx : x∈unitBall n) :
      (complexHessian (next a).1 x).det.re=gibbsDensity γ a.1 x :=
    (Classical.choose_spec (hSolve a)).2.2.2 x hx
  let a₀ : A := ⟨v,hv,hv0,hvP⟩
  let a : ℕ → A := Nat.rec a₀ (fun _ w => next w)
  refine ⟨fun j => (a j).1,rfl,fun j => (a j).2.1,
    fun j => (a j).2.2.1,fun j => (a j).2.2.2,?_⟩
  intro j x hx
  exact hNext (a j) x hx

theorem exists_bounded_smoothGibbsIteration_unconditional {n : ℕ} (hn : 2≤n)
    {γ : ℝ} (hγ : 0<γ) (hγn : γ<(n+1 : ℝ))
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x∈unitSphere n, v x=0)
    (hvP : ∀ x∈unitBall n, (complexHessian v x).PosDef) :
    ∃ (u : ℕ → E n → ℝ) (M B : ℝ),
      u 0=v ∧ (∀ j, ContDiff ℝ ∞ (u j)) ∧
      (∀ j x, x∈unitSphere n → u j x=0) ∧
      (∀ j x, x∈unitBall n → (complexHessian (u j) x).PosDef) ∧
      (∀ j x, x∈unitBall n →
        (complexHessian (u (j+1)) x).det.re=gibbsDensity γ (u j) x) ∧
      Monotone (fun j => smoothFunctional γ (u j)) ∧
      (∀ j, smoothEnergy (u j)≤M) ∧ 0<B ∧
      ∀ j x, x∈closedUnitBall n → -B≤u j x ∧ u j x≤0 := by
  obtain ⟨u,huInit,hu,hu0,huP,hEq⟩ :=
    exists_smoothGibbsIteration_unconditional hn γ hv hv0 hvP
  let β := (γ+(n+1 : ℝ))/2
  have hγβ : γ<β := by dsimp [β]; linarith only [hγn]
  have hβn : β<(n+1 : ℝ) := by dsimp [β]; linarith only [hγn]
  obtain ⟨C,hC⟩ := exists_finiteEnergyFunctional_bound_unconditional n (by omega) β
    (hγ.trans hγβ) hβn
  obtain ⟨M,B,hB,hEnergy,hLower⟩ :=
    exists_energy_and_zeroth_order_bounds_of_smoothGibbsIteration (by omega) hγ hγβ
      (fun hw => hC _ hw) isOpen_univ (subset_univ _)
      (fun j => (hu j).contDiffOn) hu0 huP hEq
  obtain ⟨B₀,hB₀⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn
    (hu 0).continuous.continuousOn
  let B' := max B B₀
  have hB' : 0<B' := hB.trans_le (le_max_left _ _)
  have hNeg (j : ℕ) (x : E n) (hx : x∈closedUnitBall n) : u j x≤0 := by
    have hNear : SmoothNear (closedUnitBall n) (u j) :=
      ⟨univ,isOpen_univ,subset_univ _,(hu j).contDiffOn⟩
    have hE := isE0_onBall_of_smooth_real_model hNear
      (fun y hy => (huP j y hy).posSemidef) (hu0 j)
    rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with h | h
    · have hxB : complexCoordinates n x∈complexUnitBall n := by
        change x∈(complexCoordinates n) ⁻¹' (complexUnitBall n : Set _)
        rw [preimage_complexUnitBall]
        exact mem_ball_zero_iff.mpr h
      have h := hE.nonpositive_unitBall (by omega) (complexCoordinates n x) hxB
      change u j ((complexCoordinates n).symm (complexCoordinates n x))≤0 at h
      simpa only [LinearIsometryEquiv.symm_apply_apply] using h
    · rw [hu0 j x (mem_sphere_zero_iff_norm.mpr h)]
  refine ⟨u,M,B',huInit,hu,hu0,huP,hEq,?_,hEnergy,hB',?_⟩
  · exact monotone_nat_of_le_succ fun j => smoothFunctional_le_of_gibbs_step
      (by omega) isOpen_univ (subset_univ _) (hu j).contDiffOn (hu (j+1)).contDiffOn
      (hu0 j) (hu0 (j+1)) (huP j) (huP (j+1)) hγ (hEq j)
  · intro j x hx
    refine ⟨?_,hNeg j x hx⟩
    cases j with
    | zero =>
      have h := hB₀ x hx
      rw [Real.norm_eq_abs] at h
      exact (neg_le_neg (le_max_right B B₀)).trans (neg_le_of_abs_le h)
    | succ j => exact (neg_le_neg (le_max_left B B₀)).trans (hLower j x hx)

end KEBall.MoserTrudinger
