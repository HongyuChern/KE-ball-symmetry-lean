import KEBall.BedfordTaylorLocalWeightLimit
import KEBall.BedfordTaylorMixedConvergence

/-!
# Joint weighted Levi convergence on an arbitrary open domain

A finite sum of convergent cutoffs on inner balls dominates any test.
The one-sided estimate on the entire domain supplies the opposite bound.
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}
  {u' p' : ℕ → ComplexModel n → ℝ}

theorem exists_test_on_inner_ball (x : Ω) {r : ℝ} (hr : 0 < r)
    (hB : closedBall (x : ComplexModel n) r ⊆ Ω) :
    ∃ χ : 𝓓(Ω, ℝ), (∀ y, 0 ≤ χ y) ∧ EqOn χ 1 (closedBall (x : ComplexModel n) (r / 4)) ∧
      tsupport χ ⊆ ball (x : ComplexModel n) (r / 2) := by
  let V := ballDomain (x : ComplexModel n) (r / 2)
  have hVΩ : V ≤ Ω := (ball_subset_ball (half_le_self hr.le)).trans (ball_subset_closedBall.trans hB)
  have hsub : closedBall (x : ComplexModel n) (r / 4) ⊆ V :=
    closedBall_subset_ball (by linarith)
  obtain ⟨χ, hχ, hχ₁⟩ := exists_testFunction_one_on (isCompact_closedBall _ _) hsub
  exact ⟨extendTest hVΩ χ, fun y => (hχ y).1, hχ₁, χ.tsupport_subset⟩

/-- Joint convergence of the weighted first Hessian for decreasing
smooth PSH sequences with arbitrary locally bounded PSH limits. -/
theorem tendsto_weightedLeviDistribution_of_decreasing_smooth
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hu' : ∀ j, IsSmoothPshOn Ω (u' j)) (hp' : ∀ j, IsSmoothPshOn Ω (p' j))
    (huanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hulim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x)))
    (hpanti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    (v : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => weightedLeviDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j))
      (isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)) v φ) atTop
      (𝓝 (weightedLeviDistribution hu hp v φ)) := by
  classical
  let T := fun j => weightedLeviDistribution (isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j))
    (isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)) v
  let S := weightedLeviDistribution hu hp v
  change Tendsto (fun j => T j φ) atTop (𝓝 (S φ))
  have hrad (x : Ω) : ∃ r : ℝ, 0 < r ∧ closedBall (x : ComplexModel n) r ⊆ Ω := by
    obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp Ω.isOpen x x.property
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hB⟩
  choose r hr hB using hrad
  choose χ hχ₀ hχ₁ hχB using fun x => exists_test_on_inner_ball x (hr x) (hB x)
  have hlocal (x : Ω) : Tendsto (fun j => T j (χ x)) atTop (𝓝 (S (χ x))) :=
    tendsto_weightedLeviDistribution_of_tsupport_subset_ball hu hp hu' hp'
      huanti hulim hpanti hplim x (half_pos (hr x)).le (half_lt_self (hr x)) (hB x) v (χ x) (hχB x)
  have hcover : tsupport φ ⊆ ⋃ x : Ω, ball (x : ComplexModel n) (r x / 4) := by
    intro y hy
    let x : Ω := ⟨y, φ.tsupport_subset hy⟩
    exact mem_iUnion.mpr ⟨x, mem_ball_self (div_pos (hr x) (by norm_num))⟩
  obtain ⟨F, hF⟩ := φ.hasCompactSupport.elim_finite_subcover
    (fun x : Ω => ball (x : ComplexModel n) (r x / 4)) (fun _ => isOpen_ball) hcover
  let η := ∑ x ∈ F, χ x
  have hηEval (y : ComplexModel n) : η y = ∑ x ∈ F, χ x y :=
    map_sum ({ toFun := fun ψ => ψ y, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      𝓓(Ω, ℝ) →+ ℝ) χ F
  have hη₀ (y : ComplexModel n) : 0 ≤ η y := by
    rw [hηEval]
    exact Finset.sum_nonneg (fun x _ => hχ₀ x y)
  have hη₁ (y : ComplexModel n) (hy : y ∈ tsupport φ) : 1 ≤ η y := by
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hF hy)
    obtain ⟨hxF, hyB⟩ := mem_iUnion.mp hx
    have h₁ : χ x y = 1 := hχ₁ x (ball_subset_closedBall hyB)
    have hle : χ x y ≤ ∑ x ∈ F, χ x y :=
      Finset.single_le_sum (fun z _ => hχ₀ z y) hxF
    simpa only [hηEval, h₁] using hle
  obtain ⟨C₀, hC₀⟩ :=
    (φ.hasCompactSupport.image_of_continuousOn φ.continuous.abs.continuousOn).bddAbove
  let C := max 0 C₀
  have hC₀' : 0 ≤ C := le_max_left _ _
  have hη (y : ComplexModel n) : |φ y| ≤ (C • η) y := by
    rw [smul_apply, smul_eq_mul]
    by_cases hy : y ∈ tsupport φ
    · exact ((hC₀ ⟨y, hy, rfl⟩).trans (le_max_right _ _)).trans
        (le_mul_of_one_le_right hC₀' (hη₁ y hy))
    · simp only [image_eq_zero_of_notMem_tsupport hy, abs_zero]
      exact mul_nonneg hC₀' (hη₀ y)
  apply tendsto_of_upper_of_dominating_test
    (fun ψ hψ _ hε => eventually_weightedLeviDistribution_lt_add hu hp hu'
      (fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j))
      huanti hulim hpanti hplim v ψ hψ hε) (C • η) φ hη
  simp only [η, map_smul, map_sum, smul_eq_mul]
  exact (tendsto_finsetSum F (fun x _ => hlocal x)).const_mul C

theorem tendsto_secondMixedHessian_of_decreasing_smooth
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (hu' : ∀ j, IsSmoothPshOn Ω (u' j)) (hp' : ∀ j, IsSmoothPshOn Ω (p' j))
    (huanti : ∀ x ∈ Ω, Antitone (fun j => u' j x))
    (hulim : ∀ x ∈ Ω, Tendsto (fun j => u' j x) atTop (𝓝 (u x)))
    (hpanti : ∀ x ∈ Ω, Antitone (fun j => p' j x))
    (hplim : ∀ x ∈ Ω, Tendsto (fun j => p' j x) atTop (𝓝 (p x)))
    (v w : Fin 2 → ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => secondMixedHessian (isLocallyBoundedPshOn_of_isSmoothPshOn (hu' j))
      (isLocallyBoundedPshOn_of_isSmoothPshOn (hp' j)) v w φ) atTop
      (𝓝 (secondMixedHessian hu hp v w φ)) := by
  apply tendsto_secondMixedHessian_of_weightedComplexHessian_test _ v w φ
  intro a b ψ
  simp only [weightedComplexHessian]
  exact tendsto_polarizedLeviDistribution_test
    (tendsto_weightedLeviDistribution_of_decreasing_smooth hu hp hu' hp' huanti hulim hpanti hplim)
    a b ψ

end KEBall.BedfordTaylor
