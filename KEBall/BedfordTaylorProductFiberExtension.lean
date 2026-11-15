import KEBall.BedfordTaylorObstacleMaximality
import KEBall.ComplexProductBall
import PshLines.PlurisubharmonicLimits

/-!
# Extension across the fiber boundary of a product ball
-/

set_option autoImplicit false

open Filter Metric Set TopologicalSpace
open scoped Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn isSmoothPshOn_norm_sq)

/-- The open cylinder with the same base as the product ball. -/
noncomputable def complexProductCylinder (n m : ℕ) : Opens (ComplexModel (n + m)) :=
  ⟨(fun x => (complexProductCoordinates n m x).2) ⁻¹' ball 0 1,
    isOpen_ball.preimage (complexProductCoordinates n m).continuous.snd⟩

theorem mem_complexProductCylinder {n m : ℕ} {x : ComplexModel (n + m)} :
    x ∈ complexProductCylinder n m ↔ ‖(complexProductCoordinates n m x).2‖ < 1 := by
  change (complexProductCoordinates n m x).2 ∈ ball 0 1 ↔ _
  rw [mem_ball, dist_zero_right]

/-- A fiberwise quadratic on the full product cylinder. -/
noncomputable def productFiberQuadratic (n m : ℕ) (x : ComplexModel (n + m)) : ℝ :=
  ‖(complexProductCoordinates n m x).1‖ ^ 2 - 1

theorem locallyBoundedPsh_productFiberQuadratic (n m : ℕ) :
    IsLocallyBoundedPshOn (complexProductCylinder n m) (productFiberQuadratic n m) := by
  have hq : IsLocallyBoundedPshOn (⊤ : Opens (ComplexModel n)) (fun z => ‖z‖ ^ 2 - 1) := by
    simpa only [sub_eq_add_neg] using locallyBoundedPsh_add_const
      (isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_norm_sq (⊤ : Opens (ComplexModel n)))) (-1)
  unfold productFiberQuadratic
  exact locallyBoundedPsh_comp_holomorphic hq
    (F := fun x => (complexProductCoordinates n m x).1)
    (complexProductCoordinates n m).differentiable.differentiableOn.fst (fun _ _ => by simp)

/-- The potential agrees with the quadratic outside the fiber ball.
A quadratic lower bound gives a decreasing PSH approximation across
the seam by shifting the interior potential and gluing on a collar. -/
theorem locallyBoundedPsh_gluedMax_productFiberQuadratic {n m : ℕ}
    {v : ComplexModel (n + m) → ℝ} (hv : IsLocallyBoundedPshOn (complexProductBall n m) v)
    (hv₀ : ∀ x ∈ complexProductBall n m, v x ≤ 0) {A : ℝ} (hA : 0 < A)
    (hvLower : ∀ x ∈ complexProductBall n m, A * productFiberQuadratic n m x ≤ v x) :
    IsLocallyBoundedPshOn (complexProductCylinder n m)
      (gluedMax (complexProductBall n m : Set (ComplexModel (n + m))) v
        (fun x => A * productFiberQuadratic n m x)) := by
  classical
  let Ω := complexProductCylinder n m
  let P := complexProductBall n m
  let b (x : ComplexModel (n + m)) := A * productFiberQuadratic n m x
  let p := gluedMax (P : Set (ComplexModel (n + m))) v b
  have hP : P ≤ Ω := fun _ hx => mem_complexProductCylinder.mpr (mem_complexProductBall.mp hx).2
  have hb : IsLocallyBoundedPshOn Ω b :=
    locallyBoundedPsh_const_mul (locallyBoundedPsh_productFiberQuadratic n m) hA
  have hbCont : Continuous b :=
    continuous_const.mul
      (((complexProductCoordinates n m).continuous.fst.norm.pow 2).sub continuous_const)
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεAnti : Antitone ε := fun _ _ hij => one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hεLim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  let q (j : ℕ) (x : ComplexModel (n + m)) :=
    gluedMax (P : Set (ComplexModel (n + m))) (fun y => v y + -ε j) b x + ε j
  have hq (j : ℕ) : IsLocallyBoundedPshOn Ω (q j) := by
    let K : Set (ComplexModel (n + m)) := {x | b x ≤ -ε j}
    have hKclosed : IsClosed K := isClosed_le hbCont continuous_const
    have hK : closure K ∩ Ω ⊆ P := by
      rw [hKclosed.closure_eq]
      intro x hx
      have hx₁ : b x ≤ -ε j := hx.1
      have hx₂ : ‖(complexProductCoordinates n m x).2‖ < 1 := mem_complexProductCylinder.mp hx.2
      have hxρ : productFiberQuadratic n m x < 0 := by
        apply neg_of_mul_neg_right _ hA.le
        exact hx₁.trans_lt (neg_lt_zero.mpr (hε j))
      exact mem_complexProductBall.mpr
        ⟨by unfold productFiberQuadratic at hxρ; nlinarith, hx₂⟩
    apply locallyBoundedPsh_add_const _ (ε j)
    apply locallyBoundedPsh_gluedMax_of_relative_closure hb
      (locallyBoundedPsh_add_const hv (-ε j)) hP hK
    intro x hx
    have hxb : -ε j ≤ b x := le_of_lt (lt_of_not_ge hx.2)
    linarith [hv₀ x hx.1]
  have hqIn (j : ℕ) {x : ComplexModel (n + m)} (hx : x ∈ P) :
      q j x = max (v x) (b x + ε j) := by
    dsimp [q]
    rw [gluedMax_eq_max hx, ← max_add_add_right, neg_add_cancel_right]
  have hqOut (j : ℕ) {x : ComplexModel (n + m)} (hx : x ∉ P) :
      q j x = b x + ε j := by simp only [q, gluedMax, if_neg (show x ∉ (P : Set (ComplexModel (n + m))) from hx)]
  have hpIn {x : ComplexModel (n + m)} (hx : x ∈ P) : p x = v x :=
    (gluedMax_eq_max hx).trans (max_eq_left (hvLower x hx))
  have hpOut {x : ComplexModel (n + m)} (hx : x ∉ P) : p x = b x := by
    simp only [p, gluedMax, if_neg (show x ∉ (P : Set (ComplexModel (n + m))) from hx)]
  have hanti (x : ComplexModel (n + m)) : Antitone (fun j => q j x) := by
    intro i j hij
    change q j x ≤ q i x
    by_cases hx : x ∈ P
    · rw [hqIn i hx, hqIn j hx]
      exact max_le_max_left _ (add_le_add_right (hεAnti hij) _)
    · rw [hqOut i hx, hqOut j hx]
      exact add_le_add_right (hεAnti hij) _
  have hlim (x : ComplexModel (n + m)) : Tendsto (fun j => q j x) atTop (𝓝 (p x)) := by
    by_cases hx : x ∈ P
    · rw [hpIn hx]
      have h := (tendsto_const_nhds (x := v x)).max
        ((tendsto_const_nhds (x := b x)).add hεLim)
      simpa only [hqIn _ hx, add_zero, max_eq_left (show b x ≤ v x from hvLower x hx)] using h
    · rw [hpOut hx]
      simpa only [hqOut _ hx, add_zero] using (tendsto_const_nhds (x := b x)).add hεLim
  have hEq (x : ComplexModel (n + m)) : (⨅ j, (q j x : EReal)) = (p x : EReal) := by
    apply iInf_eq_of_tendsto (fun i j hij => EReal.coe_le_coe_iff.mpr (hanti x hij))
    exact EReal.tendsto_coe.mpr (hlim x)
  change IsLocallyBoundedPshOn Ω p
  refine ⟨?_, ?_⟩
  · simpa only [hEq] using DiscPshOn.plurisubharmonicOn_iInf_of_antitone Ω.isOpen
      (fun j => (hq j).1.discPshOn) (fun x _ i j hij => EReal.coe_le_coe_iff.mpr (hanti x hij))
  · intro x hx
    obtain ⟨W, hxW, hW, C, hC⟩ := hb.2 x hx
    refine ⟨W, hxW, hW, C, fun y hy => ?_⟩
    by_cases hyP : y ∈ P
    · rw [hpIn hyP, abs_of_nonpos (hv₀ y hyP)]
      exact (neg_le_neg (hvLower y hyP)).trans ((neg_le_abs _).trans (hC y hy))
    · rw [hpOut hyP]
      exact hC y hy

end KEBall.BedfordTaylor
