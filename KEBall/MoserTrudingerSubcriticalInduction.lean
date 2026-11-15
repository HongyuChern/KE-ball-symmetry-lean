import KEBall.BrezisMerleBallBounds
import KEBall.MoserTrudingerGibbsMassBound

/-!
# Subcritical finite-energy estimates from the smooth Gibbs Dirichlet problem
-/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ComplexOrder ContDiff ENNReal

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

private theorem fiber_threshold {n : ℕ} {β η : ℝ} (hβ : 0 < β) (hβη : β ≤ η)
    (hβn : β < (n + 1 : ℝ)) :
    ENNReal.ofReal (η⁻¹ ^ n / (n + 1 : ℝ)) * ENNReal.ofReal (β ^ (n + 1)) < 1 := by
  have hη : 0 < η := hβ.trans_le hβη
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_one, pow_succ]
  have hp : β ^ n ≤ η ^ n := pow_le_pow_left₀ hβ.le hβη n
  calc
    _ ≤ η⁻¹ ^ n / (n + 1 : ℝ) * (η ^ n * β) := by gcongr
    _ = β / (n + 1 : ℝ) := by
      rw [div_mul_eq_mul_div]
      congr 1
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hη.ne', one_pow, one_mul]
    _ < 1 := (div_lt_one (by positivity)).mpr hβn

set_option maxHeartbeats 700000 in
/-- Subcritical functional bounds in all dimensions follow from smooth
Gibbs Dirichlet solvability. The disk estimate is unconditional. -/
theorem exists_finiteEnergyFunctional_bound_of_smoothGibbs
    (hSolve : ∀ (n : ℕ) (γ : ℝ), 1 < n → 0 < γ → γ < (n + 1 : ℝ) →
      SmoothGibbsDirichletSolvable n γ) :
    ∀ (n : ℕ), 0 < n → ∀ (γ : ℝ), 0 < γ → γ < (n + 1 : ℝ) →
    ∃ C : ℝ, ∀ (u : ComplexModel n → EReal) (hu : IsE1 (complexUnitBall n) u),
      finiteEnergyFunctional γ hu ≤ (C : EReal) := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro hn γ hγ hγn
    by_cases h : n = 0
    · subst n
      have hγ₂ : γ < 2 := by norm_num at hγn ⊢; exact hγn
      exact ⟨_, fun _ hu => finiteEnergyFunctional_disc_le hγ hγ₂ hu⟩
    have hn₀ : 0 < n := Nat.pos_of_ne_zero h
    let N : ℝ := n + 1
    have hN : 0 < N := by dsimp [N]; positivity
    have hγN : γ < N + 1 := by simpa only [N, Nat.cast_succ] using hγn
    let s := γ * (N / (N + 1))
    have hs₀ : 0 < s := by dsimp [s]; positivity
    have hs : s < N := by
      dsimp [s]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith only [mul_lt_mul_of_pos_right hγN hN]
    let β := (s + N) / 2
    let η := (β + N) / 2
    have hsβ : s ≤ β := by dsimp [β]; linarith only [hs]
    have hβ : 0 < β := hs₀.trans_le hsβ
    have hβN : β < N := by dsimp [β]; linarith only [hs]
    have hβη : β ≤ η := by dsimp [η]; linarith only [hβN]
    have hη : 0 < η := hβ.trans_le hβη
    have hηN : η < N := by dsimp [η]; linarith only [hβN]
    obtain ⟨C, hC⟩ := ih hn₀ η hη hηN
    obtain ⟨D, hD, hMass⟩ := BrezisMerle.exists_lintegral_exp_unitBall_le_of_fiberFunctionalBound
      hn₀ hη hC (fiber_threshold hβ hβη hβN)
    have hγβ : γ * (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1 : ℝ)) ≤ β := by
      simpa only [s, N, Nat.cast_add, Nat.cast_one] using hsβ
    refine ⟨_, fun _ hu => finiteEnergyFunctional_le_of_gibbsSolvability_and_massBound hn hγ hβ
      hγβ hD hMass (hSolve (n + 1) γ (by omega) hγ hγn) hu⟩

/-- A finite-energy maximizer exists below the critical exponent under
smooth Gibbs Dirichlet solvability. -/
theorem exists_finiteEnergyFunctional_maximizer_of_smoothGibbs {n : ℕ} (hn : 0 < n) {γ : ℝ}
    (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    (hSolve : ∀ (d : ℕ) (α : ℝ), 1 < d → 0 < α → α < (d + 1 : ℝ) →
      SmoothGibbsDirichletSolvable d α) :
    ∃ (v : ComplexModel n → EReal) (hv : IsE1 (complexUnitBall n) v),
      ∀ {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u),
        finiteEnergyFunctional γ hu ≤ finiteEnergyFunctional γ hv := by
  let α := (γ + (n + 1 : ℝ)) / 2
  have hγα : γ < α := by dsimp [α]; linarith only [hγn]
  have hαn : α < (n + 1 : ℝ) := by dsimp [α]; linarith only [hγn]
  obtain ⟨C, hC⟩ := exists_finiteEnergyFunctional_bound_of_smoothGibbs hSolve n hn α
    (hγ.trans hγα) hαn
  exact exists_finiteEnergyFunctional_maximizer_of_bound hn hγ hγα (fun hu => hC _ hu)

end KEBall.MoserTrudinger
