import KEBall.CegrellL1Bound
import KEBall.CegrellDecreasingClosure
import KEBall.BedfordTaylorMonotoneRepresentative
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Closure of Cegrell energy sublevels under almost-everywhere convergence
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ContDiff Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

private noncomputable def finiteTailMax (p : ℕ → ComplexModel n → EReal) (j : ℕ) :
    ℕ → ComplexModel n → EReal
  | 0 => p j
  | m + 1 => fun x => max (finiteTailMax p j m x) (p (m + 1 + j) x)

private theorem finiteTailMax_ge (p : ℕ → ComplexModel n → EReal)
    (j m : ℕ) (x : ComplexModel n) : p j x ≤ finiteTailMax p j m x := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact ih.trans (le_max_left _ _)

private theorem finiteTailMax_iSup (p : ℕ → ComplexModel n → EReal) (j : ℕ) (x : ComplexModel n) :
    (⨆ m, finiteTailMax p j m x) = ⨆ m, p (m + j) x := by
  apply le_antisymm
  · apply iSup_le
    intro m
    induction m with
    | zero => simpa only [finiteTailMax, zero_add] using (le_iSup (fun m => p (m + j) x) 0)
    | succ m ih => exact max_le ih (le_iSup (fun m => p (m + j) x) (m + 1))
  · apply iSup_le
    intro m
    cases m with
    | zero => simpa only [finiteTailMax, zero_add] using (le_iSup (fun m => finiteTailMax p j m x) 0)
    | succ m => exact (le_max_right _ _).trans (le_iSup (fun m => finiteTailMax p j m x) (m + 1))

/-- Almost-everywhere limits of a common finite-energy sublevel have
a plurisubharmonic representative in that sublevel. -/
theorem exists_isE1_of_ae_tendsto_of_energy_le (hn : 0 < n)
    {p : ℕ → ComplexModel n → EReal} (hp : ∀ j, IsE1 (complexUnitBall n) (p j))
    {u : ComplexModel n → EReal}
    (hlim : ∀ᵐ x ∂(volume : Measure (ComplexModel n)).restrict (complexUnitBall n),
      Tendsto (fun j => p j x) atTop (𝓝 (u x)))
    {M : ℝ≥0∞} (hMfin : M < ⊤) (hM : ∀ j, energy (hp j) ≤ M) :
    ∃ v : ComplexModel n → EReal, ∃ hv : IsE1 (complexUnitBall n) v, energy hv ≤ M ∧
      v =ᵐ[(volume : Measure (ComplexModel n)).restrict (complexUnitBall n)] u := by
  let B := complexUnitBall n
  let μ := (volume : Measure (ComplexModel n)).restrict B
  have hdom : ∀ᵐ x ∂μ, x ∈ B := ae_restrict_mem B.isOpen.measurableSet
  have hPsh (j m : ℕ) : PlurisubharmonicOn (finiteTailMax p j m) B := by
    induction m with
    | zero => exact (hp j).1
    | succ m ih => exact ih.max (hp (m + 1 + j)).1
  have hNeg (j m : ℕ) (x : ComplexModel n) (hx : x ∈ B) : finiteTailMax p j m x ≤ 0 := by
    induction m with
    | zero => exact (hp j).nonpositive_unitBall hn x hx
    | succ m ih => exact max_le ih ((hp (m + 1 + j)).nonpositive_unitBall hn x hx)
  have hE1 (j m : ℕ) : IsE1 B (finiteTailMax p j m) :=
    ((hp j).of_ge hn (hPsh j m) (hNeg j m) (fun x _ => finiteTailMax_ge p j m x)).choose
  have hRep (j : ℕ) : ∃ v : ComplexModel n → EReal, PlurisubharmonicOn v B ∧
      ∀ᵐ x ∂μ, v x = ⨆ m, p (m + j) x := by
    obtain ⟨v, hv, he⟩ := exists_psh_iSup_of_monotone (hPsh j) (hNeg j)
      (fun m => (hE1 j m).integrableOn_toReal hn) (fun m => (hE1 j m).ae_finite hn)
      (fun x _ => monotone_nat_of_le_succ fun m => le_max_left _ _)
    exact ⟨v, hv, he.mono fun x hx => hx.trans (finiteTailMax_iSup p j x)⟩
  choose v hvP hve using hRep
  have hvNonpos (j : ℕ) (x : ComplexModel n) (hx : x ∈ B) : v j x ≤ 0 := by
    have hzero : PlurisubharmonicOn (fun _ : ComplexModel n => (0 : EReal)) B :=
      fun y _ => plurisubharmonicAt_const _ (by simp) y
    exact (hvP j).le_of_ae_le B.isOpen hzero.upperSemicontinuousOn volume (by
      filter_upwards [hve j, hdom] with y hy hyB
      rw [hy]
      exact iSup_le fun m => (hp (m + j)).nonpositive_unitBall hn y hyB) x hx
  have hvAbove (j : ℕ) (x : ComplexModel n) (hx : x ∈ B) : p j x ≤ v j x :=
    (hp j).1.le_of_ae_le B.isOpen (hvP j).upperSemicontinuousOn volume (by
      filter_upwards [hve j] with y hy
      rw [hy]
      simpa only [zero_add] using le_iSup (fun m => p (m + j) y) 0) x hx
  have hvE (j : ℕ) : ∃ h : IsE1 B (v j), energy h ≤ energy (hp j) :=
    (hp j).of_ge hn (hvP j) (hvNonpos j) (hvAbove j)
  choose hve1 hvEnergy using hvE
  have hvAnti (x : ComplexModel n) (hx : x ∈ B) : Antitone (fun j => v j x) := by
    intro i j hij
    exact (hvP j).le_of_ae_le B.isOpen (hvP i).upperSemicontinuousOn volume (by
      filter_upwards [hve i, hve j] with y hyi hyj
      rw [hyi, hyj]
      apply iSup_le
      intro m
      have he : m + j = (m + (j - i)) + i := by omega
      rw [he]
      exact le_iSup (fun k => p (k + i) y) (m + (j - i))) x hx
  obtain ⟨h, he⟩ := isE1_iInf_of_antitone hn hve1 hvAnti
    ((iSup_le fun j => (hvEnergy j).trans (hM j)).trans_lt hMfin)
  refine ⟨fun x => ⨅ j, v j x, h, he.le.trans (iSup_le fun j => (hvEnergy j).trans (hM j)), ?_⟩
  filter_upwards [ae_all_iff.mpr hve, hlim] with x hx hxu
  simpa only [hx, limsup_eq_iInf_iSup_of_nat'] using hxu.limsup_eq

theorem energy_congr (hn : 0 < n) {u v : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) (hv : IsE1 (complexUnitBall n) v)
    (he : EqOn u v (complexUnitBall n)) :
    energy hu = energy hv := by
  obtain ⟨p⟩ := hu.2
  let q : E1Approximation (complexUnitBall n) v :=
    { p with pointwise := fun x hx => he hx ▸ p.pointwise x hx }
  rw [energy_eq_iSup hn hu p, energy_eq_iSup hn hv q]

/-- Lower semicontinuity along an almost-everywhere convergent sequence
whose real energies converge. -/
theorem energy_toReal_le_of_ae_tendsto (hn : 0 < n)
    {p : ℕ → ComplexModel n → EReal} (hp : ∀ j, IsE1 (complexUnitBall n) (p j))
    {v : ComplexModel n → EReal} (hv : IsE1 (complexUnitBall n) v)
    (hAe : ∀ᵐ x ∂(volume : Measure (ComplexModel n)).restrict (complexUnitBall n),
      Tendsto (fun j => p j x) atTop (𝓝 (v x)))
    {E : ℝ} (hE : Tendsto (fun j => (energy (hp j)).toReal) atTop (𝓝 E)) :
    (energy hv).toReal ≤ E := by
  have hE₀ : 0 ≤ E := ge_of_tendsto hE (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hE.eventually_lt_const (lt_add_of_pos_right E hδ))
  let M := ENNReal.ofReal (E + δ)
  have hM (j : ℕ) : energy (hp (j + N)) ≤ M := by
    have h := hN (j + N) (by omega)
    exact (ENNReal.ofReal_toReal (energy_lt_top hn (hp (j + N))).ne) ▸ ENNReal.ofReal_le_ofReal h.le
  have hTail : ∀ᵐ x ∂(volume : Measure (ComplexModel n)).restrict (complexUnitBall n),
      Tendsto (fun j => p (j + N) x) atTop (𝓝 (v x)) :=
    hAe.mono fun _ h => h.comp (tendsto_add_atTop_nat N)
  obtain ⟨w, hw, hwE, heq⟩ := exists_isE1_of_ae_tendsto_of_energy_le hn
    (fun j => hp (j + N)) hTail ENNReal.ofReal_lt_top hM
  have hEqOn := hw.1.eqOn_of_ae_eq hv.1 (complexUnitBall n).isOpen volume heq
  have he := energy_congr hn hw hv hEqOn
  rw [← he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hwE).trans_eq
    (ENNReal.toReal_ofReal (add_nonneg hE₀ hδ.le))

end KEBall.Cegrell
