import KEBall.DirichletScalarOscillation
import KEBall.DirichletOscillationPower
import KEBall.DirichletOscillationGeometric

/-! All-radius power decay for a uniformly bounded continuous scalar family. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter MeasureTheory Metric Set
open scoped BigOperators Topology

noncomputable section
namespace KEBall

theorem dirichletScalarFamilyOscillation_entry_nonneg {n m : ℕ}
    {q : Fin m → E n → ℝ} (hq : ∀ i, ContinuousOn (q i) (closedUnitBall n))
    {x₀ : E n} {r : ℝ} (hr : 0 < r) (hBall : ball x₀ r ⊆ unitBall n) (i : Fin m) :
    0 ≤ essSup (q i) (volume.restrict (ball x₀ r)) -
      essInf (q i) (volume.restrict (ball x₀ r)) := by
  have he := dirichlet_continuous_scalar_between_essential_bounds
    (hq i) hBall (mem_ball_self hr)
  exact sub_nonneg.mpr (he.1.trans he.2)

theorem dirichletScalarFamilyOscillation_entry_le {n m : ℕ}
    {q : Fin m → E n → ℝ} (hq : ∀ i, ContinuousOn (q i) (closedUnitBall n))
    {x₀ : E n} {r : ℝ} (hr : 0 < r) (hBall : ball x₀ r ⊆ unitBall n) (i : Fin m) :
    essSup (q i) (volume.restrict (ball x₀ r)) -
      essInf (q i) (volume.restrict (ball x₀ r)) ≤
        dirichletScalarFamilyOscillation q x₀ r :=
  Finset.single_le_sum (fun k _ => dirichletScalarFamilyOscillation_entry_nonneg hq hr hBall k)
    (Finset.mem_univ i)

theorem dirichletScalarFamilyOscillation_mono {n m : ℕ}
    {q : Fin m → E n → ℝ} (hq : ∀ i, ContinuousOn (q i) (closedUnitBall n))
    {x₀ : E n} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hBall : ball x₀ R ⊆ unitBall n) :
    dirichletScalarFamilyOscillation q x₀ r ≤ dirichletScalarFamilyOscillation q x₀ R := by
  letI : NeZero ((volume : Measure (E n)).restrict (ball x₀ r)) :=
    ⟨fun h => (measure_ball_pos volume x₀ hr).ne' (Measure.restrict_eq_zero.mp h)⟩
  have hSub : ball x₀ r ⊆ ball x₀ R := ball_subset_ball hrR
  have hMeas : (volume : Measure (E n)).restrict (ball x₀ r) ≤ volume.restrict (ball x₀ R) :=
    Measure.restrict_mono_set volume hSub
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨hHi, hLo⟩ := boundedUnder_dirichlet_continuous_scalar_ball (hq i) hBall
  obtain ⟨hsHi, hsLo⟩ := boundedUnder_dirichlet_continuous_scalar_ball (hq i) (hSub.trans hBall)
  exact sub_le_sub
    (essSup_mono_measure' hMeas hsLo.isCoboundedUnder_le hHi)
    (essInf_antitone_measure (Measure.absolutelyContinuous_of_le hMeas) hLo hsHi.isCoboundedUnder_ge)

theorem dirichletScalarFamilyOscillation_bound {n m : ℕ}
    {q : Fin m → E n → ℝ} (hq : ∀ i, ContinuousOn (q i) (closedUnitBall n))
    (B : Fin m → ℝ)
    (hBound : ∀ i x, x ∈ unitBall n → |q i x| ≤ B i)
    {x₀ : E n} {r : ℝ} (hr : 0 < r) (hBall : ball x₀ r ⊆ unitBall n) :
    dirichletScalarFamilyOscillation q x₀ r ≤ ∑ i : Fin m, 2 * B i := by
  letI : NeZero ((volume : Measure (E n)).restrict (ball x₀ r)) :=
    ⟨fun h => (measure_ball_pos volume x₀ hr).ne' (Measure.restrict_eq_zero.mp h)⟩
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨hHi, hLo⟩ := boundedUnder_dirichlet_continuous_scalar_ball (hq i) hBall
  have he : ∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ r),
      -(B i) ≤ q i x ∧ q i x ≤ B i := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
    exact abs_le.mp (hBound i x (hBall hx))
  have hs := essSup_le_of_ae_le _ (he.mono fun _ h => h.2) hLo.isCoboundedUnder_le
  have hi := le_essInf_of_ae_le _ (he.mono fun _ h => h.1) hHi.isCoboundedUnder_ge
  linarith only [hs, hi]

theorem exists_uniform_dirichlet_scalar_oscillation_power {n m : ℕ} {J : Type*}
    (q : J → Fin m → E n → ℝ)
    (hq : ∀ j i, ContinuousOn (q j i) (closedUnitBall n))
    (B : Fin m → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hBound : ∀ j i x, x ∈ unitBall n → |q j i x| ≤ B i)
    {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hStep : ∀ j (x₀ : E n) (R : ℝ),
      0 < R → R ≤ 1 → closedBall x₀ R ⊆ unitBall n →
      dirichletScalarFamilyOscillation (q j) x₀ (R / 4) ≤
        θ * dirichletScalarFamilyOscillation (q j) x₀ R + C * R) :
    ∃ α D : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ D ∧
      ∀ j (x₀ : E n) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 → closedBall x₀ R₀ ⊆ unitBall n →
        ∀ r : ℝ, 0 < r → r ≤ R₀ →
          dirichletScalarFamilyOscillation (q j) x₀ r ≤
            (D * (4 / R₀ : ℝ) ^ α) * r ^ α := by
  let M : ℝ := ∑ i : Fin m, 2 * B i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num) (hB i)
  obtain ⟨τ, D, hτ0, hτ1, hD, hBudget⟩ :=
    exists_dirichlet_oscillation_geometric_budget hθ0 hθ1 hC hM
  obtain ⟨α, hα0, hα1, hτα⟩ := exists_dirichlet_decay_exponent hτ0 hτ1
  refine ⟨α, D, hα0, hα1, hD, ?_⟩
  intro j x₀ R₀ hR₀ hR₀1 hBall
  let r : ℕ → ℝ := fun k => R₀ * (1 / 4 : ℝ) ^ k
  let o : ℕ → ℝ := fun k => dirichletScalarFamilyOscillation (q j) x₀ (r k)
  have hrPos (k : ℕ) : 0 < r k := mul_pos hR₀ (pow_pos (by norm_num) _)
  have hrLe (k : ℕ) : r k ≤ R₀ :=
    mul_le_of_le_one_right hR₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hrBall (k : ℕ) : closedBall x₀ (r k) ⊆ unitBall n :=
    (closedBall_subset_closedBall (hrLe k)).trans hBall
  have hInitial : o 0 ≤ M := by
    simpa only [o, r, pow_zero, mul_one] using
      dirichletScalarFamilyOscillation_bound (hq j) B (hBound j) hR₀ (ball_subset_closedBall.trans hBall)
  have hRec (k : ℕ) : o (k + 1) ≤ θ * o k + C * (1 / 4 : ℝ) ^ k := by
    have hRadius : r (k + 1) = r k / 4 := by dsimp only [r]; rw [pow_succ]; ring
    have h := hStep j x₀ (r k) (hrPos k) ((hrLe k).trans hR₀1) (hrBall k)
    change dirichletScalarFamilyOscillation (q j) x₀ (r (k + 1)) ≤ _
    rw [hRadius]
    apply h.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ hC
    exact mul_le_of_le_one_left (pow_nonneg (by norm_num) _) hR₀1
  have hGeo := hBudget o hInitial hRec
  intro s hs hsR
  apply dirichlet_power_bound_of_geometric
    (fun a => dirichletScalarFamilyOscillation (q j) x₀ a) hR₀ hD hτ0.le hα0.le hτα ?_
      hGeo hs hsR
  intro a b ha hab hb
  exact dirichletScalarFamilyOscillation_mono (hq j) ha hab
    ((ball_subset_ball hb).trans (ball_subset_closedBall.trans hBall))

end KEBall
