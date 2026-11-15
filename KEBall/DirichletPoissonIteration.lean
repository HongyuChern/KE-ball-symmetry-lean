import KEBall.DirichletPoissonInterior

/-! Absorption of a quadratic previous-gradient Poisson bound along an
iteration with a uniform modulus and a linear boundary barrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

open Filter Metric Set
open scoped ContDiff Laplacian Topology

noncomputable section

namespace KEBall

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- A genuine induction: the previous iterate's gradient bound is an input to
the Poisson bound, while the conclusion gives one bound for every iterate. -/
theorem exists_uniform_gradient_bound_of_poisson_iteration
    {u : ℕ → V → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    {b T : ℝ} (hb : 0 ≤ b) (hT : 0 < T)
    (hbar : ∀ j x, x ∈ closedBall (0 : V) 1 → ‖u (j + 1) x‖ ≤ b * (1 - ‖x‖))
    (hboundary : ∀ j x, x ∈ sphere (0 : V) 1 → ‖fderiv ℝ (u (j + 1)) x‖ ≤ b)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ j : ℕ,
      ∀ x ∈ closedBall (0 : V) 1, ∀ y ∈ closedBall (0 : V) 1,
        dist x y < η → dist (u (j + 1) x) (u (j + 1) y) < ε)
    (hrec : ∀ j (G : ℝ), 0 ≤ G →
      (∀ x ∈ closedBall (0 : V) 1, ‖fderiv ℝ (u j) x‖ ≤ G) →
      ∀ x ∈ ball (0 : V) 1, ‖Δ (u (j + 1)) x‖ ≤ T * (1 + G ^ 2)) :
    ∃ N : ℝ, 0 < N ∧ ∀ j x, x ∈ closedBall (0 : V) 1 → ‖fderiv ℝ (u j) x‖ ≤ N := by
  obtain ⟨C, hC, hlocal⟩ := exists_local_poisson_gradient_constant (V := V)
  let δ : ℝ := 1 / (8 * C * T + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : 8 * C * T * δ < 1 := by
    have hid : (8 * C * T + 1) * δ = 1 := by
      dsimp [δ]
      field_simp
    nlinarith only [hid, hδ]
  let ε : ℝ := δ / (4 * C)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨η, hη, hηmod⟩ := hmod ε hε
  have hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  have hnonempty : (closedBall (0 : V) (1 : ℝ)).Nonempty := ⟨0, by simp⟩
  obtain ⟨x₀, hx₀, hmax₀⟩ := hcompact.exists_isMaxOn hnonempty
    ((hu 0).fderiv_right (m := ∞) (by simp)).continuous.norm.continuousOn
  let G₀ : ℝ := ‖fderiv ℝ (u 0) x₀‖
  have hG₀ : 0 ≤ G₀ := norm_nonneg _
  let N : ℝ := 1 + G₀ + b + 4 * C * b + 2 * δ / η
  have hCb : 0 ≤ 4 * C * b := by positivity
  have hδη : 0 ≤ 2 * δ / η := by positivity
  have hN1 : 1 ≤ N := by dsimp [N]; linarith only [hG₀, hb, hCb, hδη]
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have hNG : G₀ ≤ N := by dsimp [N]; linarith only [hb, hCb, hδη]
  have hNb : b ≤ N := by dsimp [N]; linarith only [hG₀, hCb, hδη]
  have hNCb : 4 * C * b ≤ N := by dsimp [N]; linarith only [hG₀, hb, hδη]
  have hNη : 2 * δ / η ≤ N := by dsimp [N]; linarith only [hG₀, hb, hCb]
  refine ⟨N, hN0, ?_⟩
  intro j
  induction j with
  | zero =>
    intro x hx
    exact (show ‖fderiv ℝ (u 0) x‖ ≤ G₀ from hmax₀ hx).trans hNG
  | succ j ih =>
    obtain ⟨y, hy, hmax⟩ := hcompact.exists_isMaxOn hnonempty
      ((hu (j + 1)).fderiv_right (m := ∞) (by simp)).continuous.norm.continuousOn
    let M : ℝ := ‖fderiv ℝ (u (j + 1)) y‖
    by_cases hMN : M ≤ N
    · exact fun x hx => (show ‖fderiv ℝ (u (j + 1)) x‖ ≤ M from hmax hx).trans hMN
    have hNM : N < M := not_le.mp hMN
    have hM : 0 < M := hN0.trans hNM
    have hM1 : 1 ≤ M := hN1.trans hNM.le
    have hyn : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
    have hylt : ‖y‖ < 1 := by
      rcases hyn.lt_or_eq with hlt | heq
      · exact hlt
      · have hbd := hboundary j y (mem_sphere_zero_iff_norm.mpr heq)
        exact False.elim (hNM.not_ge (hbd.trans hNb))
    let d : ℝ := 1 - ‖y‖
    have hd : 0 < d := sub_pos.mpr hylt
    let r : ℝ := min (d / 2) (δ / M)
    have hr : 0 < r := lt_min (half_pos hd) (div_pos hδ hM)
    have hrd : r ≤ d / 2 := min_le_left _ _
    have hrδ : r ≤ δ / M := min_le_right _ _
    have hrM : r * M ≤ δ := (le_div_iff₀ hM).mp hrδ
    have hrη : r < η := by
      have hnη := (div_le_iff₀ hη).mp hNη
      have hnmη := mul_lt_mul_of_pos_right hNM hη
      have hdη : δ < η * M := by nlinarith only [hnη, hnmη, hδ]
      exact hrδ.trans_lt ((div_lt_iff₀ hM).mpr hdη)
    have hsub : closedBall y r ⊆ ball (0 : V) 1 := by
      intro z hz
      have hz' : dist z y ≤ r := hz
      have ht := dist_triangle z y (0 : V)
      simp only [dist_zero_right] at ht
      apply mem_ball_zero_iff.mpr
      have hrd' : r ≤ (1 - ‖y‖) / 2 := hrd
      linarith only [ht, hz', hrd', hylt]
    let L : ℝ := T * (1 + N ^ 2)
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hLap (z : V) (hz : z ∈ closedBall y r) : ‖Δ (u (j + 1)) z‖ ≤ L :=
      hrec j N hN0.le ih z (hsub hz)
    have hN2 : N ^ 2 ≤ M ^ 2 := (sq_le_sq₀ hN0.le hM.le).mpr hNM.le
    have hM2 : 1 ≤ M ^ 2 := by nlinarith only [hM1]
    have hLB : L ≤ 2 * T * M ^ 2 := by
      have h := mul_le_mul_of_nonneg_left
        (show 1 + N ^ 2 ≤ 2 * M ^ 2 by linarith only [hN2, hM2]) hT.le
      dsimp [L]
      nlinarith only [h]
    have hSource : C * r * L < M / 4 := by
      calc
        C * r * L ≤ C * r * (2 * T * M ^ 2) :=
          mul_le_mul_of_nonneg_left hLB (by positivity)
        _ = 2 * C * T * (r * M) * M := by ring
        _ ≤ 2 * C * T * δ * M :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrM (by positivity)) hM.le
        _ < M / 4 := by
          have h := mul_lt_mul_of_pos_right hδsmall hM
          nlinarith only [h]
    have hcontr : False := by
      rcases le_total (d / 2) (δ / M) with hcase | hcase
      · have hrEq : r = d / 2 := min_eq_left hcase
        have hAmp (z : V) (hz : z ∈ closedBall y r) : ‖u (j + 1) z‖ ≤ 3 * b * r := by
          have ht := dist_triangle y z (0 : V)
          simp only [dist_zero_right, dist_comm y z] at ht
          have hz' : dist z y ≤ r := hz
          have hdr : d = 2 * r := by linarith only [hrEq]
          have hdist : 1 - ‖z‖ ≤ 3 * r := by
            have hdid : d = 1 - ‖y‖ := rfl
            linarith only [ht, hz', hdr, hdid]
          calc
            ‖u (j + 1) z‖ ≤ b * (1 - ‖z‖) := hbar j z (ball_subset_closedBall (hsub hz))
            _ ≤ b * (3 * r) := mul_le_mul_of_nonneg_left hdist hb
            _ = 3 * b * r := by ring
        have hloc := hlocal (u (j + 1)) (hu (j + 1)) y r (3 * b * r) L
          hr (by positivity) hL hAmp hLap
        have heq : C * (3 * b * r / r + r * L) = 3 * C * b + C * r * L := by
          field_simp [hr.ne'] <;> ring
        rw [heq] at hloc
        change M ≤ 3 * C * b + C * r * L at hloc
        nlinarith only [hloc, hNCb, hNM, hSource]
      · have hrEq : r = δ / M := min_eq_right hcase
        let v : V → ℝ := fun z => u (j + 1) z - u (j + 1) y
        have hv : ContDiff ℝ ∞ v := (hu (j + 1)).sub contDiff_const
        have hfirst : fderiv ℝ v = fderiv ℝ (u (j + 1)) :=
          funext fun z => fderiv_sub_const (u (j + 1) y)
        have hLapEq (z : V) : Δ v z = Δ (u (j + 1)) z := by
          simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
            iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hfirst]
        have hAmp (z : V) (hz : z ∈ closedBall y r) : ‖v z‖ ≤ ε := by
          change ‖u (j + 1) z - u (j + 1) y‖ ≤ ε
          rw [← dist_eq_norm]
          exact (hηmod j z (ball_subset_closedBall (hsub hz)) y hy
            ((show dist z y ≤ r from hz).trans_lt hrη)).le
        have hloc := hlocal v hv y r ε L hr hε.le hL hAmp
          (fun z hz => by rw [hLapEq]; exact hLap z hz)
        rw [hfirst] at hloc
        change M ≤ C * (ε / r + r * L) at hloc
        have hamp : C * (ε / r) = M / 4 := by
          rw [hrEq]
          dsimp [ε]
          field_simp [hC.ne', hδ.ne', hM.ne'] <;> ring
        rw [mul_add, hamp] at hloc
        nlinarith only [hloc, hSource, hM]
    exact hcontr.elim

end KEBall
