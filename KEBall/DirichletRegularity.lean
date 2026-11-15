import KEBall.DirichletWholeLocalizedRegularity
import KEBall.DirichletWeakSobolevBootstrap

/-! Finite-order weak elliptic regularity up to the boundary of the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)
local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)

private noncomputable def dirichletTestToWhole {n : ℕ} (ψ : 𝓓B[n]) : 𝓓E[n] :=
  ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_univ _⟩

private theorem dirichletTestToWhole_lineDerivative {n : ℕ} (ψ : 𝓓B[n]) (d : E n) :
    dirichletTestToWhole (dirichletTestLineDerivative d ψ) =
      euclideanTestLineDerivative d (dirichletTestToWhole ψ) := by
  apply TestFunction.ext
  intro x
  rw [euclideanTest_lineDeriv_apply]
  rfl

private theorem dirichletWeakDerivativeTest_eq_whole_on {n : ℕ} {f F : E n → ℝ}
    {s : Set (E n)}
    (he : ∀ ψ : 𝓓B[n], tsupport (ψ : E n → ℝ) ⊆ s →
      (∫ x, ψ x * f x ∂ν[n]) = ∫ x, dirichletTestToWhole ψ x * F x ∂volume0 n)
    (ds : List (E n)) (ψ : 𝓓B[n]) (hψ : tsupport (ψ : E n → ℝ) ⊆ s) :
    dirichletWeakDerivativeTest f ds ψ =
      euclideanWeakDerivativeTest F ds (dirichletTestToWhole ψ) := by
  induction ds generalizing ψ with
  | nil => exact he ψ hψ
  | cons d ds ih =>
      have hD : tsupport (dirichletTestLineDerivative d ψ : E n → ℝ) ⊆
          tsupport (ψ : E n → ℝ) :=
        tsupport_fderiv_apply_subset ℝ d
      simp only [dirichletWeakDerivativeTest, euclideanWeakDerivativeTest,
        ih _ (hD.trans hψ), dirichletTestToWhole_lineDerivative]

/-- In the interior, any finite order of the forcing controls two more
weak derivatives of the solution, given the preceding global order. -/
theorem IsDirichletWeakSolution.exists_dirichletDistributionalDerivativeL2_interior
    {n : ℕ} (hn : 0 < n) (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (k : ℕ) (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) k)
    (hU : HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 1))
    (ds : List (E n)) (e : E n) (hds : ds.length ≤ k + 1) :
    ∃ R : E n → ℝ, MemLp R 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      tsupport (ψ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2) →
      dirichletDistributionalDerivative u (ds ++ [e]) ψ = ∫ x, ψ x * R x ∂ν[n] := by
  obtain ⟨χ, η, B, K, hB, f', hχ, hη, hBc, hBE, hLip, _, _, hSupp, hf', hEq⟩ :=
    hu.exists_interior_cutoff_with_derivativeSupport hn b hA hSym hE
  have hF := hasEuclideanWeakDerivativesL2_dirichletCutoffForcing hn b k hA hU hg χ η
    (fun x hx => (hη x hx).eq_of_nhds) f' hf'
  let z := dirichletSobolevZeroExtension n u
  let w := euclideanSobolevCutoff χ z
  let f (x : E n) := inner ℝ e ((u : DirichletBallL2Pair n).snd x)
  let F (x : E n) := inner ℝ e ((w : EuclideanL2Pair n).snd x)
  have hReg : HasEuclideanWeakDerivativesL2 F (k + 1) :=
    hEq.hasEuclideanWeakGradientDerivativesL2 b hBc
      (memLp_iteratedLineDerivative_of_derivativeSupport hBc hB hSupp)
      hl (Eventually.of_forall hBE) hLip k hF e
  obtain ⟨R, hR, heR⟩ := hReg.2 ds hds
  refine ⟨R, hR.restrict _, fun ψ hψ => ?_⟩
  have hPair (φ : 𝓓B[n]) (hφ : tsupport (φ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2)) :
      (∫ x, φ x * f x ∂ν[n]) = ∫ x, dirichletTestToWhole φ x * F x ∂volume0 n := by
    rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
    apply integral_congr_ae
    filter_upwards [euclideanSobolevCutoff_gradient_ae χ z, dirichletSobolevZeroExtension_gradient_ae u]
      with x hw hz
    change (z : EuclideanL2Pair n).snd x =
      (unitBall n).indicator (fun y => (u : DirichletBallL2Pair n).snd y) x at hz
    change (unitBall n).indicator (fun y => φ y * f y) x = φ x * F x
    by_cases hs : x ∈ tsupport (φ : E n → ℝ)
    · have hb : x ∈ unitBall n := φ.tsupport_subset hs
      have hNear : (χ : E n → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_ball.mem_nhds (hφ hs)] with y hy
        exact hχ y (ball_subset_closedBall hy)
      have hzχ : ∇ (χ : E n → ℝ) x = 0 := by
        apply ext_inner_right ℝ
        intro y
        rw [inner_gradient_left, inner_zero_left, hNear.fderiv_eq, fderiv_fun_const, Pi.zero_apply, zero_apply]
      change (w : EuclideanL2Pair n).snd x = _ at hw
      simp only [F, f, indicator_of_mem hb, hw, hz, hNear.eq_of_nhds, hzχ, one_smul, smul_zero, add_zero]
    · have hzφ := image_eq_zero_of_notMem_tsupport hs
      by_cases hb : x ∈ unitBall n <;> simp [indicator_of_mem, indicator_of_notMem, hb, hzφ]
  have hSingle (φ : 𝓓B[n]) :
      dirichletDistributionalDerivative u [e] φ = ∫ x, φ x * f x ∂ν[n] :=
    dirichletDistributionalDerivative_singleton u e φ
  rw [show dirichletDistributionalDerivative u (ds ++ [e]) ψ =
    dirichletWeakDerivativeTest f ds ψ from dirichletWeakDerivativeTest_append_singleton e hSingle ds ψ]
  rw [dirichletWeakDerivativeTest_eq_whole_on hPair ds ψ hψ, heR (dirichletTestToWhole ψ)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (ψ.tsupport_subset hs)), zero_mul]

/-- Smooth uniformly elliptic coefficients give two orders of L² regularity
on the whole ball for forcing of any finite weak order. -/
theorem IsDirichletWeakSolution.hasDirichletWeakDerivativesL2
    {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    (k : ℕ) {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A g u)
    (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) k) :
    HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2) := by
  induction k generalizing g u with
  | zero =>
      let f := (u : DirichletBallL2Pair n).fst
      let U := (u : DirichletBallL2Pair n).snd
      apply HasDirichletWeakDerivativesL2.of_coordinate_tests hn b (Lp.memLp f)
      intro is hLen
      match is with
      | [] => exact ⟨f, Lp.memLp f, fun _ => rfl⟩
      | [i] => exact ⟨fun x => inner ℝ (b i) (U x), (Lp.memLp U).const_inner (b i),
          dirichletDistributionalDerivative_singleton u (b i)⟩
      | [j, i] =>
          obtain ⟨R, hR, heR⟩ := exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE
            hLipA hM₀ hM hu i j
          exact ⟨R, hR, fun ψ => (dirichletDistributionalDerivative_pair u (b j) (b i) ψ).trans (heR ψ)⟩
      | _ :: _ :: _ :: _ =>
          simp only [List.length_cons] at hLen
          omega
  | succ k ih =>
      have hg₀ : HasDirichletWeakDerivativesL2 (g : E n → ℝ) k :=
        ⟨hg.1, fun ds hs => hg.2 ds (hs.trans (Nat.le_succ _))⟩
      have hU := ih hu hg₀
      apply hu.hasDirichletWeakDerivativesL2_succ_of_interior hn b hA hAc hSym hl hE hLipA hM₀ hM
        k (fun _ _ hw hf => ih hw hf) hg
      intro is hLen
      induction is using List.reverseRecOn with
      | nil => simp at hLen
      | append_singleton is i =>
          have hLen' : (is.map b).length ≤ (k + 1) + 1 := by
            simp only [List.length_append, List.length_singleton] at hLen
            simp only [List.length_map]
            omega
          simpa only [List.map_append, List.map_cons, List.map_nil] using
            hu.exists_dirichletDistributionalDerivativeL2_interior hn b hAc (fun x _ => hSym x)
              hl hE (k + 1) hg hU (is.map b) (b i) hLen'

end KEBall
