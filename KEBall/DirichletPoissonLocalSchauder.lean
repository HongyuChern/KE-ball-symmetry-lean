import KEBall.DirichletPoissonSchauder
import KEBall.DirichletPoissonCutoff
import DifferentialGeometry.Analysis.Schauder.Cutoff.Elliptic.Ball
import DifferentialGeometry.Analysis.Schauder.Holder.Bilinear

/-! Local Poisson Schauder estimates for the actual full real Hessian.
Only the function, gradient, and actual Laplacian enter the local data. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

open Filter Metric Set
open scoped ContDiff Laplacian NNReal Topology

noncomputable section
namespace KEBall
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Schauder

theorem exists_uniform_poisson_cutoff_source_holder {n : ℕ} (hn : 0 < n)
    (p : E n) {R : ℝ} (hR : 0 < R)
    (α A G L KU KG KL : ℝ≥0) (hα1 : α ≤ 1) :
    ∃ B K : ℝ≥0, ∀ (u : E n → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ closedBall p R, ‖u x‖ ≤ A) →
      (∀ x ∈ closedBall p R, ‖fderiv ℝ u x‖ ≤ G) →
      (∀ x ∈ closedBall p R, ‖Δ u x‖ ≤ L) →
      HolderOnWith KU α u (closedBall p R) →
      HolderOnWith KG α (fderiv ℝ u) (closedBall p R) →
      HolderOnWith KL α (Δ u) (closedBall p R) →
      let v := fun x => ballCutoff p (R / 2) R x * u x
      (∀ x, ‖v x‖ ≤ A) ∧ (∀ x, ‖Δ v x‖ ≤ B) ∧ HolderWith K α (Δ v) := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  have hr : 0 ≤ R / 2 := by positivity
  have hrR : R / 2 < R := by linarith
  let χ := ballCutoff p (R / 2) R
  have hχ : ContDiff ℝ ∞ χ := DifferentialGeometry.Analysis.ballCutoff_contDiff p (R / 2) R
  let M1 : ℝ≥0 := Real.toNNReal (ballCutoffFDerivBound (R / 2) R)
  let M2 : ℝ≥0 := Real.toNNReal (ballCutoffLaplacianBound (V := E n) (R / 2) R)
  let K0 := ballCutoffHolderConst (R / 2) R
  let K1 := ballCutoffFDerivHolderConst (R / 2) R
  let K2 := ballCutoffLaplacianHolderConst (V := E n) (R / 2) R
  let d : ℝ≥0 := Module.finrank ℝ (E n)
  let B : ℝ≥0 := L + A * M2 + 2 * d * M1 * G
  let Ki : ℝ≥0 := G * K1 + M1 * KG
  let K : ℝ≥0 := (L * K0 + 1 * KL) + (A * K2 + M2 * KU) + (d * Ki + d * Ki)
  have hχNorm (x : E n) : ‖χ x‖ ≤ (1 : ℝ≥0) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc p (R / 2) R x).1]
    exact (ballCutoff_mem_Icc p (R / 2) R x).2
  have hDNorm (x : E n) : ‖fderiv ℝ χ x‖ ≤ M1 := by
    rw [show χ = ballCutoff p (R / 2) R from rfl, fderiv_ballCutoff]
    exact (norm_ballCutoffFDeriv_le hr hrR x).trans (Real.le_coe_toNNReal _)
  have hLNorm (x : E n) : ‖Δ χ x‖ ≤ M2 := by
    rw [show χ = ballCutoff p (R / 2) R from rfl, euclideanLaplacian_ballCutoff,
      Real.norm_eq_abs]
    exact (abs_ballCutoffLaplacian_le hr hrR x).trans (Real.le_coe_toNNReal _)
  have hχH : HolderWith K0 α χ := ballCutoff_holderWith hr hrR (by positivity) hα1
  have hDH : HolderWith K1 α (fderiv ℝ χ) := by
    simpa only [χ, fderiv_ballCutoff] using
      (ballCutoffFDeriv_holderWith (center := p) hr hrR (by positivity) hα1)
  have hLH : HolderWith K2 α (Δ χ) := by
    have heq : Δ χ = ballCutoffLaplacian p (R / 2) R :=
      funext fun x => euclideanLaplacian_ballCutoff p x (R / 2) R
    rw [heq]
    exact ballCutoffLaplacian_holderWith (center := p) hr hrR (by positivity) hα1
  have hOutside (x : E n) (hx : x ∉ closedBall p R) : χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have hd : R < dist x p := not_le.mp hx
    have hopen : IsOpen {y : E n | R < dist y p} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    filter_upwards [hopen.mem_nhds hd] with y hy
    exact ballCutoff_eq_zero_of_le_dist hr hrR hy.le
  have hχZero (x : E n) (hx : x ∉ closedBall p R) : χ x = 0 :=
    (hOutside x hx).self_of_nhds
  have hDZero (x : E n) (hx : x ∉ closedBall p R) : fderiv ℝ χ x = 0 := by
    rw [(hOutside x hx).fderiv_eq, fderiv_const_apply]
  have hLZero (x : E n) (hx : x ∉ closedBall p R) : Δ χ x = 0 := by
    rw [(InnerProductSpace.laplacian_congr_nhds (hOutside x hx)).self_of_nhds]
    simp
  refine ⟨B, K, ?_⟩
  intro u hu hA hG hL hUH hGH hLapH
  let v := fun x => χ x * u x
  have hvA (x : E n) : ‖v x‖ ≤ A := by
    by_cases hx : x ∈ closedBall p R
    · calc
        ‖v x‖ = ‖χ x‖ * ‖u x‖ := norm_mul _ _
        _ ≤ 1 * A := mul_le_mul (hχNorm x) (hA x hx) (norm_nonneg _) (by norm_num)
        _ = A := one_mul _
    · simp only [v, hχZero x hx, zero_mul, norm_zero]
      exact A.coe_nonneg
  have hvL (x : E n) : ‖Δ v x‖ ≤ B := by
    by_cases hx : x ∈ closedBall p R
    · refine (norm_euclideanLaplacian_mul_le hχ hu x).trans ?_
      calc
        _ ≤ 1 * L + A * M2 + 2 * (Module.finrank ℝ (E n) : ℝ) * M1 * G := by
          gcongr
          · exact hχNorm x
          · exact hL x hx
          · exact hA x hx
          · exact hLNorm x
          · exact hDNorm x
          · exact hG x hx
        _ = B := by simp only [B, d, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast,
          NNReal.coe_ofNat, one_mul]
    · have heq : v =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hOutside x hx] with y hy
        simp only [v, hy, zero_mul]
      rw [(InnerProductSpace.laplacian_congr_nhds heq).self_of_nhds]
      simpa using B.coe_nonneg
  have hFirst : HolderWith (L * K0 + 1 * KL) α (fun x => Δ u x * χ x) := by
    exact holderWith_smul_of_restrict_of_support
      (HolderWith.restrict_iff.mpr hLapH) hχH hL hχNorm hχZero
  have hSecond : HolderWith (A * K2 + M2 * KU) α (fun x => u x * Δ χ x) := by
    exact holderWith_smul_of_restrict_of_support
      (HolderWith.restrict_iff.mpr hUH) hLH hA hLNorm hLZero
  let e := stdOrthonormalBasis ℝ (E n)
  have hEval (i : Fin (Module.finrank ℝ (E n))) :
      ‖ContinuousLinearMap.apply ℝ ℝ (e i)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    change ‖T (e i)‖ ≤ 1 * ‖T‖
    simpa only [e, (stdOrthonormalBasis ℝ (E n)).orthonormal.norm_eq_one,
      mul_one, one_mul] using T.le_opNorm (e i)
  have hTerm (i : Fin (Module.finrank ℝ (E n))) :
      HolderWith Ki α (fun x => fderiv ℝ u x (e i) * fderiv ℝ χ x (e i)) := by
    apply holderWith_smul_of_restrict_of_support
    · exact holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply ℝ ℝ (e i)) (hEval i) (HolderWith.restrict_iff.mpr hGH)
    · exact holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply ℝ ℝ (e i)) (hEval i) hDH
    · intro x hx
      have hi := (fderiv ℝ u x).le_opNorm (e i)
      rw [show ‖e i‖ = 1 from (stdOrthonormalBasis ℝ (E n)).orthonormal.norm_eq_one i,
        mul_one] at hi
      exact hi.trans (hG x hx)
    · intro x
      have hi := (fderiv ℝ χ x).le_opNorm (e i)
      rw [show ‖e i‖ = 1 from (stdOrthonormalBasis ℝ (E n)).orthonormal.norm_eq_one i,
        mul_one] at hi
      exact hi.trans (hDNorm x)
    · intro x hx
      rw [hDZero x hx, ContinuousLinearMap.zero_apply]
  have hSum : HolderWith (d * Ki) α
      (fun x => ∑ i : Fin (Module.finrank ℝ (E n)),
        fderiv ℝ u x (e i) * fderiv ℝ χ x (e i)) := by
    simpa only [d, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using
      holderWith_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ (E n))))
        (K := fun _ => Ki) (f := fun i x => fderiv ℝ u x (e i) * fderiv ℝ χ x (e i))
        (fun i _ => hTerm i)
  have hAll := holderWith_add (holderWith_add hFirst hSecond) (holderWith_add hSum hSum)
  refine ⟨hvA, hvL, holderWith_congr hAll ?_⟩
  intro x
  rw [euclideanLaplacian_mul_of_contDiff hχ hu x]
  simp only [Pi.add_apply, e]
  simp_rw [mul_comm (fderiv ℝ u x _) (fderiv ℝ χ x _)]
  ring

theorem exists_uniform_local_poisson_hessian_holder {n : ℕ} (hn : 0 < n)
    (p : E n) {R : ℝ} (hR : 0 < R)
    (α A G L KU KG KL : ℝ≥0) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ (u : E n → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ closedBall p R, ‖u x‖ ≤ A) →
      (∀ x ∈ closedBall p R, ‖fderiv ℝ u x‖ ≤ G) →
      (∀ x ∈ closedBall p R, ‖Δ u x‖ ≤ L) →
      HolderOnWith KU α u (closedBall p R) →
      HolderOnWith KG α (fderiv ℝ u) (closedBall p R) →
      HolderOnWith KL α (Δ u) (closedBall p R) →
      (∀ x ∈ ball p (R / 2), ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C) ∧
        HolderOnWith C α (fderiv ℝ (fderiv ℝ u)) (ball p (R / 2)) := by
  obtain ⟨B, K, hCut⟩ := exists_uniform_poisson_cutoff_source_holder hn p hR α A G L KU KG KL hα1.le
  obtain ⟨C, hS⟩ := exists_uniform_compactSupport_poisson_hessian_holder hn α K B A hα hα1
  refine ⟨C, ?_⟩
  intro u hu hA hG hL hUH hGH hLapH
  let χ := ballCutoff p (R / 2) R
  let v := fun x => χ x * u x
  have hr : 0 ≤ R / 2 := by positivity
  have hrR : R / 2 < R := by linarith
  obtain ⟨hvA, hvL, hvH⟩ := hCut u hu hA hG hL hUH hGH hLapH
  have hv : ContDiff ℝ ∞ v := (DifferentialGeometry.Analysis.ballCutoff_contDiff p (R / 2) R).mul hu
  have hc : HasCompactSupport v :=
    (DifferentialGeometry.Analysis.ballCutoff_hasCompactSupport (center := p) hr hrR).mul_right
  obtain ⟨hNorm, hHolder⟩ := hS v hv hc hvA hvL hvH
  have heq (x : E n) (hx : x ∈ ball p (R / 2)) : v =ᶠ[𝓝 x] u := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have hOne : χ y = 1 := ballCutoff_eq_one_of_mem_closedBall hr hrR (ball_subset_closedBall hy)
    simp only [v, hOne, one_mul]
  have hHess (x : E n) (hx : x ∈ ball p (R / 2)) :
      fderiv ℝ (fderiv ℝ v) x = fderiv ℝ (fderiv ℝ u) x := (heq x hx).fderiv.fderiv_eq
  refine ⟨fun x hx => by simpa only [hHess x hx] using hNorm x, ?_⟩
  intro x hx y hy
  simpa only [hHess x hx, hHess y hy] using hHolder x y

end KEBall
