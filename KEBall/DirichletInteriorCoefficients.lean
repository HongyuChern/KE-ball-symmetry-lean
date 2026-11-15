import KEBall.DirichletInteriorLocalize
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Bounded uniformly elliptic coefficients for the localized interior equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions NNReal Topology

namespace KEBall

/-- A smooth compactly supported field on the real model is globally Lipschitz. -/
theorem exists_lipschitzWith_of_contDiff_hasCompactSupport {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F}
    (hf : ContDiff ℝ ∞ f) (hSupp : HasCompactSupport f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  have hc : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := ∞) (by simp)).continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hSupp.fderiv ℝ)
  let K : ℝ≥0 := ⟨max 0 C, le_max_left _ _⟩
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) fun x => ?_⟩
  exact_mod_cast (hC x).trans (le_max_right 0 C)

set_option maxHeartbeats 600000 in
/-- A smooth cutoff of the given coefficients extends them to bounded
Lipschitz coefficients on the whole space while retaining uniform ellipticity. -/
theorem exists_euclideanCoefficientExtension_with_derivativeSupport {n : ℕ}
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {l : ℝ}
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (η : 𝓓(dirichletBallOpens n, ℝ)) (hη₀ : ∀ x, 0 ≤ η x) :
    ∃ (B : E n → E n →L[ℝ] E n) (K : ℝ≥0), ContDiff ℝ ∞ B ∧
      MemLp B ⊤ (volume0 n) ∧ LipschitzWith K B ∧
      (∀ x, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) ∧
      (∀ x, η x = 1 → B x = A x) ∧
      (∀ d : E n, MemLp (fun x => fderiv ℝ B x d) ⊤ (volume0 n)) ∧
      (∀ d e : E n, MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ B y d) x e) ⊤
        (volume0 n)) ∧
      ∀ d : E n, HasCompactSupport (fun x => fderiv ℝ B x d) := by
  let I : E n →L[ℝ] E n := l • ContinuousLinearMap.id ℝ (E n)
  let F (x : E n) := η x • (A x - I)
  let B (x : E n) := I + F x
  have hF : ContDiff ℝ ∞ F := η.contDiff.smul (hA.sub contDiff_const)
  have hFc : HasCompactSupport F := by
    apply η.hasCompactSupport.mono'
    intro x hx
    by_contra h
    apply hx
    change η x • (A x - I) = 0
    rw [image_eq_zero_of_notMem_tsupport h]
    exact zero_smul ℝ (A x - I)
  have hBC : ContDiff ℝ ∞ B := contDiff_const.add hF
  have hB : MemLp B ⊤ (volume0 n) := by
    have hFtop : MemLp F ⊤ (volume0 n) := hF.continuous.memLp_top_of_hasCompactSupport hFc _
    exact (memLp_top_const (μ := volume0 n) I).add hFtop
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport hF hFc
  have hBLip : LipschitzWith K B := LipschitzWith.of_dist_le_mul fun x y => by
    change dist (I + F x) (I + F y) ≤ (K : ℝ) * dist x y
    rw [dist_add_left]
    exact hK.dist_le_mul x y
  have hDB (d : E n) : (fun x => fderiv ℝ B x d) = fun x => fderiv ℝ F x d := by
    funext x
    exact congrArg (fun T : E n →L[ℝ] (E n →L[ℝ] E n) => T d)
      (fderiv_const_add (f := F) (x := x) I)
  have hDF (d : E n) : ContDiff ℝ ∞ (fun x => fderiv ℝ F x d) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have hD₂F (d e : E n) : ContDiff ℝ ∞
      (fun x => fderiv ℝ (fun y => fderiv ℝ F y d) x e) :=
    ((hDF d).fderiv_right (by simp)).clm_apply contDiff_const
  refine ⟨B, K, hBC, hB, hBLip, ?_, ?_, ?_, ?_, ?_⟩
  · intro x v
    have hI : inner ℝ (I v) v = l * ‖v‖ ^ 2 := by
      change inner ℝ ((l • ContinuousLinearMap.id ℝ (E n)) v) v = _
      rw [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
    by_cases hx : x ∈ unitBall n
    · have hExpr : inner ℝ (B x v) v =
          l * ‖v‖ ^ 2 + η x * (inner ℝ (A x v) v - l * ‖v‖ ^ 2) := by
        change inner ℝ (I v + η x • (A x v - I v)) v = _
        rw [inner_add_left, real_inner_smul_left, inner_sub_left, hI]
      rw [hExpr]
      exact le_add_of_nonneg_right (mul_nonneg (hη₀ x) (sub_nonneg.mpr (hE x hx v)))
    · have hz : η x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hs => hx (η.tsupport_subset hs))
      have hAt : B x = I := by
        change I + η x • (A x - I) = I
        rw [hz, zero_smul ℝ (A x - I), add_zero]
      rw [hAt, hI]
  · intro x hx
    change I + η x • (A x - I) = A x
    rw [hx, one_smul]
    abel
  · intro d
    rw [hDB d]
    exact (hDF d).continuous.memLp_top_of_hasCompactSupport (hFc.fderiv_apply ℝ d) _
  · intro d e
    simp_rw [hDB d]
    exact (hD₂F d e).continuous.memLp_top_of_hasCompactSupport
      ((hFc.fderiv_apply ℝ d).fderiv_apply ℝ e) _
  · intro d
    rw [hDB d]
    exact hFc.fderiv_apply ℝ d

/-- A smooth cutoff of the given coefficients extends them to bounded
Lipschitz coefficients on the whole space while retaining uniform ellipticity. -/
theorem exists_euclideanCoefficientExtension_with_derivatives {n : ℕ}
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {l : ℝ}
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (η : 𝓓(dirichletBallOpens n, ℝ)) (hη₀ : ∀ x, 0 ≤ η x) :
    ∃ (B : E n → E n →L[ℝ] E n) (K : ℝ≥0), ContDiff ℝ ∞ B ∧
      MemLp B ⊤ (volume0 n) ∧ LipschitzWith K B ∧
      (∀ x, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) ∧
      (∀ x, η x = 1 → B x = A x) ∧
      (∀ d : E n, MemLp (fun x => fderiv ℝ B x d) ⊤ (volume0 n)) ∧
      ∀ d e : E n, MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ B y d) x e) ⊤
        (volume0 n) := by
  obtain ⟨B, K, hBC, hB, hLip, hE, hEq, hD₁, hD₂, _⟩ :=
    exists_euclideanCoefficientExtension_with_derivativeSupport hA hE η hη₀
  exact ⟨B, K, hBC, hB, hLip, hE, hEq, hD₁, hD₂⟩

theorem exists_euclideanCoefficientExtension {n : ℕ}
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {l : ℝ}
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (η : 𝓓(dirichletBallOpens n, ℝ)) (hη₀ : ∀ x, 0 ≤ η x) :
    ∃ (B : E n → E n →L[ℝ] E n) (K : ℝ≥0), ContDiff ℝ ∞ B ∧
      MemLp B ⊤ (volume0 n) ∧ LipschitzWith K B ∧
      (∀ x, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) ∧
      ∀ x, η x = 1 → B x = A x := by
  obtain ⟨B, K, hBC, hB, hBLip, hBE, hEq, _, _⟩ :=
    exists_euclideanCoefficientExtension_with_derivatives hA hE η hη₀
  exact ⟨B, K, hBC, hB, hBLip, hBE, hEq⟩

/-- A cutoff equal to one near the center gives a globally elliptic
whole-space equation with L² forcing. -/
theorem IsDirichletWeakSolution.exists_interior_cutoff_with_derivativeSupport {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x)
    {l : ℝ}
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u) :
    ∃ (χ η : 𝓓(dirichletBallOpens n, ℝ)) (B : E n → E n →L[ℝ] E n)
      (K : ℝ≥0) (hB : MemLp B ⊤ (volume0 n)) (f' : DirichletBallL2 n ℝ),
      (∀ x ∈ closedBall (0 : E n) (1 / 2), χ x = 1) ∧
      (∀ x ∈ tsupport (χ : E n → ℝ), (η : E n → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ)) ∧
      ContDiff ℝ ∞ B ∧
      (∀ x v, l * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) ∧ LipschitzWith K B ∧
      (∀ d : E n, MemLp (fun x => fderiv ℝ B x d) ⊤ (volume0 n)) ∧
      (∀ d e : E n, MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ B y d) x e) ⊤
        (volume0 n)) ∧
      (∀ d : E n, HasCompactSupport (fun x => fderiv ℝ B x d)) ∧
      f' =ᵐ[(volume0 n).restrict (unitBall n)] dirichletCutoffForcing b A χ g u ∧
      IsEuclideanWeakSolution hB (dirichletL2ZeroExtension f')
        (euclideanSobolevCutoff χ (dirichletSobolevZeroExtension n u)) := by
  let p : ContDiffBump (0 : E n) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  let q : ContDiffBump (0 : E n) := ⟨13 / 16, 7 / 8, by norm_num, by norm_num⟩
  have hp : tsupport (p : E n → ℝ) ⊆ unitBall n := by
    rw [p.tsupport_eq]
    exact closedBall_subset_ball (show p.rOut < (1 : ℝ) by norm_num [p])
  have hq : tsupport (q : E n → ℝ) ⊆ unitBall n := by
    rw [q.tsupport_eq]
    exact closedBall_subset_ball (show q.rOut < (1 : ℝ) by norm_num [q])
  let χ : 𝓓(dirichletBallOpens n, ℝ) := ⟨p, p.contDiff, p.hasCompactSupport, hp⟩
  let η : 𝓓(dirichletBallOpens n, ℝ) := ⟨q, q.contDiff, q.hasCompactSupport, hq⟩
  obtain ⟨B, K, hBC, hB, hLip, hBE, hEq, hD₁, hD₂, hSupp⟩ :=
    exists_euclideanCoefficientExtension_with_derivativeSupport hA hE η (fun _ => q.nonneg)
  have hη (x : E n) (hx : x ∈ tsupport (χ : E n → ℝ)) :
      (η : E n → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    have hq₀ : x ∈ ball (0 : E n) q.rIn := by
      change x ∈ tsupport (p : E n → ℝ) at hx
      rw [p.tsupport_eq] at hx
      exact closedBall_subset_ball (show p.rOut < q.rIn by norm_num [p, q]) hx
    filter_upwards [isOpen_ball.mem_nhds hq₀] with y hy
    exact q.one_of_mem_closedBall (ball_subset_closedBall hy)
  have hAgree (x : E n) (hx : x ∈ tsupport (χ : E n → ℝ)) : B x = A x :=
    hEq x (Filter.EventuallyEq.eq_of_nhds (hη x hx))
  obtain ⟨f', hf', hG⟩ := hu.exists_wholeCutoff_with_forcing hn b hA hSym hB χ hAgree
  exact ⟨χ, η, B, K, hB, f', fun x hx => p.one_of_mem_closedBall hx, hη, hBC,
    hBE, hLip, hD₁, hD₂, hSupp, hf', hG⟩

/-- A cutoff equal to one near the center gives a globally elliptic
whole-space equation with L² forcing. -/
theorem IsDirichletWeakSolution.exists_interior_cutoff_with_forcing {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x)
    {l : ℝ}
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u) :
    ∃ (χ η : 𝓓(dirichletBallOpens n, ℝ)) (B : E n → E n →L[ℝ] E n)
      (K : ℝ≥0) (hB : MemLp B ⊤ (volume0 n)) (f' : DirichletBallL2 n ℝ),
      (∀ x ∈ closedBall (0 : E n) (1 / 2), χ x = 1) ∧
      (∀ x ∈ tsupport (χ : E n → ℝ), (η : E n → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ)) ∧
      ContDiff ℝ ∞ B ∧
      (∀ x v, l * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) ∧ LipschitzWith K B ∧
      (∀ d : E n, MemLp (fun x => fderiv ℝ B x d) ⊤ (volume0 n)) ∧
      (∀ d e : E n, MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ B y d) x e) ⊤
        (volume0 n)) ∧
      f' =ᵐ[(volume0 n).restrict (unitBall n)] dirichletCutoffForcing b A χ g u ∧
      IsEuclideanWeakSolution hB (dirichletL2ZeroExtension f')
        (euclideanSobolevCutoff χ (dirichletSobolevZeroExtension n u)) := by
  obtain ⟨χ, η, B, K, hB, f', hχ, hη, hBC, hBE, hLip, hD₁, hD₂, _, hf', hG⟩ :=
    hu.exists_interior_cutoff_with_derivativeSupport hn b hA hSym hE
  exact ⟨χ, η, B, K, hB, f', hχ, hη, hBC, hBE, hLip, hD₁, hD₂, hf', hG⟩

/-- A cutoff equal to one near the center gives a globally elliptic
whole-space equation with L² forcing. -/
theorem IsDirichletWeakSolution.exists_interior_cutoff {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x)
    {l : ℝ}
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u) :
    ∃ (χ : 𝓓(dirichletBallOpens n, ℝ)) (B : E n → E n →L[ℝ] E n)
      (K : ℝ≥0) (hB : MemLp B ⊤ (volume0 n)) (g' : EuclideanL2 n ℝ),
      (∀ x ∈ closedBall (0 : E n) (1 / 2), χ x = 1) ∧
      (∀ x v, l * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) ∧ LipschitzWith K B ∧
      IsEuclideanWeakSolution hB g' (euclideanSobolevCutoff χ (dirichletSobolevZeroExtension n u)) := by
  obtain ⟨χ, _, B, K, hB, f', hχ, _, _, hBE, hLip, _, _, _, hEq⟩ :=
    hu.exists_interior_cutoff_with_forcing hn b hA hSym hE
  exact ⟨χ, B, K, hB, dirichletL2ZeroExtension f', hχ, hBE, hLip, hEq⟩

end KEBall
