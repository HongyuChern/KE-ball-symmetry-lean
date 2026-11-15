import KEBall.DirichletUniformEllipticApproximation
import KEBall.DirichletLinearizedHessianCoercivity
import KEBall.DirichletRotationCofactorEquation
import KEBall.DirichletBoundedBilinear

/-!
# Global Hessian coercivity for actual closed-ball C2 potentials

Both the coefficient potential and the test potential are allowed to be
only C2 on the closed ball, with smoothness in the open ball.  The proof
passes to zero-boundary smooth approximants in all actual second jets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

noncomputable section

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

def dirichletWithinRealHessian {n : ℕ} (u : E n → ℝ) :
    E n → E n →L[ℝ] E n →L[ℝ] ℝ :=
  fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n)

theorem continuousOn_dirichletWithinRealHessian {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) :
    ContinuousOn (dirichletWithinRealHessian u) (closedUnitBall n) := by
  have hU : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  exact ((hu.fderivWithin (m := 1) hU (by norm_num)).fderivWithin
    (m := 0) hU (by norm_num)).continuousOn

theorem dirichletWithinRealHessian_eq_on_ball {n : ℕ} (u : E n → ℝ) :
    EqOn (dirichletWithinRealHessian u) (realHessian u) (unitBall n) := by
  intro x hx
  exact fderivWithin_fderivWithin_eq_of_mem_nhds
    (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)

theorem exists_integral_sq_withinRealHessian_le_withinLinearizedDet
    {n : ℕ} (hn : 0 < n) {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    ∃ C ≥ (0 : ℝ), ∀ {u q : E n → ℝ},
      ContDiffOn ℝ 2 u (closedUnitBall n) → ContDiffOn ℝ ∞ u (unitBall n) →
      ContDiffOn ℝ 2 q (closedUnitBall n) → ContDiffOn ℝ ∞ q (unitBall n) →
      (∀ x ∈ unitSphere n, u x = 0) → (∀ x ∈ unitSphere n, q x = 0) →
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef) →
      (∀ x ∈ closedUnitBall n,
        a ^ n ≤ (dirichletWithinComplexHessian u x).det.re ∧
        (dirichletWithinComplexHessian u x).det.re ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ‖dirichletWithinRealHessian u x‖ ≤ D) →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian q x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * ∫ x in unitBall n,
          (dirichletContractionCLM n
            (dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x))
            (dirichletWithinRealHessian q x)) ^ 2 ∂volume0 n := by
  obtain ⟨C, hC, hEst⟩ := exists_integral_sq_realHessian_le_linearizedDet hn
    (show 0 < a / 2 by positivity) (show 0 < b + 1 by positivity)
    (show 0 < D + 1 by positivity)
  refine ⟨C, hC, ?_⟩
  intro u q hu huS hq hqS hu0 hq0 hPos hDen hNorm
  obtain ⟨v, hV, _, _, hVH⟩ := exists_dirichlet_zeroBoundary_smooth_C2_approximation hu huS hu0
  obtain ⟨w, hW, _, _, hWH⟩ := exists_dirichlet_zeroBoundary_smooth_C2_approximation hq hqS hq0
  let Hu := dirichletWithinRealHessian u
  let Hq := dirichletWithinRealHessian q
  have hHu : ContinuousOn Hu (closedUnitBall n) := continuousOn_dirichletWithinRealHessian hu
  have hHq : ContinuousOn Hq (closedUnitBall n) := continuousOn_dirichletWithinRealHessian hq
  have hK : IsCompact (closedUnitBall n) := isCompact_closedBall _ _
  have hVCont (j : ℕ) : ContinuousOn (realHessian (v j)) (closedUnitBall n) := by
    intro x hx
    exact (realHessian_contDiffAt ((hV j).1.contDiffAt hx)).continuousAt.continuousWithinAt
  have hWCont (j : ℕ) : ContinuousOn (realHessian (w j)) (closedUnitBall n) := by
    intro x hx
    exact (realHessian_contDiffAt ((hW j).1.contDiffAt hx)).continuousAt.continuousWithinAt
  have hLower : (a / 2) ^ n < a ^ n := pow_lt_pow_left₀ (by linarith) (by positivity) hn.ne'
  have hUpper : b ^ n < (b + 1) ^ n := pow_lt_pow_left₀ (by linarith) hb.le hn.ne'
  have hEv := eventually_dirichlet_elliptic_bounds_of_uniform_hessian
    (fun j => (hV j).1) hHu hVH hPos
    (fun x hx => ⟨hLower.trans_le (hDen x hx).1, (hDen x hx).2.trans_lt hUpper⟩)
    (fun x hx => (hNorm x hx).trans_lt (lt_add_one D))
  let Q (B : E n →L[ℝ] E n →L[ℝ] ℝ) : ℝ :=
    ∑ i, ∑ j, (B (e[n] i) (e[n] j)) ^ 2
  have hQC : Continuous Q := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).pow 2
  have hQL := dirichlet_uniform_limit_comp_continuous hK hHq hWH hQC
  have hLeft := tendsto_integral_dirichlet_uniform_limit hn (hQC.comp_continuousOn hHq)
    (fun j => hQC.comp_continuousOn (hWCont j)) hQL
  let S (p : (E n →L[ℝ] E n →L[ℝ] ℝ) × (E n →L[ℝ] E n →L[ℝ] ℝ)) : ℝ :=
    (dirichletContractionCLM n (dirichletCofactorOfMatrix
      (complexHessianOfRealBilinear p.1)) p.2) ^ 2
  have hSC : Continuous S :=
    (((dirichletContractionCLM n).continuous.comp
      (contDiff_dirichletCofactorOfMatrix.continuous.comp
        (contDiff_dirichlet_complexHessianOfRealBilinear.continuous.comp continuous_fst))).clm_apply
          continuous_snd).pow 2
  have hPair : TendstoUniformlyOn
      (fun j x => (realHessian (v j) x, realHessian (w j) x))
      (fun x => (Hu x, Hq x)) atTop (closedUnitBall n) :=
    (hVH.prodMk hWH).seq_tendstoUniformlyOn (fun j : ℕ => (j, j))
      (tendsto_id.prodMk tendsto_id)
  have hSL := dirichlet_uniform_limit_comp_continuous hK (hHu.prodMk hHq) hPair hSC
  have hRight := tendsto_integral_dirichlet_uniform_limit hn
    (hSC.comp_continuousOn (hHu.prodMk hHq))
    (fun j => hSC.comp_continuousOn ((hVCont j).prodMk (hWCont j))) hSL
  have hSrc (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) :
      S (realHessian (v j) x, realHessian (w j) x) =
        (MoserTrudinger.cofactorContraction (v j) (w j) x) ^ 2 := by
    dsimp only [S]
    rw [complexHessianOfRealBilinear_eq
      (((hV j).1.contDiffAt hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      dirichletContractionCLM_apply,
      dirichletBilinearContraction_cofactor_eq (v j) (w j)
        (((hW j).1.contDiffAt hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  have hLe : ∀ᶠ j in atTop,
      (∫ x in unitBall n, Q (realHessian (w j) x) ∂volume0 n) ≤
        C * ∫ x in unitBall n, S (realHessian (v j) x, realHessian (w j) x) ∂volume0 n := by
    filter_upwards [hEv] with j hj
    have h := hEst (hV j).1 (hW j).1 (hV j).2 (hW j).2
      (fun x hx => (hj x hx).1)
      (fun x hx => ⟨(hj x hx).2.1.le, (hj x hx).2.2.1.le⟩)
      (fun x hx => (hj x hx).2.2.2.le)
    have he : (∫ x in unitBall n, S (realHessian (v j) x, realHessian (w j) x) ∂volume0 n) =
        ∫ x in unitBall n, (MoserTrudinger.cofactorContraction (v j) (w j) x) ^ 2 ∂volume0 n := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact hSrc j x (ball_subset_closedBall hx)
    rw [he]
    exact h
  exact le_of_tendsto_of_tendsto hLeft (hRight.const_mul C) hLe

end KEBall
