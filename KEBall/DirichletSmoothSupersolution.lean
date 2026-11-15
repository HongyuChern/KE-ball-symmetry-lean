import KEBall.DirichletWeakHarnack
import KEBall.DirichletRotationCofactorEquation
import KEBall.MoserTrudingerSmoothGibbsExtension

/-!
# Smooth-near potentials as actual weak supersolutions

Only a neighborhood of the closed ball is used.  The already verified
smooth extension supplies a global representative for the weak-gradient
identity, and locality returns all integrals to the original function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions ENNReal Gradient Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem dirichlet_gradient_eq_of_eventuallyEq {n : ℕ}
    {f g : E n → ℝ} {x : E n} (h : f =ᶠ[𝓝 x] g) : ∇ f x = ∇ g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, inner_gradient_left, h.fderiv_eq]

theorem IsDirichletWeakGradient.of_smoothNear {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : SmoothNear (closedUnitBall n) f) :
    IsDirichletWeakGradient f (∇ f) := by
  obtain ⟨g, hg, he⟩ := MoserTrudinger.exists_global_contDiff_of_smoothNear hf
  have hG : ∇ g =ᵐ[ν[n]] ∇ f := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact dirichlet_gradient_eq_of_eventuallyEq (he x (ball_subset_closedBall hx))
  have hF : g =ᵐ[ν[n]] f := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact (he x (ball_subset_closedBall hx)).self_of_nhds
  have h := IsDirichletWeakGradient.of_smooth hn hg
  intro j ψ
  calc
    _ = ∫ x, ψ x * inner ℝ (e[n] j) (∇ g x) ∂ν[n] := by
      apply integral_congr_ae
      filter_upwards [hG] with x hx
      rw [hx]
    _ = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] j) * g x ∂ν[n]) := h j ψ
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      rw [hx]

theorem memLp_dirichlet_smoothNear_gradient {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : SmoothNear (closedUnitBall n) f) :
    MemLp f 2 ν[n] ∧ MemLp (∇ f) 2 ν[n] := by
  obtain ⟨g, hg, he⟩ := MoserTrudinger.exists_global_contDiff_of_smoothNear hf
  have hG : ∇ g =ᵐ[ν[n]] ∇ f := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact dirichlet_gradient_eq_of_eventuallyEq (he x (ball_subset_closedBall hx))
  have hF : g =ᵐ[ν[n]] f := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact (he x (ball_subset_closedBall hx)).self_of_nhds
  exact ⟨(memLp_continuousOn_dirichletBall hn hg.continuous.continuousOn).ae_eq hF,
    (memLp_continuousOn_dirichletBall hn
      (contDiff_euclideanGradient hg).continuous.continuousOn).ae_eq hG⟩

theorem integral_dirichlet_cofactor_smooth_eq_neg_realHessian {n : ℕ} (hn : 0 < n)
    {u q : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hq : SmoothNear (closedUnitBall n) q)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef) (ψ : 𝓓B[n]) :
    (∫ x, inner ℝ (dirichletCofactorOperator u x (∇ q x))
      (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
      -(∫ x, ψ x * dirichletBilinearContraction e[n] (dirichletCofactorOperator u x)
        (realHessian q x) ∂ν[n]) := by
  obtain ⟨U, hU, hSubU, huU⟩ := hu
  obtain ⟨V, hV, hSubV, hqV⟩ := hq
  have hψ0 (x : E n) (hx : x ∈ unitSphere n) : ψ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hb := mem_ball_zero_iff.mp (ψ.tsupport_subset hs)
    rw [mem_sphere_zero_iff_norm.mp hx] at hb
    exact (lt_irrefl _ hb).elim
  have h := integral_dirichletCofactorOperator_eq_neg_linearization hn
    (hU.inter hV) (fun x hx => ⟨hSubU hx, hSubV hx⟩)
    (huU.mono inter_subset_left) ψ.contDiff.contDiffOn (hqV.mono inter_subset_right) huP hψ0
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  have hqAt : ContDiffAt ℝ 2 q x :=
    (hqV.contDiffAt (hV.mem_nhds (hSubV (ball_subset_closedBall hx)))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [← dirichletCofactorOfMatrix_complexHessian,
    dirichletBilinearContraction_cofactor_eq u q hqAt]

theorem dirichlet_smooth_cofactor_weak_supersolution {n : ℕ} (hn : 0 < n)
    {u q : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hq : SmoothNear (closedUnitBall n) q)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hL : ∀ x ∈ unitBall n,
      dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian q x) ≤ 0) :
    ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
      0 ≤ ∫ x, inner ℝ (dirichletCofactorOperator u x (∇ q x))
        (∇ (ψ : E n → ℝ) x) ∂ν[n] := by
  intro ψ hψ
  rw [integral_dirichlet_cofactor_smooth_eq_neg_realHessian hn hu hq huP]
  apply neg_nonneg.mpr
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  exact mul_nonpos_of_nonneg_of_nonpos (hψ x hx) (hL x hx)

end KEBall
