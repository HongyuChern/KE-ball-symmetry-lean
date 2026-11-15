import KEBall.DirichletMirandaTalenti
import KEBall.DirichletLaplacianTrace
import KEBall.DirichletLogDensityStability

/-! Full real Hessian estimates for pairs of smooth Dirichlet solutions. -/

set_option autoImplicit false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Laplacian Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

private theorem realHessian_sub_at {n : ℕ} {u v : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) :
    realHessian (v - u) x = realHessian v x - realHessian u x := by
  have he : fderiv ℝ (v - u) =ᶠ[𝓝 x] fun y => fderiv ℝ v y - fderiv ℝ u y := by
    filter_upwards [(hu.of_le (m := 1) (by norm_num)).eventually (by simp), (hv.of_le (m := 1) (by norm_num)).eventually (by simp)] with y hy hz
    exact fderiv_sub (hz.differentiableAt one_ne_zero) (hy.differentiableAt one_ne_zero)
  rw [realHessian, he.fderiv_eq, fderiv_fun_sub
    ((hv.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))]
  rfl

/-- With identical zero boundary data, the whole real Hessian difference is
controlled in (L²) by the complex Hessian difference. -/
theorem integral_sq_realHessian_sub_le_complex {n : ℕ} (hn : 0 < n)
    {u v : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u) (hv : SmoothNear (closedUnitBall n) v)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0) :
    (∫ x in unitBall n, ∑ i, ∑ j, ((realHessian v x - realHessian u x) (e[n] i) (e[n] j)) ^ 2
      ∂volume0 n) ≤
    (16 * n : ℝ) * ∫ x in unitBall n, ∑ i, ∑ j, ‖(complexHessian v x - complexHessian u x) i j‖ ^ 2
      ∂volume0 n := by
  have hw : SmoothNear (closedUnitBall n) (v - u) := by
    obtain ⟨U, hU, hSubU, huU⟩ := hu
    obtain ⟨V, hV, hSubV, hvV⟩ := hv
    exact ⟨U ∩ V, hU.inter hV, subset_inter hSubU hSubV,
      (hvV.mono inter_subset_right).sub (huU.mono inter_subset_left)⟩
  have hw0 (x : E n) (hx : x ∈ unitSphere n) : (v - u) x = 0 := by simp [hu0 x hx, hv0 x hx]
  have h := mirandaTalenti_identity_on_unitBall hn hw hw0
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hFlux : 0 ≤ (2 * n : ℝ) * (2 * n - 1 : ℝ) *
      ∫ θ : Sphere n, (fderiv ℝ (v - u) θ.val θ.val) ^ 2 ∂sphere0 n :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith only [hnR]))
      (integral_nonneg fun _ => sq_nonneg _)
  have hReal :
      (∫ x in unitBall n, ∑ i, ∑ j, (realHessian (v - u) x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) =
        ∫ x in unitBall n, ∑ i, ∑ j, ((realHessian v x - realHessian u x) (e[n] i) (e[n] j)) ^ 2
          ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    simp only [realHessian_sub_at (hu.contDiffAt (ball_subset_closedBall hx))
      (hv.contDiffAt (ball_subset_closedBall hx))]
  have hLap :
      (∫ x in unitBall n, (Δ (v - u) x) ^ 2 ∂volume0 n) =
        ∫ x in unitBall n, (Δ v x - Δ u x) ^ 2 ∂volume0 n := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    have huAt := (hu.contDiffAt (ball_subset_closedBall hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hvAt := (hv.contDiffAt (ball_subset_closedBall hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    simp only [hvAt.laplacian_sub huAt]
  rw [hLap, hReal] at h
  exact (sub_nonneg.mp (hFlux.trans_eq h.symm)).trans (integral_sq_euclideanLaplacian_sub_le hn hu hv)

/-- Along the smooth log-density path the entire real Hessian is Lipschitz
in the parameter in the Hilbert–Schmidt (L²) norm. -/
theorem exists_integral_sq_realHessian_sub_le_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) :
    ∃ C ≥ (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ {u v : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) v →
      (∀ x ∈ unitSphere n, u x = 0) → (∀ x ∈ unitSphere n, v x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = Real.exp (s * g x)) →
      (∀ x ∈ unitBall n, (complexHessian v x).det.re = Real.exp (t * g x)) →
      (∫ x in unitBall n, ∑ i, ∑ j, ((realHessian v x - realHessian u x) (e[n] i) (e[n] j)) ^ 2
        ∂volume0 n) ≤ C * (t - s) ^ 2 := by
  obtain ⟨C, hC, hBound⟩ := exists_integral_sq_complexHessian_sub_le_of_logDensityPath hn hg
  refine ⟨(16 * n : ℝ) * C, by positivity, ?_⟩
  intro s hs t ht u v hu hv hu0 hv0 huP hvP huEq hvEq
  exact (integral_sq_realHessian_sub_le_complex hn hu hv hu0 hv0).trans
    ((mul_le_mul_of_nonneg_left (hBound s hs t ht hu hv hu0 hv0 huP hvP huEq hvEq)
      (by positivity)).trans_eq (mul_assoc _ _ _).symm)

end KEBall
