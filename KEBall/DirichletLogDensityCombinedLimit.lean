import KEBall.DirichletC1InteriorLimit
import KEBall.DirichletLogDensityBoundaryLimit

/-!
# Interior and boundary estimates for the same actual path limit

The uniform derivative convergence is retained, so the boundary quotient
estimate applies to precisely the first jet with the classical interior
determinant equation and scaled Hessian Hölder estimates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff Matrix NNReal Topology

namespace KEBall

def HasDirichletRotationBoundaryPower {n : ℕ} (G : E n → E n →L[ℝ] ℝ) : Prop :=
  ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
    ∀ (T : E n →L[ℝ] E n), (∀ y, T (J y) = J (T y)) →
      ∀ (M : Matrix (Fin n) (Fin n) ℂ), (∀ y, complexCoord (T y) = M *ᵥ complexCoord y) →
        Mᴴᵀ = -Mᵀ → (∀ x ∈ unitSphere n, inner ℝ x (T x) = 0) → ‖T‖ ≤ 3 →
        ∀ p ∈ unitSphere n, ∀ r : ℝ, 0 < r → r ≤ 1 →
          dirichletBoundaryOscillation
            (fun x => G x (T x) / dirichletBoundaryDistanceProxy x) p r ≤ C * r ^ α

theorem hasDirichletRotationBoundaryPower_of_logDensityPath_firstJet_limit
    {n : ℕ} (hn : 2 ≤ n) {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x))
    {G : E n → E n →L[ℝ] ℝ}
    (hGrad : TendstoUniformlyOn (fun m => fderiv ℝ (u m)) G atTop (closedUnitBall n)) :
    HasDirichletRotationBoundaryPower G := by
  obtain ⟨α, D, hα0, hα1, hD, hPower⟩ :=
    exists_logDensityPath_firstJet_limit_boundary_power hn hg (by norm_num : (0 : ℝ) ≤ 3)
      ht hu hu0 huP hEq hGrad
  refine ⟨α, D * (256 : ℝ) ^ α, hα0, hα1, by positivity, ?_⟩
  intro T hTJ M hTM hM hTan hNorm p hp r hr hr1
  simpa only [div_one] using
    hPower T hTJ M hTM hM hTan hNorm p hp 1 zero_lt_one le_rfl r hr hr1

theorem exists_dirichlet_C1_interior_boundary_limit_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      StrictMono φ ∧ TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      ContDiffOn ℝ 1 w (closedUnitBall n) ∧ ContDiffOn ℝ 2 w (unitBall n) ∧
      (∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧ (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      HasDirichletHessianOscillationDecay G ∧
      (∃ α H : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ H ∧
        ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
          ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
            ‖realHessian w x - realHessian w y‖ ≤
              (H * (4 / R : ℝ) ^ α) * ‖x - y‖ ^ α) ∧
      HasDirichletRotationBoundaryPower G := by
  obtain ⟨φ, w, G, L, α, H, hφ, hUw, hGrad, hα0, hα1, hH, hw1, hw2,
      hDclosed, hD, hLip, hw0, hPos, hDet, hDecay, hHolder⟩ :=
    exists_dirichlet_C1_interior_classical_holder_limit_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  refine ⟨φ, w, G, L, hφ, hUw, hGrad, hw1, hw2, hDclosed, hD, hLip, hw0, hPos, hDet,
    hDecay, ⟨α, H, hα0, hα1, hH, hHolder⟩, ?_⟩
  exact hasDirichletRotationBoundaryPower_of_logDensityPath_firstJet_limit hn hg
    (fun j => ht (φ j)) (fun j => hu (φ j)) (fun j => hu0 (φ j))
    (fun j => huP (φ j)) (fun j => hEq (φ j)) hGrad

end KEBall
