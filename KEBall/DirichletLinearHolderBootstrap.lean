import KEBall.DirichletLocalHolderLinearGain
import KEBall.DirichletC3DifferentiatedEquation

/-!
# Finite-order interior bootstrap for an actual linear elliptic equation

Each induction step differentiates the actual equation.  The derivative of
the coefficient is contracted with the original Hessian in the new source.
The coefficient and the original source gain no unproved derivative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

theorem hasDirichletHolderAt_of_linear_elliptic_equation {n : ℕ} (hn : 0 < n)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∀ {S : Set (E n)} (hS : IsOpen S) {p : E n} (hp : p ∈ S)
      {u f : E n → ℝ} {A : E n → E n →L[ℝ] E n},
      HasDirichletHolderAt 2 α u p → HasDirichletHolderAt k α f p → HasDirichletHolderAt k α A p →
      (dirichletSchauderMatrix (A p)).PosDef →
      ∀ {l : ℝ}, 0 < l → (∀ z, l * ‖z‖ ^ 2 ≤ inner ℝ (A p z) z) →
      (∀ x ∈ S, dirichletContractionCLM n (A x) (fderiv ℝ (fderiv ℝ u) x) = f x) →
      HasDirichletHolderAt (k + 2) α u p := by
  induction k with
  | zero =>
      intro S hS p hp u f A hu hf hA hPos l hl hEll hEq
      exact hu
  | succ k ih =>
      intro S hS p hp u f A hu hf hA hPos l hl hEll hEq
      have hf1 : HasDirichletHolderAt 1 α f p := hf.of_order_le (by omega) hα1.le
      have hA1 : HasDirichletHolderAt 1 α A p := hA.of_order_le (by omega) hα1.le
      have hu3 := hasDirichletHolderAt_three_of_linear_elliptic_equation hn hS hp
        hα hα1 hu hf1 hA1 hPos hl hEll hEq
      have huk := ih hS hp hu (hf.of_order_le (by omega) hα1.le)
        (hA.of_order_le (by omega) hα1.le) hPos hl hEll hEq
      have hHk : HasDirichletHolderAt k α (fderiv ℝ (fderiv ℝ u)) p := huk.derivative.derivative
      have hDir (v : E n) : HasDirichletHolderAt (k + 2) α (fun x => fderiv ℝ u x v) p := by
        let g (x : E n) := fderiv ℝ f x v -
          dirichletContractionCLM n (fderiv ℝ A x v) (fderiv ℝ (fderiv ℝ u) x)
        have hv : HasDirichletHolderAt 2 α (fun x => fderiv ℝ u x v) p :=
          hu3.derivative.clm hα hα1.le (ContinuousLinearMap.apply ℝ ℝ v)
        have hDf : HasDirichletHolderAt k α (fun x => fderiv ℝ f x v) p :=
          hf.derivative.clm hα hα1.le (ContinuousLinearMap.apply ℝ ℝ v)
        have hDA : HasDirichletHolderAt k α (fun x => fderiv ℝ A x v) p :=
          hA.derivative.clm hα hα1.le (ContinuousLinearMap.apply ℝ (E n →L[ℝ] E n) v)
        have hg : HasDirichletHolderAt k α g p :=
          hDf.sub (hDA.bilinear hHk hα hα1.le (dirichletContractionCLM n)) hα hα1.le
        have hNear : ∀ᶠ x in 𝓝 p,
            dirichletContractionCLM n (A x)
              (fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y v)) x) = g x := by
          filter_upwards [hu3.contDiffAt.eventually (by simp), hA1.contDiffAt.eventually (by simp),
            hS.mem_nhds hp] with x hux hAx hxS
          apply dirichlet_linear_directional_equation_of_C3 hux
            (hAx.differentiableAt (by norm_num))
          filter_upwards [hS.mem_nhds hxS] with y hy
          exact hEq y hy
        obtain ⟨ρ, hρ, hPDE⟩ := Metric.mem_nhds_iff.mp hNear
        exact ih isOpen_ball (mem_ball_self hρ) hv hg
          (hA.of_order_le (by omega) hα1.le) hPos hl hEll (fun x hx => hPDE hx)
      obtain ⟨R, hR, huC, K, huH⟩ := hu3
      exact HasDirichletHolderAt.of_directions hR (huC.of_le (by norm_num))
        (fun i => hDir (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i))

end KEBall
