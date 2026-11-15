import KEBall.DirichletComplexFiniteLpJets
import Mathlib.Data.Matrix.Basis

/-! Real coordinates of the actual complex matrix field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000
open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

theorem dirichlet_matrix_single_real_decomposition {m : ℕ} (i j : Fin m) (z : ℂ) :
    Matrix.single i j z=z.re • Matrix.single i j (1 : ℂ)+z.im • Matrix.single i j Complex.I := by
  rw [Matrix.smul_single,Matrix.smul_single,← Matrix.single_add]
  congr 1
  simpa only [Complex.real_smul,mul_one] using (Complex.re_add_im z).symm

theorem hasDirichletFiniteLpJets_matrix_real_clm {n m k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A : E n → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j))
    (L : Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℝ) :
    HasDirichletFiniteLpJets U μ k (fun x => L (A x)) := by
  have hSum := HasDirichletFiniteLpJets.finsetSum hU hμ Finset.univ
    (fun i _ => HasDirichletFiniteLpJets.finsetSum hU hμ Finset.univ (fun j _ =>
      (((hA i j).1).mul hU hμ (HasDirichletFiniteLpJets.const k (L (Matrix.single i j 1)))).add hU hμ
        (((hA i j).2).mul hU hμ (HasDirichletFiniteLpJets.const k (L (Matrix.single i j Complex.I))))))
  refine hSum.congr hU hμ ?_
  intro x _
  change (∑ i, ∑ j, ((A x i j).re*L (Matrix.single i j 1)+
    (A x i j).im*L (Matrix.single i j Complex.I)))=L (A x)
  calc
    _ = L (∑ i, ∑ j, Matrix.single i j (A x i j)) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [dirichlet_matrix_single_real_decomposition i j (A x i j),map_add,map_smul,map_smul]
      rfl
    _ = _ := congrArg L (Matrix.matrix_eq_sum_single (A x)).symm

theorem hasDirichletFiniteLpJets_matrix_real_coord {n m k : ℕ} {ι : Type*}
    (b : Module.Basis ι ℝ (Matrix (Fin m) (Fin m) ℂ))
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A : E n → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j)) (i : ι) :
    HasDirichletFiniteLpJets U μ k (fun x => b.repr (A x) i) := by
  exact hasDirichletFiniteLpJets_matrix_real_clm hU hμ hA (b.coord i).toContinuousLinearMap

end KEBall
