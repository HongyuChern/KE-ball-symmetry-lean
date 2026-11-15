import KEBall.DirichletDifferenceQuotientRegularity

/-!
# Reassembling local derivative Holder bounds in finite dimensions

Only finitely many basis directions are needed, so the individual
neighborhoods have a common positive-radius subball.  Flipping the two
linear slots is an isometry and introduces no loss of exponent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Function Metric Module Set
open scoped NNReal Topology

namespace KEBall

theorem dirichlet_exists_holderOnWith_clm_of_basis {n : ℕ} {F X : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [PseudoEMetricSpace X]
    {S : Set X} {f : X → E n →L[ℝ] F} {α : ℝ≥0}
    (hf : ∀ i : Fin (2 * n), ∃ K : ℝ≥0, HolderOnWith K α
      (fun x => f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) S) :
    ∃ K : ℝ≥0, HolderOnWith K α f S := by
  classical
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  let e : (E n →L[ℝ] F) ≃L[ℝ] (Fin (2 * n) → F) :=
    (b.equivFunL.arrowCongr (ContinuousLinearEquiv.refl ℝ F)).trans
      (ContinuousLinearEquiv.piRing (Fin (2 * n)))
  have he (A : E n →L[ℝ] F) (i : Fin (2 * n)) : e A i = A (b i) := by
    change A (b.equivFunL.symm (Pi.single i 1)) = A (b i)
    congr 1
    change b.equivFun.symm (Pi.single i 1) = b i
    simp
  choose K hK using hf
  have hp : HolderOnWith (∑ i, K i) α (fun x => e (f x)) S := by
    intro x hx y hy
    apply edist_pi_le_iff.mpr
    intro i
    change edist (e (f x) i) (e (f y) i) ≤ _
    rw [he, he]
    apply (hK i x hx y hy).trans
    gcongr
    exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)
  refine ⟨‖e.symm.toContinuousLinearMap‖₊ * ∑ i, K i, ?_⟩
  have hh := e.symm.lipschitz.holderWith.comp_holderOnWith hp
  intro x hx y hy
  simpa only [Function.comp_def, e.symm_apply_apply, one_mul, NNReal.coe_one,
    NNReal.rpow_one] using! hh x hx y hy

theorem dirichlet_contDiffOn_clm_of_basis {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : WithTop ℕ∞} {S : Set (E n)} {f : E n → E n →L[ℝ] F}
    (hf : ∀ i : Fin (2 * n), ContDiffOn ℝ k
      (fun x => f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) S) :
    ContDiffOn ℝ k f S := by
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  let e : (E n →L[ℝ] F) ≃L[ℝ] (Fin (2 * n) → F) :=
    (b.equivFunL.arrowCongr (ContinuousLinearEquiv.refl ℝ F)).trans
      (ContinuousLinearEquiv.piRing (Fin (2 * n)))
  have he (A : E n →L[ℝ] F) (i : Fin (2 * n)) : e A i = A (b i) := by
    change A (b.equivFunL.symm (Pi.single i 1)) = A (b i)
    congr 1
    change b.equivFun.symm (Pi.single i 1) = b i
    simp
  have hc : ContDiffOn ℝ k (e ∘ f) S := by
    apply contDiffOn_pi.mpr
    intro i
    simpa only [Function.comp_def, he] using! hf i
  simpa only [Function.comp_def, e.symm_apply_apply] using!
    e.symm.contDiff.comp_contDiffOn hc

theorem exists_dirichlet_local_C1_holder_clm_of_directions {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → E n →L[ℝ] F} {p : E n} {α : ℝ≥0}
    (hf : ∀ i : Fin (2 * n), ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ≥0,
      ContDiffOn ℝ 1 (fun x => f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) (ball p δ) ∧
      HolderOnWith K α (fderiv ℝ (fun x => f x (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i))) (ball p δ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ≥0,
      ContDiffOn ℝ 1 f (ball p δ) ∧ HolderOnWith K α (fderiv ℝ f) (ball p δ) := by
  classical
  choose r hr K hC1 hHolder using hf
  have hN : (⋂ i, ball p (r i)) ∈ 𝓝 p :=
    Filter.iInter_mem.mpr (fun i => ball_mem_nhds p (hr i))
  obtain ⟨δ, hδ, hδSub⟩ := Metric.mem_nhds_iff.mp hN
  have hSub (i : Fin (2 * n)) : ball p δ ⊆ ball p (r i) :=
    fun _ hx => mem_iInter.mp (hδSub hx) i
  have hC : ContDiffOn ℝ 1 f (ball p δ) :=
    dirichlet_contDiffOn_clm_of_basis (fun i => (hC1 i).mono (hSub i))
  have hEval (x : E n) (hx : x ∈ ball p δ) (v : E n) :
      fderiv ℝ (fun y => f y v) x = (fderiv ℝ f x).flip v := by
    have hd := (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x
      ((hC.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
    apply hd.fderiv.trans
    ext z
    rfl
  obtain ⟨C, hCFlip⟩ := dirichlet_exists_holderOnWith_clm_of_basis
    (f := fun x => (fderiv ℝ f x).flip) (S := ball p δ) (α := α) (by
      intro i
      refine ⟨K i, ?_⟩
      intro x hx y hy
      change edist ((fderiv ℝ f x).flip (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i))
        ((fderiv ℝ f y).flip (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)) ≤ _
      rw [← hEval x hx, ← hEval y hy]
      exact hHolder i x (hSub i hx) y (hSub i hy))
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro x hx y hy
  have he := (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) F).isometry.edist_eq
    (fderiv ℝ f x) (fderiv ℝ f y)
  rw [← he]
  exact hCFlip x hx y hy

end KEBall
