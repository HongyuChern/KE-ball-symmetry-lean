import Drafts.KEBall.InteriorGradientRigidity
import KEBall.Endpoints
import KEBall.ScalarBranches

/-!
Stage09 SOURCE_DRAFT_UNCOMPILED.
The forward classification and the exact solution counts concern the original
solutionSet, not just the explicit radial subfamily. Frozen specifications and
closed-ball restrictions are unchanged.
-/
set_option autoImplicit false
open Set

namespace KEBall.Stage09

theorem classification : ClassificationStatement := by
  intro n hn μ u hu
  exact hu.radial_classification hn

theorem solutionSet_eq_radialSolutionSet {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) :
    solutionSet n μ = radialSolutionSet n μ := by
  apply Set.Subset.antisymm
  · rintro v ⟨u, hu, hv⟩
    obtain ⟨b, hb, heq, hμ⟩ := hu.radial_classification hn
    refine ⟨b, hb, hμ.symm, ?_⟩
    have hrestr : restrictClosedBall u = restrictClosedBall (radialPotential n b) :=
      restrictClosedBall_eq_iff.mpr heq
    exact hrestr.symm.trans hv
  · exact radialSolutionSet_subset_solutionSet n μ

theorem solutionCounts : SolutionCountsStatement := by
  intro n hn
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ hμc
    rw [solutionSet_eq_radialSolutionSet hn]
    exact radialSolutionSet_subcritical (by omega) hμ hμc
  · rw [solutionSet_eq_radialSolutionSet hn, radialSolutionSet_critical (by omega : 1 ≤ n)]
    refine ⟨restrictClosedBall (radialPotential n (n : ℝ)), ?_, ?_⟩
    · exact Set.mem_singleton _
    · intro v hv
      exact Set.mem_singleton_iff.mp hv
  · intro μ hμ
    rw [solutionSet_eq_radialSolutionSet hn]
    exact radialSolutionSet_supercritical (by omega) hμ

/-- The forward and converse statements have exactly the frozen quantifiers. -/
theorem classification_and_counts :
    ClassificationStatement ∧ RadialExistenceStatement ∧ SolutionCountsStatement :=
  ⟨classification, KEBall.radialExistence, solutionCounts⟩

#print axioms classification
#print axioms solutionCounts

end KEBall.Stage09
