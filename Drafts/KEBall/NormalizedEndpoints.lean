import Drafts.KEBall.NormalizedBridge

/-! Stage09 SOURCE_DRAFT_UNCOMPILED. Exact frozen determinant-level endpoint. -/
set_option autoImplicit false
open Set

namespace KEBall.Stage09

theorem normalizedClassification : NormalizedClassificationStatement := by
  intro n hn γ hγ
  refine ⟨?_, ?_⟩
  · intro hγκ
    have hex := normalizedPotential_isNormalizedSolution hn hγ hγκ
    refine ⟨hex, ?_⟩
    ext v
    constructor
    · rintro ⟨φ, hφ, hv⟩
      have heq := (hφ.eqOn_normalizedPotential hn).2
      apply Set.mem_singleton_iff.mpr
      exact hv.symm.trans (restrictClosedBall_eq_iff.mpr heq)
    · intro hv
      have hv' := Set.mem_singleton_iff.mp hv
      exact ⟨normalizedPotential n γ, hex, hv'.symm⟩
  · intro hκγ
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro v ⟨φ, hφ, _⟩
    exact (not_lt_of_ge hκγ) (hφ.eqOn_normalizedPotential hn).1

#print axioms normalizedClassification

end KEBall.Stage09
