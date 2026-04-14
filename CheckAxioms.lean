/-
Axiom checking script for Paper C diversity theorems.
This file prints all axioms used by the main diversity theorems D1-D9.
-/

import FormalAnthropology.PaperC_DiversityTheorems_Revision
import FormalAnthropology.PaperC_RevisionPlan_Theorems

open PaperC_DiversityRevision PaperC_RevisionPlan

-- D1-D5 from DiversityTheorems_Revision
#print axioms diversity_growth_monotone
#print axioms diversity_finite_bound
#print axioms transmission_monotonicity
#print axioms phase_transition_strict_growth
#print axioms diversity_respects_primitives

-- D6-D9 from RevisionPlan_Theorems
#print axioms phase_transition_diversity_explosion
#print axioms transmission_diversity_loss
#print axioms diversity_cumulative_growth
#print axioms diversity_ordinal_rankings_preserved
#print axioms diversity_depth_antimonotone_simplified
