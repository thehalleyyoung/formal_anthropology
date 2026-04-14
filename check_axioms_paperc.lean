import FormalAnthropology.PaperC_DiversityTheorems_Revision
import FormalAnthropology.PaperC_RevisionPlan_Theorems
import FormalAnthropology.PaperC_NewTheorems_D10
import FormalAnthropology.PaperC_NewTheorems_D11
import FormalAnthropology.PaperC_NewTheorems_D12
import FormalAnthropology.PaperC_NewTheorems_D13_D14
import FormalAnthropology.PaperC_NewTheorems_D15
import FormalAnthropology.PaperC_NewTheorems_D16_D20
import FormalAnthropology.PaperC_NewTheorems_D21_D26
import FormalAnthropology.PaperC_NewTheorems_D27_D29

#check axioms

-- Standard Lean axioms:
-- propext : ∀ {a b : Prop}, (a ↔ b) → a = b
-- Classical.choice : ∀ {α : Sort u}, Nonempty α → α  
-- Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b

-- These are the only acceptable axioms - no custom axioms allowed
