module

import Solution

/-!
# Axiom check

`lake env lean scripts/CheckAxioms.lean` (after `lake build`) prints the axioms that each compared
theorem of `Solution.lean` depends on. Palomar permits only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms Gw53.exists_good_row5
#print axioms Gw53.lt_of_gwProperty_row5
#print axioms Gw53.lt_GW_row5
#print axioms Gw53.exists_canonical_row5
#print axioms Gw53.exists_good_row6
#print axioms Gw53.lt_of_gwProperty_row6
#print axioms Gw53.lt_GW_row6
