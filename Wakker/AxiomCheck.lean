/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Classical Lottery / Wakker--Debreu--Koopmans artifact
-/

import WakkerDebreuKoopmans.Audit

/-!
# Axiom audit for the Wakker--Debreu--Koopmans interface

This is the reviewer-facing regression file for the split Wakker/DK artifact.
It imports the detailed construction-stack audit in
`WakkerDebreuKoopmans.Audit` and adds the headline public theorem surface:

* the Wakker IV.2.7 and Debreu--Koopmans wrappers;
* the stable core consumers used by downstream artifacts;

The imported audit covers the certificate iff-equivalences, M2 frontier,
T1--T6 topology-bundle consumers, S23--S33 construction stack, and the
A4 → A1 → A3 → A2 → B → C closure chain.

## Expected output

Every `#print axioms` command in this file and in the imported detailed audit
should print

```
[propext, Classical.choice, Quot.sound]
```

No theorem in the public Wakker/DK interface should depend on any additional
axiom.
-/

/-! ## Headline theorem surface -/

#print axioms WakkerDebreuKoopmans.wakker_IV_2_7
#print axioms WakkerDebreuKoopmans.debreu_koopmans_easy
#print axioms WakkerDebreuKoopmans.debreu_koopmans_hard

/-! ## Core Wakker/DK consumers and stable downstream interfaces -/

#print axioms WakkerDebreuKoopmans.AdditiveRep.additiveRep_isWeakOrder
#print axioms WakkerDebreuKoopmans.AdditiveRep.additiveRep_separable
#print axioms WakkerDebreuKoopmans.concaveOn_sum_of_concaveOn
#print axioms WakkerRoadmap.WakkerExistence.global_additive_from_pairwise
#print axioms WakkerRoadmap.WakkerExistence.additive_rep_indiff_iff
#print axioms WakkerRoadmap.WakkerExistence.additive_rep_strict_iff
#print axioms WakkerRoadmap.WakkerExistence.additive_rep_unique
#print axioms WakkerRoadmap.WakkerExistence.wakker_IV_2_7_consumer
#print axioms WakkerRoadmap.DebreuKoopmansHard.two_coord_quasiconcave_left
#print axioms WakkerRoadmap.DebreuKoopmansHard.two_coord_quasiconcave_right
#print axioms WakkerRoadmap.DebreuKoopmansHard.two_coord_concave
#print axioms WakkerRoadmap.DebreuKoopmansHard.concave_transfers
#print axioms WakkerRoadmap.DebreuKoopmansHard.debreu_koopmans_hard_consumer
#print axioms WakkerRoadmap.DebreuKoopmansHard.debreu_koopmans_hard_from_base_and_pairs
