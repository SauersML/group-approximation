---
rg: 2
id: bvc-counterexample-from-fp-torsion-group-with-bvc
kind: route
title: "A finitely presented infinite torsion group with BVC refutes Conjecture B"
target: some-fp-non-vc-group-has-property-bvc
requires: [some-fp-infinite-torsion-group-has-bvc]
---

Let `G` be a finitely presented infinite torsion group with BVC.  A virtually
cyclic torsion group is finite, because an infinite virtually cyclic group
contains an element of infinite order.  So `G` is not virtually cyclic, and
it witnesses `some-fp-non-vc-group-has-property-bvc`.  `∎`

This is a specialization, not a restatement: the prerequisite also asks for
torsion.  It links Conjecture B to Zaremsky Problem 1.11.  A finitely
presented infinite torsion group whose finite subgroups have bounded order
and lie in finitely many conjugacy classes of maximal finite subgroups would
settle both.
