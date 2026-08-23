---
rg: 2
id: congruence-repair-bypasses-cycle-firewalls-proof
kind: route
title: Apply labeled pure-dyadic repair on every congruence CRT fiber
target: congruence-repair-bypasses-koopman-cycle-firewalls
requires:
  - mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding
  - odd-label-stabilization-has-uniform-repair
---

Decompose the two congruence vertex representations by their common odd
CRT labels.  The mixed-CRT reduction identifies each label fiber with a
pure dyadic Iwahori matching problem.  The uniform odd-label theorem
balances unequal fibers, relabels only the globally trivial surplus, and
applies the pure dyadic repair with one dimension-independent constant.
Summing the weighted fiber costs gives a global compatible pair at cost
`O(defect)`, hence `o(1)` along the sequence.

This conclusion quantifies over every dyadic conductor and every
fourth-power cycle in the fibers.  It therefore already includes both the
delocalized first-mode firewall and the concentrated two-jump firewall.
No separate Koopman inverse estimate is needed on this locus.

