---
rg: 2
id: two-generator-fp-torsion-free-master-tester
kind: claim
title: One two-generator finitely presented torsion-free group tests Whitehead, assembly, Farrell--Jones, Kaplansky, and classical Bass
distinct_from:
  two-generator-fp-torsion-free-universal-whitehead-container: that is the structural universal-embedding theorem; this records the exact global-conjecture equivalences enjoyed by the same group.
  universal-torsion-free-subgroup-colimit-class-tester: that gives the abstract tester without controlling generators or approximation properties; this supplies a two-generator nonsofic non-MF witness and also lists the Whitehead-functor applications that need more than class closure.
  whitehead-universal-finitely-presented-torsion-free-group: that tests ordinary Whitehead vanishing; this packages the same role simultaneously for several major conjectures in a two-generator group.
---

There exists one two-generator finitely presented torsion-free group `E`,
which may simultaneously be chosen nonsofic and non-MF, with all of the
following exact tester properties.

1. `Wh(E)=0` iff `Wh(G)=0` for every torsion-free group `G`.
2. The degree-one integral assembly `A_1^E` is onto iff `A_1^G` is onto
   for every torsion-free `G`.
3. The connective integral Loday assembly for `E` is a weak equivalence
   iff it is a weak equivalence for every torsion-free `G`.
4. `E` satisfies Full Farrell--Jones iff every torsion-free group does.
5. For every field `k`, separately, each of the domain,
   trivial-idempotent, and trivial-two-sided-unit properties for `k[E]` is
   equivalent to that property for `k[G]` for every torsion-free `G`.
6. For every class `C` closed under subgroups and directed colimits with
   arbitrary structure maps,

   ```text
   E belongs to C  <=>  every torsion-free group belongs to C.
   ```

7. `E` satisfies the integral classical Bass conjecture iff every
   torsion-free group does.

For each of the three properties in item 5, its assertion for every field
and every torsion-free group is also equivalent to checking `F[E]` for
every finite field `F`.

These are equivalences, not proofs of the open sides. In particular the
Whitehead, connective Loday, Full Farrell--Jones, zero-divisor, idempotent,
and classical Bass conjectures remain open; the all-fields unit statement is
already false.

**ESTABLISHED 2026-08-30** by
[[two-generator-master-tester-consequences]].
