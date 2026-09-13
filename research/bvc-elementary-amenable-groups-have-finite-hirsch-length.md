---
rg: 2
id: bvc-elementary-amenable-groups-have-finite-hirsch-length
kind: claim
title: An elementary amenable group with property BVC has finite Hirsch length
---

If `G` is elementary amenable and has property BVC, then the Hirsch length `h(G)` is finite.

Given `elementary-amenable-finite-hirsch-length-bvc-groups-are-vc`, this is equivalent to
`elementary-amenable-bvc-groups-are-virtually-cyclic`. The reason to state it separately is
that it isolates the missing input as a bound on Hirsch length, a property different from
virtual cyclicity and attackable by structure theory.

## Attempts

- Available constraints for `G` with BVC (von Puttkamer–Wu 1607.03790):
  - bounded orders of finite subgroups, so every locally finite subgroup is finite (argument of
    `elementary-amenable-finite-hirsch-length-bvc-groups-are-vc`, step 3);
  - ascending chain condition on normal subgroups (Lemma 1.13(a));
  - at most `N` non-torsion factors in any normal series, where `N` is the number of infinite
    witness subgroups (Lemma 1.13(c));
  - all quotients have the property "every cyclic subgroup is conjugate into finitely many
    virtually cyclic subgroups", so abelian quotients are virtually cyclic (B. H. Neumann's
    covering lemma);
  - BVC passes to finite-index subgroups and to quotients by finite normal subgroups;
  - `bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z`.
- Where the direct attempt dies (2026-09-13, lane z1-07-vc-proof): Lemma 1.13(c) bounds the
  NUMBER of non-torsion factors, not their torsion-free ranks. A single abelian normal section
  of infinite rank, acted on almost transitively on its rational lines, passes every constraint
  above that concerns normal subgroups. What is missing is a way to push BVC-type conjugacy
  control from `G` into a normal abelian section whose acting group `G/C_G(A)` is not itself
  virtually cyclic. Induction over Chou's elementary classes stalls at directed unions: for
  finitely generated `G` the union case collapses, but the kernel of an extension by an abelian
  quotient needn't be finitely generated.
- Plausible next step: show that for `A` abelian normal in a BVC group `G`, the quotient
  `Q = G/C_G(A)` (which inherits the cyclic-subgroup property) is virtually cyclic when
  elementary amenable, then use height counting on lines of `A ⊗ Q` under a virtually cyclic
  group to force finite rank.
