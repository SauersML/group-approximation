---
rg: 2
id: iwahori-congruence-capture-transfers-across-one-edge
kind: claim
title: Congruence capture of one Iwahori vertex transfers across the edge to the other vertex
distinct_from:
  dv-distance-is-defect-plus-congruence-capture: that shows D(pi) is controlled by def(pi) plus distance of the whole pair to congruence pairs; this bounds the pair distance by the distance of one vertex alone, so the capture hypothesis there may be halved.
  modular-vertex-extension-does-not-force-congruence: that shows an edge representation extending through one exact modular vertex need not be congruence; this shows that once one vertex is congruence, a near-compatible second vertex is near congruence, which is a different implication and consistent with that example.
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that assumes both vertices factor through odd congruence quotients; this assumes one vertex near a congruence representation of any level and produces the congruence partner.
  regular-iwahori-relative-congruence-exactification: that asks to move an arbitrary regular pair into the congruence locus; this makes that move automatic for any pair one of whose vertices is already near congruence.
  iwahori-unitary-commutant-transfer: that transfers almost-centralizing unitaries between vertices; this transfers congruence proximity, using induction and Selberg (tau), and no commutant input.
---

**ESTABLISHED.** Use the notation of `iwahori-local-global-defect-question`:
`Lambda = C_+ * C_-` with `C_+ = C_- = C = SL_2(Z)`, Iwahori subgroups
`B_+ = Gamma_0(2)` and `B_- = Gamma^0(2)`, `sigma : B_+ -> B_-`, the generalized
metric `d_2`, and the defect `def(pi)`. Pairs are compared on
`S = S_C ⊔ S_C`, a fixed finite generating set of each vertex. Let
`A_cong(pi)` be the generalized distance from `pi` to the class of exact
pairs, of any dimension, whose two vertices factor through congruence
quotients of arbitrary levels. This is the quantity (DCC1) of
`dv-distance-is-defect-plus-congruence-capture`. For an exact pair
`pi = (pi_+, pi_-)` put

```text
A_+(pi) = inf { d_2(pi_+, rho) : rho exact rep of C factoring through some SL_2(Z/N), any dimension },
```

and define `A_-(pi)` in the same way.

**Theorem.** There is a constant `C < infinity`, depending only on the fixed
generating sets and Selberg's constant, and not on the dimension or on any
congruence level, such that every exact pair `pi` satisfies

```text
A_+(pi) <= A_cong(pi) <= 2 A_+(pi) + C sqrt( def(pi) + A_+(pi) ),     (CT1)
```

and the same with `A_-` in place of `A_+`.

**Exact case.** If `pi_+` factors through `SL_2(Z/m)`, then `pi_-` lies within
`C sqrt(def(pi))` of an exact representation of `C` that factors through
`SL_2(Z/2m)`, and the resulting pair (after trivial padding of `pi_+`) is an
exact congruence pair at distance `<= C sqrt(def(pi))` from `pi`.

**Consequences.** These use the established uniform congruence-pair repair
`congruence-repair-bypasses-koopman-cycle-firewalls`.

1. If `def(pi_n) -> 0` and `A_+(pi_n) -> 0`, then `D(pi_n) -> 0`. Since also
   `A_+(pi) <= D(pi)`, Dogon--Vigdorovich Question 1.4 is **equivalent to
   one-vertex congruence capture** (`iwahori-one-vertex-congruence-capture`):
   `def(pi_n) -> 0` implies `A_+(pi_n) -> 0`. The quantitative (DCC2) of
   `dv-distance-is-defect-plus-congruence-capture` would make this explicit,
   but it is not needed here.
2. **Obstruction for the negative side.** Every countersequence to Question
   1.4 has `def(pi_n) -> 0` and `D(pi_n) >= delta_0 > 0`. Along it, **both**
   `liminf A_+(pi_n) > 0` and `liminf A_-(pi_n) > 0`, and the same holds on
   every subsequence. So no construction in which either vertex is
   congruence, or tends to the congruence locus, can refute the question.
   This includes every construction that fixes one vertex as a finite-quotient
   or regular-congruence representation and varies only the other vertex.
3. Once the question has a positive answer, compatible pairs restrict to odd
   congruence representations
   (`finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence`). So
   capture of one vertex by congruence representations of *any* level upgrades
   to capture by *odd* level. The even-level part of the capture target costs
   nothing.

The proof is `iwahori-congruence-capture-transfer-proof`. It induces the
transported first vertex from `B_-` to `C`. The induced representation is a
congruence representation that almost contains the second vertex. Selberg
property `(tau)` is then used on the conjugation representation to round the
almost-invariant projection to an exact subrepresentation.
