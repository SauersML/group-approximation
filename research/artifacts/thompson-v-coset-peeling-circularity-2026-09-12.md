# Surjunctivity of Thompson's V and the Leavitt units: where coset peeling stops

Lane `gk-leavitt-positive`, 2026-09-12. Supports the claims
`thompson-v-coset-stabilizers-contain-copies-of-v`, `thompson-v-surjunctive`
and `leavitt-unit-group-surjunctive`, and the dead route
`thompson-v-surjunctive-via-coset-peeling`.

## 0. Summary

* Surjunctivity of Thompson's group `V` was not recorded in the graph. It is now
  the open root `thompson-v-surjunctive`. The positive dual of
  `leavitt-unit-group-nonsurjunctive` is the open root
  `leavitt-unit-group-surjunctive`, and `V <= R^x` gives the route
  `thompson-v-surjunctive-from-leavitt-units`.
* **Permanence cannot reach either group unless `V` is sofic.** By
  `gottschalk-counterexamples-lie-outside-the-permanence-closure` (and
  `sofic-permanence-closure-omits-simple-fa-nonsofic-groups`,
  `fixed-host-outside-sofic-permanence-closure`), no finitely presented infinite
  simple nonsofic group lies in the permanence closure of the sofic groups.
  `R^x` is such a group. `V` is finitely presented, infinite and simple
  (`thompson-v-finitely-presented-infinite-simple`), so `V` lies in that closure
  if and only if `V` is sofic, and `thompson-v-not-sofic` is open. This kills the
  lane's planned step "prove `V`, then `R^x`, by extending the permanence
  theorems".
* **The Cantor-set replacement for marked sites is circular** (Theorem 1 below).
  The peeling proofs replace an injective automaton by its transplants to coset
  spaces and finish with the coset-region lemma over a surjunctive stabilizer
  group. For `V`, every natural stabilizer in the separating families that the
  Cantor action provides contains a rigid stabilizer, and every rigid stabilizer
  is isomorphic to `V`. The rigid-stabilizer transplant is a map over a copy of
  `V` with an infinite compact alphabet. This kills the lane's planned step
  "extend marked-site peeling to Thompson-like and topological full groups
  through their Cantor action".
* What remains for a positive answer is an argument over `V` or `R^x` itself
  that does not pass to smaller groups: Section 4.

## 1. Conventions

`C = {0,1}^N`. An element of `V` is given by two complete prefix codes
`(a_1..a_k)`, `(b_1..b_k)` and acts by `a_i w -> b_i w`. For a clopen `U`, the
rigid stabilizer `V_U` is the set of elements equal to the identity off `U`.
Automata use `tau(x)(g) = mu((x(gm))_(m in M))`. For `H <= V` the transplant to
`Omega = H\V` is `tau_Omega(y)(Hw) = mu((y(Hwm))_m)`. It is injective when
`tau` is, and if it is surjective for a family of `H` separating every finite
set, then `tau` is surjective (Lemmas 1.1 and 1.2 of
`research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md`).

## 2. Theorem 1

**Theorem 1.**

1. For every nonempty clopen `U` in `C`, `V_U` is isomorphic to `V`.
2. For every finite set `P` of points of `C`, the pointwise stabilizer `V_(P)`
   contains `V_U` for some nonempty clopen `U`, hence a copy of `V`. The family
   `{V_(P)}` separates finite subsets of `V`.
3. For clopens `D_1, ..., D_r`, `V_(D_1) intersect ... intersect V_(D_r) = V_(D_1 intersect ... intersect D_r)`.
   The family `{V_D : D clopen, C \ D nonempty}` separates finite subsets of `V`.
4. Let `D` be a clopen with `U = C \ D` nonempty. The transplant of `tau` to
   `V_D\V` commutes with a free action of `V_U`, a copy of `V`. As a
   `V_U`-space, `B^(V_D\V)` is `(B^E)^(V_U)` for a countably infinite set `E`, so
   the transplant is a continuous `V_U`-equivariant injection of a full shift
   over `V_U` with infinite compact alphabet `B^E`. Over every group that class
   contains injective maps that are not surjective.

So the stabilizer groups available to the coset-region step are copies of `V`,
or contain one, and the rigid-stabilizer transplant lands in a class of maps
where surjunctivity of `V_U` gives nothing.

*Proof.*

(1) Write `U` as a disjoint union of cylinders `[c_1], ..., [c_q]`. Choose a
complete prefix code `(d_1..d_q)` and the prefix homeomorphism
`theta: [c_i] w -> d_i w` from `U` onto `C`. Then `g -> theta g theta^-1`
(restricted to `U`) is an isomorphism `V_U -> V`. It is well defined and onto
because conjugating a prefix-replacement homeomorphism of `U` by a finite prefix
recoding gives a prefix-replacement homeomorphism of `C`, and conversely.

(2) `C \ P` is open and nonempty because `C` has no isolated points, so it
contains a nonempty cylinder `U`, and `V_U <= V_(P)`. For separation, let
`w != w'` lie in a finite `F`. `Hw = Hw'` exactly when `w' w^-1` fixes `P`
pointwise. Every nontrivial `g = w'w^-1` moves some point, and moved points form a
nonempty open set. Choose one moved point for each of the finitely many pairs and
let `P` collect them. Then no `w'w^-1` fixes `P`, so `pi_(V_(P))` is injective
on `F`.

(3) An element that is the identity off each `D_i` is the identity off their
intersection, and conversely. For separation, a nontrivial `g` is not the
identity on some cylinder `[c]`, so `g` is not in `V_D` whenever `D` misses a
point of `[c]` that `g` moves. Take `D` to be the complement of a union of small
cylinders around one moved point of each of the finitely many `w'w^-1`. This `D`
is clopen with nonempty complement, and none of those elements lies in `V_D`.

(4) *Cosets.* `V_D w = V_D w'` iff `w'w^-1` is the identity off `D` iff
`w^-1` and `w'^-1` agree on `U`. So `V_D\V` is the set of restrictions
`w^-1|_U`. These are prefix-replacement injections of `U` onto a clopen `E'`
whose complement is nonempty. The right action is `(V_D w).u <-> u^-1 o (w^-1|_U)`.

*Commuting free action.* For `g in V_U`, `g V_D g^-1 = V_D` because `g` fixes
`D` pointwise. So `g.(V_D w) = V_D g w` is well defined on cosets and corresponds
to precomposition `w^-1|_U -> (w^-1|_U) o g^-1|_U`. It commutes with the right
action, hence with every transplant, and it is free because a prefix injection
precomposed with a nontrivial homeomorphism of `U` changes. Its orbits are
indexed by the image `E'`, and the set `E` of admissible images (nonempty clopens
with nonempty complement) is countably infinite. Choosing one base injection
`phi_(E'): U -> E'` for each `E'` identifies `V_D\V` with `E x V_U` equivariantly,
so `B^(V_D\V) = (B^E)^(V_U)`.

*Infinite alphabet.* Over any group `G`, with alphabet `K = B^N` and `B` having
at least two symbols, the map `(Sy)(g)_0 = b_0`, `(Sy)(g)_(n+1) = y(g)_n` is
continuous, `G`-equivariant, injective and not surjective. So equivariance,
continuity and injectivity over `V_U` with alphabet `B^E` do not force
surjectivity. Any surjectivity of the transplant has to come from its particular
form, which in these coordinates reads `y` at `(m^-1 E', c(m, E') h)` with
`c(m, E') = phi_(m^-1 E')^-1 o m^-1 o phi_(E')` in `V_U`. QED

## 3. The dead route and what it records

`thompson-v-surjunctive-via-coset-peeling` is the route "prove `V` surjunctive by
transplanting an injective automaton to the coset spaces of the point
stabilizers or rigid stabilizers of the Cantor action, and finish each stratum
with the coset-region lemma". The coset-region lemma needs a surjunctive group
`K` whose right cosets carry the rules. By Theorem 1 the groups these families
offer are copies of `V` or contain one. The step therefore assumes the target.
This is the circularity the permutational wreath proofs avoid: there the
stabilizer intersections are subgroups of the base, which is outside the
nonsofic kernel.

`R^x` contains `V` (`leavitt-cylinder-swaps-generate-thompson-in-el`), so any
proof for `R^x` proves `V` surjunctive and passes through the same obstruction.
No statement about coset families of other `R^x`-actions is claimed here.

## 4. What a head-on proof has to supply

* **Not counting.** The sofic radical of `R^x` is `R^x`
  (`sofic-radical-localizes-garden-of-eden-windows` localizes every Garden of
  Eden there). For `V`, counting works exactly when `V` is sofic.
* **Not permanence.** By the closure theorems above.
* **Not Cantor-orbit encodings.** By
  `full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`.
* **Not coset peeling through the Cantor action** (Theorem 1).

What is left is an argument that proves surjectivity for automata whose memory
generates `V`, working over `V` directly. It could use self-similarity
(`V_U ~= V` for every nonempty clopen `U`, and commuting copies on disjoint
clopens) as an induction on the automaton, not on the group. No such induction
is known. For instance, conjugating the memory into a small cylinder does not
lower any complexity the peeling proofs use, because the rules still read the
whole configuration. That is the open content of `thompson-v-surjunctive`.
