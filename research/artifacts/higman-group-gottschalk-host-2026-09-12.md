# Higman's group as a Gottschalk host

Lane `w5-free-neg-c`, 2026-09-12. Artifact for `higman-group-nonsurjunctive`.

## 0. The host and why it is new

Let

```text
H = < a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >,     x^y = y^(-1) x y.
```

Facts already on main at statement level (`linear-sterility-does-not-obstruct-division-embedding`,
sources read there): `H` is torsion-free and left-orderable (Rivas--Triestino), has no nontrivial
finite quotient (Higman 1951), every finite-dimensional representation of `H` over every field is
trivial, and `k[H]` embeds in a division ring when `char k = 0` (Fisher--Sanchez-Peralta 3.14).
Adding the four relations in the abelianization kills every generator, so `H` is perfect.

Whether `H` is sofic is open. (Helfgott--Juschenko relate soficity of `H` to a conjecture on short
cycles of `x -> 2^x` modulo primes; this lane did not read that paper and no node depends on it.)

**Why a Gottschalk host.**

* **No landed theorem reaches it.** `H` is finitely presented and not residually finite, so it is not
  LEF; it has no finite quotient at all, so every permanence device that feeds on finite quotients or
  residually finite kernels is void; its soficity is open.
* **Non-unimodular pieces.** Each consecutive pair generates `BS(1,2)`, whose Bass--Serre tree is the
  end-fixing 3-regular tree with modular function 2. The only equivariant strict maps known on such
  trees are copying maps, and `H` carries four of them on coset spaces (Section 2). The four expansion
  directions form the cycle `a -> b -> c -> d -> a`, which is exactly what kills finite quotients. `H`
  itself is discrete, hence unimodular, and perfect, so no level function exists.
* **Disjoint from the swarm.** None of the hosts of RULES.md WAVE 3--5 (Leavitt unit groups, V, E x| V,
  Radu's lattice, Clifford covers, lamp quotients of W, Deligne's cover) is `H`, and `H` has none of their
  features: no torsion, no compression `R = R^2`, no finite quotients, no central extension.

## 1. Two splittings over free groups, and the edge-group filter

Write `B(x,y) = < x, y | y^x = y^2 >`, a copy of `BS(1,2) = Z[1/2] x| Z` in which `x` is the stable
letter (it maps to a generator of the quotient `Z`) and `y` lies in the base `Z[1/2]`.

**Theorem 1.1 (splittings).** Let `G_1 = <a,b,c>`, `G_2 = <c,d,a>`, `G_3 = <b,c,d>`, `G_4 = <d,a,b>` be
defined by the two relations of `H` among their letters. Then:

1. `G_1 = B(a,b) *_<b> B(b,c)` and `G_2 = B(c,d) *_<d> B(d,a)`; similarly for `G_3, G_4`.
2. `{a, c}` freely generates a free subgroup `F_ac` of `G_1` and of `G_2`, and `{b, d}` one of `G_3`
   and `G_4`.
3. `H = G_1 *_(F_ac) G_2 = G_3 *_(F_bd) G_4`. In particular each `G_i` and each `B(x,y)` embeds in `H`.
4. Each `G_i` is sofic.

*Proof.*
1. A presentation of an amalgam is the union of the presentations with the amalgamated generator
   identified. The letter `b` has infinite order in `B(a,b)` and in `B(b,c)`.
2. In `B(a,b)` the quotient to `Z` sends `a -> 1`, `b -> 0`, so `a^k in <b>` forces `k = 0`. In
   `B(b,c)` the quotient sends `b -> 1`, `c -> 0`; if `c^l = b^m` then `m = 0`, so `c^l = 1` and `l = 0`.
   A nontrivial reduced word in `a, c` is an alternating product of nonzero powers of `a` and `c`,
   that is, an alternating product of elements of `B(a,b) \ <b>` and `B(b,c) \ <b>`. By the normal form
   theorem for amalgams it is not 1. In `G_2`, `c` is the stable letter of `B(c,d)` and `a` lies in the
   base of `B(d,a)`, and the same argument applies with `<d>` amalgamated.
3. The presentation of `G_1 *_(F_ac) G_2`, identifying `a` with `a` and `c` with `c`, is the presentation
   of `H`. Factors of an amalgam embed. The cyclic relabelling `a -> b -> c -> d -> a` preserves the
   relator set, which gives the second splitting.
4. `BS(1,2)` is solvable, hence amenable, and `<b> = Z` is amenable. Amalgams of sofic groups over
   amenable subgroups are sofic (literature input, Elek--Szabo, as cited by
   `amenable-envelope-magnus-piece-sofic-proof`; not re-read here). QED

**Theorem 1.2 (edge-group filter).** Let `S <= H` be finitely generated and nonsofic. For each of the two
splittings of Theorem 1.1, `S` fixes no vertex and no end of the Bass--Serre tree, and some edge
stabilizer `S cap g F g^(-1)` (with `F = F_ac`, resp. `F_bd`) is a nonabelian free group. In particular `S`
lies in no conjugate of `G_1, ..., G_4`.

*Proof.* Let `S` act on the Bass--Serre tree `T` of `H = G_1 *_(F_ac) G_2`.
* **Every element elliptic.** A finitely generated group of elliptic automorphisms fixes a vertex
  (Serre), so `S` lies in a conjugate of `G_1` or `G_2`, which is sofic.
* **A hyperbolic element and a fixed end.** The Busemann homomorphism `S -> Z` has kernel `K` consisting
  of elements that fix a ray to the end. Finitely many of them fix a common ray, so `K` is locally
  contained in vertex stabilizers, hence locally sofic, hence sofic. Then `S` is sofic by
  `sofic-kernel-amenable-quotient-permanence`.
* **Otherwise.** `S` acts minimally on its minimal subtree with finite quotient graph, so `S` is the
  fundamental group of a finite graph of groups whose vertex groups lie in conjugates of `G_1, G_2`
  (sofic) and whose edge groups are `S cap g F_ac g^(-1)`, subgroups of a free group. If every edge group
  were amenable, `S` would be sofic (literature input: graphs of groups with sofic vertex groups and
  amenable edge groups are sofic, Elek--Szabo and Ciobanu--Holt--Rees as cited by
  `amenable-envelope-magnus-piece-sofic-proof`; not re-read). Amenable subgroups of free groups are
  cyclic, so some edge group is nonabelian free.
The same argument runs on the tree of `G_3 *_(F_bd) G_4`. QED

**Corollary 1.3 (memory filter).** Let `tau` be a strict automaton on `A^H`. By
`strict-composites-have-strict-factors`, some factor of `tau` is strict and its memory generates a
subgroup `S` that is not surjunctive, hence not sofic (`sofic-groups-are-surjunctive`). So `S` meets a
conjugate of `F_ac = <a,c>` and a conjugate of `F_bd = <b,d>` in nonabelian free groups, and is contained
in no conjugate of a subgroup generated by three consecutive generators. Every automaton whose memory
lies in a conjugate of the subgroup generated by three consecutive generators is surjunctive. (Three consecutive
Baumslag--Solitar pieces already generate all of `H`; the filter is about three consecutive generators.)

## 2. The four copying maps, and why they are not yet a design

**Lemma 2.1.** For `x` in `{b,c,d,a}` let `x'` be the preceding generator (`b' = a`, `c' = b`, `d' = c`,
`a' = d`), so that `x^(x') = x^2`. Then `p_x(g<x>) = g x' <x>` is a well-defined, left-equivariant,
exactly two-to-one map `H/<x> -> H/<x>`. Hence `y -> y o p_x` is an injective, non-surjective,
`H`-equivariant continuous self-map of `A^(H/<x>)`.

*Proof.* Well-defined: `g x^k x' = g x' (x'^(-1) x^k x') = g x' x^(2k)`. Fibres: `g x' <x> = h x' <x>` iff
`h^(-1) g in x' <x> x'^(-1) = < x' x x'^(-1) >`. Since `(x' x x'^(-1))^2 = x' x^2 x'^(-1) = x`, the subgroup
`<x>` has index at most 2 in it, and exactly 2: `x' x x'^(-1) = x^m` would give `x = x^(2m)`, impossible in a
torsion-free group. QED

**Remark 2.2 (the defect is absorbed by right translation).** Identify `A^(H/<x>)` with the configurations
on `H` that are right `<x>`-invariant. On these, `y o p_x` is the restriction of the right translation
`R(y)(g) = y(g x')`, which is a bijection of `A^H`. It maps the `<x>`-invariant configurations onto the
`x'<x>x'^(-1)`-invariant ones, a proper subshift. So the four copying maps carry no strictness of the full
shift by themselves: the missing information sits in the configurations that are not `<x>`-invariant.
This is the unimodularity of `H` in its simplest form. A strict automaton on `A^H` therefore cannot be a
translation on any piece; by Corollary 1.3 its memory must also meet `<a,c>` and `<b,d>` in nonabelian free
groups.

## 3. Linear side and where this stops

* **One track.** If `H` has unique products, `F_p[H]` is a domain, so `ab = 1` forces `ba = 1`, and every
  linear automaton on `(F_p)^H` is surjunctive. Left-orderable groups are unique-product groups; this is a
  standard import (Passman's book) that this lane did not re-read, and it is recorded here, not as a node.
* **Several tracks.** Stable finiteness of `F_p[H]` is open. The division-ring embedding of
  Fisher--Sanchez-Peralta is stated only in characteristic zero, and finite alphabets live in characteristic
  `p`. A one-sided inverse pair in `M_n(F_p[H])`, `n >= 2`, would refute Gottschalk.
* **Where it stops.** No candidate strict automaton is known. What is known is where one must live: a memory
  mixing all four Baumslag--Solitar pieces through nonabelian free edge groups in both splittings, with
  strictness not coming from any single copying map.

## 4. Higman's group is a twisted double, with a three-generator overgroup

**Theorem 4.1.** Let `G_1 = <a,b,c | b^a = b^2, c^b = c^2>`, `F = <a,c> = F_2` (free by Theorem 1.1), and
`theta : F -> F` the swap `a <-> c`.

1. `H = G_1 *_theta G_1`, the amalgam of two copies of `G_1` identifying `f` in the first copy with `theta(f)` in
   the second.
2. `alpha : a -> c, b -> d, c -> a, d -> b` is an automorphism of `H` of order two.
3. `E = H x|_alpha Z/2` has the presentation `E = < a, b, t | t^2, b^a = b^2, c^b = c^2 >` with `c = t a t`,
   and `E = G_1 *_F (F x|_theta Z/2)`.
4. `H` is surjunctive iff `E` is (`surjunctivity-is-a-commensurability-invariant`).
5. The sign character `chi : E -> {+-1}`, `t -> -1`, `a, b -> 1`, exists. For odd `p`, the averaging idempotents
   `(1 +- t)/2` of `F_p[E]` are killed by `chi` or by the trivial character, so no averaging-idempotent corner
   witness `c e b = 1` exists over `E`.

*Proof.*
1. `psi : G_1 -> G_2 = <c,d,a>`, `a -> c`, `b -> d`, `c -> a`, sends the relators `b^a b^(-2)`, `c^b c^(-2)` to
   `d^c d^(-2)`, `a^d a^(-2)`; the map `c -> a`, `d -> b`, `a -> c` inverts it. On `F`, `psi` restricts to
   `theta` followed by `F <= G_2`. Transporting `G_2` back along `psi` turns the identification of Theorem 1.1
   into `f ~ theta(f)'`, since `theta` is an involution.
2. `alpha` permutes the four relators (`b^a = b^2 -> d^c = d^2 -> b^a = b^2`, `c^b = c^2 -> a^d = a^2 -> c^b = c^2`),
   and `alpha^2 = id`.
3. The semidirect product is presented by the four relators, `t^2`, and `tat = c`, `tbt = d`, `tct = a`,
   `tdt = b`. Eliminate `c = tat` and `d = tbt`. Then `tct = a` and `tdt = b` follow from `t^2 = 1`; `d^c = d^2` is
   the `t`-conjugate of `b^a = b^2`, and `a^d = a^2` is the `t`-conjugate of `c^b = c^2`. What remains is the stated
   presentation. The amalgam `G_1 *_F (F x|_theta <t>)` is presented by the relators of `G_1`, `t^2` and `tat = c`
   (`tct = a` follows), which is the same presentation.
4. `H` is the kernel of `E -> Z/2`, of index two.
5. The relators map to 1 under `chi`, because `tat -> 1`. `chi((1+t)/2) = 0` and the trivial character kills
   `(1-t)/2`; applying the character to `c e b = 1` gives `0 = 1`. QED

**What the twist does.** The untwisted double `G_1 *_F G_1` is surjunctive by
`doubles-of-surjunctive-groups-are-surjunctive`, since `G_1` is sofic. Higman's group is the same construction
with the identification twisted by `theta`, and the twist cannot be undone:

* `theta` extends to no endomorphism `beta` of `G_1`. Applying `beta` to `c^b = c^2` would give `a^(beta(b)) = a^2`,
  so `a` and `a^2` would be conjugate, but `G_1^ab = Z` is generated by the image of `a` (the relators force
  `b = c = 0`), where they map to 1 and 2.
* More simply, `H` is not a double of `G_1` over any subgroup: every such double maps onto `G_1` and so onto `Z`,
  while `H` has no nontrivial finite quotient.

So the twist is exactly what separates Higman's group from the doubles permanence theorem, and it is what closes
the pieces up into the doubling cycle.
