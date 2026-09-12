# The surjunctivity permanence envelope and finitely presented simple groups

Lane `gk-leavitt-positive`, 2026-09-12. Cited by `thompson-v-surjunctive`.

**Relation to landed nodes.** The main theorem here was found independently of,
and at the same time as, two peer landings:
`gottschalk-counterexamples-lie-outside-the-permanence-closure` (with the
local-embedding transfer `strict-pairs-transfer-to-table-realizations`) and
`sofic-permanence-closure-omits-simple-fa-nonsofic-groups`. So Lemma 1,
Proposition 2 and Theorem 3 below are not landed as separate nodes. This is a
second write-up of that obstruction. What it adds:
closure under residual membership (E5) and under free and direct products (E7);
the characterization "a finitely presented infinite simple group lies in the
envelope if and only if it is sofic", used for `V` in `thompson-v-surjunctive`;
and the per-theorem kernel analysis of Section 6. The Cantor-set coset analysis
of Section 7 is landed separately as
`thompson-v-coset-stabilizers-contain-copies-of-v`, with its own artifact.

## 0. The question and the answer

The landed permanence theorems prove surjunctivity for permutational wreath
products with residually finite lamps, finitary split extensions, group doubles,
graph folds and graph wreaths with LEF lamps, always over a surjunctive base.
Can the same method be extended to the binary Leavitt unit group
`R^x = L_(F_2)(1,2)^x`, or to Thompson's group `V` inside it?

No method of that shape reaches `R^x`, and it reaches `V` exactly when `V` is
sofic. The reason is short. Every nontrivial homomorphism out of a simple group
is injective. So a simple subgroup of an extension lies inside the kernel or
embeds in the quotient, and a local embedding of a finitely presented simple
group is an embedding. Extension-type permanence therefore never manufactures a
simple group that its inputs did not already contain.

Surjunctivity of `V` was not recorded anywhere in the graph before this
landing. It is now the open root `thompson-v-surjunctive`.

## 1. Conventions

A group `G` is **locally embeddable** into a class `K` of groups if for every
finite `F` in `G` there are `H` in `K` and an injective map `phi: F -> H` with
`phi(ab) = phi(a) phi(b)` whenever `a, b, ab` lie in `F`.

A cellular automaton over `G` with finite alphabet `A` has finite memory `M`
and local rule `mu: A^M -> A`, and `tau(x)(g) = mu((x(gm))_(m in M))`. It
commutes with the left shift `(h.x)(g) = x(h^-1 g)`.

## 2. Lemma 1: local embeddings of finitely presented simple groups

**Lemma 1.** Let `S` be a nontrivial finitely presented simple group and `K` a
class of groups closed under subgroups and isomorphism. If `S` is locally
embeddable into `K`, then `S` belongs to `K`.

*Proof.* Fix a finite presentation `S = <X | r_1, ..., r_k>` and a nontrivial
`g in S` with a word `w` for it. Let `F` contain `1`, every `x` and `x^-1` for
`x in X`, every prefix (as an element of `S`) of every `r_i`, and every prefix
of `w`. Take `phi: F -> H`, `H in K`, injective and multiplicative on `F`.

From `1.1 = 1` we get `phi(1) = 1`, and from `x x^-1 = 1` we get
`phi(x^-1) = phi(x)^-1`. If `p` and `px` (or `px^-1`) are consecutive prefixes
of a relator, multiplicativity gives `phi(px) = phi(p) phi(x)`. By induction
along the relator, the word `r_i` evaluated at `(phi(x))_x` equals
`phi(r_i) = phi(1) = 1`. So `x -> phi(x)` defines a homomorphism
`psi: S -> H`. The same induction along `w` gives `psi(g) = phi(g)`, which is
not `phi(1) = 1` because `phi` is injective. Hence `psi` is nontrivial, its
kernel is a proper normal subgroup, so it is trivial, and `S` is isomorphic to
`psi(S) <= H`. QED

The hyperlinear analogue is `fp-simple-groups-escape-soft-hyperlinear-permanence`.

## 3. Proposition 2: local embeddability preserves surjunctivity

**Proposition 2.** If `G` is locally embeddable into the class of surjunctive
groups, then `G` is surjunctive.

*Proof.* Let `tau` over `G` be injective with memory `M` and rule `mu`.

*Decoder.* `A^G` is compact and `tau` is continuous and injective, so `tau` is
a homeomorphism onto its closed image `Y`, and `tau^-1: Y -> A^G` commutes with
the shift. By compactness there are a finite `D` and `nu_0` with
`tau^-1(y)(1) = nu_0(y|_D)` for `y in Y`. Equivariance gives
`tau^-1(y)(g) = nu_0((y(gd))_(d in D))`. Extending `nu_0` arbitrarily to all of
`A^D` gives a cellular automaton `sigma` with `sigma o tau = id`. This identity
holds at every cell once it holds at `1`, and at `1` it reads

```text
nu( ( mu((x(dm))_(m in M)) )_(d in D) ) = x(1)      for every x.          (I)
```

(I) depends only on `x` restricted to `DM union {1}` and on the incidence map
`(d, m) -> dm`.

*Orphan.* If `tau` is not surjective, `Y` is a proper closed subset, so some
finite `Omega` and pattern `p in A^Omega` occur in no `tau(x)`. Equivalently,
no pattern `q` on `Omega M` satisfies `mu((q(om))_m) = p(o)` for all `o` in
`Omega`. (O)

*Transfer.* Put `F = {1} union M union D union Omega union DM union Omega M` and
take `phi: F -> H` with `H` surjunctive, injective and multiplicative on `F`.
Define `tau_H` with memory `phi(M)` and rule `mu`, and `sigma_H` with memory
`phi(D)` and rule `nu`. Since `phi(d)phi(m) = phi(dm)`,
`phi(o)phi(m) = phi(om)` and `phi` is injective on these sets, patterns on
`phi(DM union {1})` and on `DM union {1}` correspond with the same incidence. So
(I) holds over `H` at `1`, hence everywhere, `sigma_H o tau_H = id`, and
`tau_H` is injective. As `H` is surjunctive, `tau_H` is surjective. So the
pattern `p o phi^-1` on `phi(Omega)` has a preimage configuration. Its
restriction to `phi(Omega M)`, pulled back along `phi`, is a pattern `q`
contradicting (O). QED

This is the finite decoder-and-orphan certificate argument used for finite lamp
tables in `research/artifacts/lef-graph-wreath-surjunctivity-2026-09-12.md`,
stated for an arbitrary group and arbitrary surjunctive targets. No novelty is
claimed for it.

## 4. Theorem 3: the permanence envelope

**Definition.** The **permanence envelope** `E` is the smallest class of groups
that contains every sofic group and is closed under:

* **(E1)** subgroups and isomorphism;
* **(E2)** directed unions;
* **(E3)** overgroups containing a member with finite index;
* **(E4)** local embeddability into `E`;
* **(E5)** residual membership: `G` belongs if for every `g != 1` some
  homomorphism from `G` to a member of `E` does not kill `g`;
* **(E6)** extensions with sofic kernel: `N` normal in `G`, `N` sofic and `G/N`
  in `E`;
* **(E7)** free products and direct products of two members.

`E` is an envelope, not a class of surjunctive groups. (E6) with an arbitrary
sofic kernel is not a known surjunctivity permanence. Theorem 3 bounds what any
combination of these operations can certify.

**Theorem 3.** Every finitely presented infinite simple group in `E` is sofic.
So a finitely presented infinite simple group belongs to `E` if and only if it
is sofic, and every group containing a nonsofic finitely presented infinite
simple subgroup lies outside `E`.

*Proof.* Let `P` be the class of groups all of whose finitely presented infinite
simple subgroups are sofic. `P` contains every sofic group, because soficity
passes to subgroups. Minimality of `E` gives `E <= P` once `P` is closed under
(E1)-(E7). Let `S` be a finitely presented infinite simple subgroup of the new
group `G` in each case.

* (E1) A subgroup of `S`'s ambient member already contains `S`.
* (E2) `S` is finitely generated, so it lies in one member of the union.
* (E3) Let `L <= G` have finite index with `L in P`. Then `S intersect L` has
  finite index in `S`, so it contains a finite-index normal subgroup of `S`. That
  subgroup is `S`, since an infinite simple group has no proper finite-index
  normal subgroup. So `S <= L`.
* (E4) `S` is locally embeddable into `P` (restrict the local embeddings of
  `G`), and `P` is closed under subgroups. By Lemma 1, `S` is isomorphic to a
  subgroup of a member of `P`, hence sofic.
* (E5) Pick `s != 1` in `S` and a homomorphism `f` to a member of `P` with
  `f(s) != 1`. Then `f|_S` is nontrivial, hence injective, and `f(S)` is a
  finitely presented infinite simple subgroup of a member of `P`. So `S` is sofic.
* (E6) `S intersect N` is normal in `S`. If it is `S`, then `S <= N` is sofic.
  If it is trivial, `S` embeds in `G/N in P`, and its image is sofic.
* (E7) For `A x B`, one projection restricts to a nontrivial homomorphism on `S`,
  which is then injective. For `A * B`, the Kurosh subgroup theorem writes `S`
  as a free product of a free group and conjugates of subgroups of `A` and `B`.
  A nontrivial free product has a proper nontrivial normal subgroup, and a
  nontrivial free group maps onto `Z`. So `S` is conjugate into `A` or `B`.

In every case `S` is sofic. QED

## 5. Corollary 4: the Leavitt units and Thompson's V

* `R^x` is finitely presented (`leavitt-unit-group-finitely-presented`), simple
  (`binary-leavitt-unit-group-is-simple`) and nonsofic
  (`openai-leavitt-unit-nonsofic`). So `R^x` is not in `E`, and neither is any
  group containing it.
* `V` is finitely presented, infinite and simple
  (`thompson-v-finitely-presented-infinite-simple`). So `V` is in `E` if and
  only if `V` is sofic, which is open (`thompson-v-not-sofic`).

## 6. Every group-level surjunctivity theorem in the graph stays inside E

As of main `ce355bb6ec`, the established group-class theorems are the
following. Each applies to a surjunctive base `G`, and the bases established so
far lie in `E` by the same analysis, inductively.

* **Residually finite and amenable groups**, and Gromov--Weiss for sofic groups.
  These are sofic.
* **Finitary split extensions** (`finitary-split-extension-surjunctivity-permanence`).
  Detection (A1) puts finitely many nontrivial elements into one residually
  finite `N_S` simultaneously, so the kernel `N` is residually finite, hence
  sofic. This is (E6).
* **Permutational wreath products with residually finite lamps**
  (`rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`). They are an
  instance with `N` a direct sum of residually finite groups.
* **Group doubles** (`doubles-of-surjunctive-groups-are-surjunctive`).
  `G *_Gamma G ~= F semidirect G` with `F` free. This is (E6).
* **Graph folds** (`graph-folds-over-surjunctive-groups-are-surjunctive`).
  `f: P -> G` is injective on every vertex group, so `ker f` meets every
  conjugate of a vertex group trivially. It acts freely on the Bass--Serre tree
  and is free. `P` is free-by-`f(P)` with `f(P) <= G`, which is (E6) and (E1).
* **Graph wreaths with LEF lamps** (`lef-lamp-graph-wreaths-are-surjunctive`).
  Their proof locally embeds the group into graph wreaths with finite lamps over
  the same actor and graph (E4). Those have graph products of finite groups as
  kernels, residually finite by Green's theorem, so they are (E6).

The automaton-class theorems (`surjunctive-guard-subgroups-force-surjectivity`,
`certificate-controlled-routing-is-surjunctive`, the quadratic-feedback
families, `stable-three-factor-reduction-proves-gottschalk`) are statements about
classes of automata over arbitrary groups, not group permanence. Theorem 3 says
nothing about them.

## 7. Where the extension to V and R^x fails, concretely

**The failure point.** The peeling proofs end in the coset-region lemma
(Lemma 3.1 of `research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md`),
which needs surjunctivity of stabilizer intersections `G_U` of the base, and
the base sits outside the kernel. A simple group has no kernel to peel.

**The natural coset families of V contain V again.** Let `C = {0,1}^N` and let
`V_U` be the rigid stabilizer of a clopen `U` (elements that are the identity
off `U`). For every nonempty clopen `U`, `V_U` is isomorphic to `V`: write `U`
as a finite disjoint union of cylinders and conjugate by a prefix homeomorphism
from `U` onto one cylinder, whose rigid stabilizer is a copy of `V`.

* The pointwise stabilizer of a finite set of points contains `V_U` for a
  nonempty clopen `U` missing those points, because `C` has no isolated points.
* An intersection of rigid stabilizers `V_(C \ U_i)` equals `V_(C \ union U_i)`,
  which contains `V_U` for any nonempty clopen `U` in the complement of the union.

These are the families that separate finite sets. Every stabilizer intersection
therefore contains a copy of `V`, and the coset-region step would need
surjunctivity of a group containing `V`. The induction is circular.

**The transplant does not reduce the automaton either.** On `V_U\V`, cosets
correspond to restrictions of `w^-1` to `D = C \ U`, with right multiplication
acting by post-composition. The rigid stabilizer `V_D` acts freely by
precomposition and commutes with the transplanted automaton. Choosing base
partial maps for each clopen image `E`, the automaton becomes a `V_D`-equivariant
map on configurations indexed by `(E, h)`, reading
`(m^-1 E, c(m, E) h)`. The factor `c(m, E)` ranges over infinitely many elements
of `V_D` as `E` varies. So this is not a finite-memory automaton over `V_D`; it
is a continuous equivariant map with an infinite site set, a weaker hypothesis
than surjunctivity of `V_D ~= V` can use.

## 8. What a positive proof for R^x must supply

* **Not counting.** Garden-of-Eden windows of injective automata fold on
  sofic-invisible elements (`sofic-radical-localizes-garden-of-eden-windows`),
  and the sofic radical of the nonsofic simple group `R^x` is all of `R^x`.
* **Not extension, local or residual permanence** (Theorem 3).
* **Not a Cantor-orbit encoding**
  (`full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`).

What remains is an internal argument over `R^x` itself: a way to prove surjectivity
of an injective automaton whose memory generates a nonsofic simple group, where
every subgroup in the argument's natural families is at least as large as `V`.
An argument of that kind would be the first surjunctivity proof for a group not
known to be sofic that is not assembled from sofic pieces. The same obstruction
tells the negative lanes that finitely presented simple nonsofic groups are
exactly where the existing positive toolkit is silent.
