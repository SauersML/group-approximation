# LEF graph wreaths: surjunctivity without an action approximation

Date: 2026-09-12. Lane: `surjunctivity`.

This extends the established finitary split-extension result in
[`finitary-split-extension-surjunctivity-2026-09-11.md`](finitary-split-extension-surjunctivity-2026-09-11.md).
The new scope is arbitrary commutation graphs and LEF lamps. The elementary
finite-table step matters: a LEF lamp need not admit any nontrivial finite
quotient, so it cannot simply be substituted for a residually finite lamp
in the existing transplant proof.

## 1. Theorems and conventions

Let `G` act by graph automorphisms on a simplicial graph `Lambda` with
vertex set `X`. For a group `A`, let

```text
N = Lambda(A) = (*_(x in X) A_x) /
                  << [A_x,A_y] : {x,y} an edge >>.
```

The action is `alpha_g(a_x)=a_(gx)`, with no automorphism applied to `a`.
Set `W=Lambda(A) semidirect_alpha G` and use
`(n,g)(n',g')=(n alpha_g(n'),gg')`.

**Theorem 1.** If `A` is LEF, then `W` is surjunctive if and only if `G`
is surjunctive. There are no restrictions on the graph, stabilizers, or
cardinalities. LEF means that every finite subset `P` of `A` has an
injective map into a finite group preserving all products whose three
entries lie in `P`.

**Theorem 2.** For a Kun--Thom Theorem E pair `Gamma<G`, every invariant
graph on `G/Gamma` and every nontrivial countable LEF lamp `A` give a
surjunctive nonsofic graph wreath. If `A` is finitely generated, so is the
graph wreath. In particular all binary commutation graphs give finitely
generated witnesses for the existing surjunctive/nonsofic separation.

Theorem 1 is proved in Sections 2--5; Theorem 2 in Section 6. These are
class theorems with proofs, not computational observations. They do not
settle the universal Gottschalk conjecture or any hyperlinearity question.

## 2. Residually finite lamps: the induced-graph retractions

First assume `A` residually finite. For finite `S` contained in `X`, let
`N_S=Lambda[S](A)`, the graph product over the induced subgraph. Define

```text
p_S:N -> N_S,        p_S(a_x)=a_x if x in S, and 1 otherwise.
```

These are homomorphisms: each original within-vertex relation stays a
relation, while an edge commutator either stays an edge commutator or has
one trivial entry. The natural map `j_S:N_S->N` is a homomorphism and
`p_S j_S=id`, so it is injective. More generally the maps
`i_(U,S):N_U->N_S` for `U` contained in `S` are compatible split injections.
The graph must be induced here; imposing a new edge could kill a word.

The classical graph-product residual-finiteness theorem of Green gives
residual finiteness of every `N_S`; `N_empty=1`. Thus the data satisfy (D)
and (D') of the finitary theorem. For completeness the other three axioms
are exact word identities, as follows.

**Detection (A1).** Choose words for finitely many nonidentity `n_i`.
Take `S` containing all their vertex labels. Each `n_i` lies in `j_S(N_S)`
and `j_S p_S(n_i)=n_i`, so all `p_S(n_i)` are nonidentity.

**Finite support (A2).** For a word
`n=(a_1)_(x_1)...(a_l)_(x_l)`, use
`L(n)={x_1,...,x_l}`. Its translate is the same coefficient word with
vertex labels `g x_i`. If `g L(n)` misses `S minus U`, the letters retained
by `p_S` are precisely those retained by `p_U`. Hence, as group elements,

```text
p_S(alpha_g(n)) = i_(U,S)(p_U(alpha_g(n))).
```

Reduction of words after deletion introduces no issue: the two sides are
the identical retained word in `N_S`. Minimality of the chosen support is
unnecessary.

**Stabilizer invariance (A3).** If `k` fixes `S` pointwise, it preserves
`X minus S` setwise. On a vertex generator inside `S`, both `p_S alpha_k`
and `p_S` give `a_x`; on one outside `S`, both give `1`. The homomorphisms
therefore agree on all of `N`.

The finitary split-extension theorem now proves that `W` is surjunctive
when `G` is. Its finite quotients are quotients of `N_S`, not finite
quotients of `W`. No approximation of the action on `X` has been asserted.
This proves the residually finite lamp case, including all finite lamps.

## 3. Surjunctivity is closed under local embeddings

We give the finite-certificate proof of this standard closure fact, to
specify exactly the amount of multiplication data used in Section 5.

**Lemma 3.1.** If each finite subset of a group `H` embeds as a partial
multiplication table into some surjunctive group, then `H` is surjunctive.

*Proof.* Suppose instead that an injective cellular automaton
`tau:B^H->B^H` is not surjective, for a nonempty finite alphabet `B`.
Its image is compact, and the inverse from its image is continuous and
equivariant. Compactness gives a finite-memory rule recovering the input
symbol at `1` from an output pattern in the image. Extend that rule
arbitrarily on the other patterns. Equivariance extends it to a cellular
automaton `sigma` on the full shift with `sigma tau=id`.

Let `M,S` be memories of `tau,sigma`, containing `1`. Since the closed
image of `tau` is proper, some pattern `p` on a finite set `Omega` is not
in its language. Let

```text
F = {1} union M union S union Omega union SM union Omega M.
```

Take an injective partial multiplication map `eta:F->K` into a
surjunctive group. We have `eta(1)=1`, since `eta(1)^2=eta(1)`. In `K`
use the same local rules on `eta(M)` and `eta(S)`. The products
`eta(s)eta(m)=eta(sm)` have exactly the coincidence pattern of `SM`:
partial multiplication gives the equality, and injectivity of `eta`
gives both directions of the coincidence assertion. Consequently the
identity `sigma tau=id`, tested at `1` on every input assignment on
`SM`, holds for the transplanted automata on `K`. Translation gives the
identity everywhere, so the transplanted `tau_K` is injective.

The same argument for `Omega M` shows that the transplanted pattern
`p_K(eta(w))=p(w)` is missing from the image of `tau_K`. Any input
assignment on `eta(Omega)eta(M)` corresponds to one on `Omega M`, and
such a finite assignment extends to a configuration on `H`. Hence it
cannot produce `p`. This contradicts surjunctivity of `K`. QED.

This is the marked-limit closure theorem in finite-table form, not a new
general permanence claim. It also shows why matching only a finite ball
without both composition and missing-cylinder data would be inadequate.

## 4. LEF lamps give local models with finite lamps

**Lemma 4.1.** For a LEF group `A`, every finite partial multiplication
table in `Lambda(A) semidirect G` embeds into
`Lambda(B) semidirect G` for some finite group `B`. Both `Lambda` and `G`,
including the entire action, remain identical.

*Proof.* Fix a finite set `F` of elements of the graph wreath, containing
`1`. Choose for each `u in F` an expression

```text
u = ((a_1)_(x_1)...(a_l)_(x_l),g_u).
```

Choose the empty lamp word for `1`. Our finite collection of test words
consists of all `u v^-1` with distinct `u,v in F`, and all
`u v w^-1` for `u,v,w in F` with `uv=w`. These tests suffice for
injectivity and partial multiplicativity.

Expand each test by the semidirect product law, moving all actor factors
to the right. This produces a finite lamp word with translated vertex
labels, followed by its actor component. For each such lamp word, choose
a complete graph-product reduction. The elementary moves are:

1. interchange neighboring syllables at adjacent vertices;
2. multiply neighboring syllables at the same vertex;
3. delete identity syllables.

Every word admits such a finite reduction to a syllable-reduced word.
A syllable word with all coefficients nonidentity is reduced when two
syllables at the same vertex cannot be brought together by the allowed
interchanges. A nonempty reduced word represents a nonidentity element.
These are the standard graph-product normal-form facts.

Let `P` contain `1`, all lamp coefficients in the expressions and their
inverses, and every coefficient appearing during the chosen reductions.
For each multiplication step include both factors and their product;
enlarge `P` to include inverses as well. The set is finite. Choose a LEF
embedding `theta:P->B` into a finite group. It preserves `1`, inverses of
entries in `P`, and each of the recorded multiplication steps.

Replace every original lamp coefficient by its `theta`-image, keeping
all vertex labels and all actor components. This defines a map
`eta:F->Lambda(B) semidirect G`. On each test word, exactly the same
reduction can be performed after replacement. Interchanges depend only
on the unchanged graph; recorded products agree by partial
multiplicativity; a coefficient is identity if and only if its image is,
by injectivity of `theta`.

The final word is therefore empty if the original reduced word is empty.
If it was nonempty, it remains syllable-reduced and nonempty: reducedness
depends on the vertex sequence and which coefficients are nonidentity,
both unchanged. Thus triviality of each lamp test word is preserved in
both directions. Actor components are literally unchanged. It follows
that distinct elements of `F` have distinct images and every multiplication
relation among members of `F` is preserved. QED.

The map `theta` is not alleged to extend to a homomorphism from `A`.
Recording all intermediate coefficients is the step that makes a partial
map sufficient. The finite group `B` need not approximate or act on the
vertex set. No quotient of `G` is taken.

## 5. Proof of Theorem 1 and a strict enlargement of the lamp class

If `G` is surjunctive, Lemma 4.1 locally embeds the graph wreath into
graph wreaths over finite lamps. Section 2 makes every such model group
surjunctive, and Lemma 3.1 makes the original group surjunctive. Conversely,
`G` embeds as the actor subgroup; subgroup heredity of surjunctivity proves
the only-if direction.

The LEF extension is strictly broader than the residually finite lamp
case. For instance `Alt_fin(N)` is locally finite and hence LEF. It is an
infinite simple group and so has no nontrivial homomorphism to a finite
group: the kernel of such a map would have to be trivial or the whole
group, and an injection into a finite group is impossible. It is therefore
not residually finite. Theorem 1 still applies with this lamp. Its usual
simplicity is only an illustrative standard fact; it is not used in the
proof or the Kun--Thom specialization.

For a complete graph Theorem 1 gives all permutational wreaths with LEF
lamps, extending the original residually finite lamp statement. For an
empty graph it gives free permutational lamps. Every intermediate graph
is treated directly by the same argument.

## 6. Every Kun--Thom graph choice is nonsofic as well

Use the explicit Theorem E pair in `kun-thom-nonsofic-wreath`.
The actor is residually finite and hence surjunctive. Theorem 1 therefore
supplies the positive part for every LEF lamp and every invariant graph.

For nonsoficity, take any nonidentity `a in A` and write `a_x` for its
copy at `x`. Because the compression semigroup generates `G` and
`Gamma` is not normal, some compressor `t` satisfies
`t Gamma t^-1` properly contained in `Gamma`. Choose
`gamma in Gamma` outside `t Gamma t^-1`. Then

```text
x = t Gamma,       y = gamma t Gamma,       x != y.
```

The element `a_Gamma` commutes with `Gamma`. But, with commutator convention
`[b,c]=b c b^-1 c^-1`, its translated defect is

```text
[t a_Gamma t^-1, gamma] = a_x (a^-1)_y.
```

Retraction onto the single vertex group `A_x` maps this word to `a != 1`.
The retraction exists for every graph by Section 2, irrespective of
whether `x` and `y` are adjacent. Thus the graph wreath contains a
nontrivial rigid compression defect. The established theorem
`sofic-groups-kill-rigid-compression-defects` forbids this in a countable
sofic group containing the pair. Countability holds here when `A` is
countable. This proves nonsoficity directly, without using a quotient
preservation assertion.

If `A` is finitely generated, take finite generators for `A_Gamma` and
for `G`. Conjugating the root generators by the transitive actor gives
every vertex group, so their union generates the graph wreath. This
proves the final assertion of Theorem 2.

## 7. Scope, integration, and source audit

The new claims and routes consume the existing finitary split-extension
theorem and rigid-defect theorem. A route back to
`surjunctive-nonsofic-group-exists` uses any binary instance. The
existential root was already established in the repository; the advance
here is the whole graph-product/LEF class and its exclusion as a
Gottschalk counterexample family.

This does not cover the twisted Clifford graph groups. In those groups
deleting one endpoint of a relation `[u_x,u_y]=z` can force the global
central element `z` to vanish, so the retractions used in Section 2 do
not detect all elements. It also does not cover arbitrary internal lamp
automorphisms, arbitrary LEF-by-surjunctive extensions, or arbitrary
surjunctive lamps. The latter cannot be substituted into the finite-lamp
argument: being surjunctive supplies no finite partial group models.

External checks performed 2026-09-12:

* Green, [Graph products of groups, thesis](https://etheses.whiterose.ac.uk/id/eprint/236/)
  (1990), supplies graph-product normal forms and residual finiteness.
  A modern primary proof with stronger monoid scope is Cho--Gould--Ruskuc--Yang,
  [Graph products of residually finite monoids are residually finite](https://arxiv.org/abs/2403.13614),
  Theorem 5.1. These classical graph-product inputs are not claimed as new.
* Ceccherini-Silberstein--Coornaert,
  [Expansive actions on uniform spaces and surjunctive maps](https://irma.math.unistra.fr/~coornaer/usca.pdf),
  Corollary 1.3, attributes closedness of marked surjunctive groups to
  Gromov. Section 3 above is an explicit finite-certificate proof of that
  standard input, adapted to the local maps required here.
* Arzhantseva--Gal,
  [On approximation properties of semidirect products of groups](https://arxiv.org/html/1312.7682),
  treat finitely generated residually finite kernels. Here the kernel can
  have infinitely many lamp sites and need not be finitely generated or
  residually finite when the lamp is merely LEF.
* Needham, [Residual Finiteness of Graph Wreath Products](https://arxiv.org/html/2509.11170v1),
  Theorem 1.1, requires conditions on finite-index actor orbits to obtain
  residual finiteness of the whole graph wreath. That theorem does not
  supply the surjunctivity result above, whose action is unrestricted.
  Its induced-subgraph retractions agree with the elementary maps used here.
* Kun--Thom, [Nonsofic wreath products of residually finite groups](https://arxiv.org/abs/2608.06222),
  is the primary source for the existing rigid pair and centralizer
  obstruction. The new argument is the uniform two-site defect for every
  graph, combined with the class-level positive theorem.
* Bowen--Chapman, [Surjunctivity does not characterize cosoficity of invariant random subgroups](https://arxiv.org/abs/2511.06586),
  remains the primary problem reference for the group separation. Its
  abstract's 2025 statement that no nonsofic group is known is stale in
  light of Kun--Thom's 2026 paper and is not used as current evidence.
  The maintained Bowen research page was inspected but the fetched text
  did not contain the surjunctivity question, so no freshness claim is
  based on it. No externally verified resolution of universal Gottschalk
  was located; nothing in this artifact asserts one.

Repository lexical searches and targeted external searches for graph-wreath
surjunctivity and LEF lamps found the previous wreath/finitary/graph-fold
arguments, not the class statement proved here. The cited works contain
mathematical proofs; no computational supplement or released algorithm
was used as a novelty source. This is a bounded prior-art audit, not an
exhaustive claim of bibliographic priority. No computation or formal Lean
verification is claimed. Cairn validation is to run through the MSI
wrapper with the parent lane's integrated check.
