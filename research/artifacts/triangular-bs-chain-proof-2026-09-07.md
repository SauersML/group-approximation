# A cyclic-amalgam construction for triangular Baumslag-Solitar chains

Date: 2026-09-07. This is a written mathematical proof, not a Lean
certificate. It establishes a restricted class of groups, not the assertion
that all one-relator groups are sofic.

## 1. Statement

Let `I` be any subset of `Z`. For each `i in I`, take integers
`l_i,k_i,s_i != 0`, an integer `j_i>i`, and a finite word `U_i` in the
letters `x_j^(+/-1)` with `j>i`. Write

    c_i = U_i^(-1) x_(j_i)^(s_i) U_i,
    R_i = c_i^(-1) x_i^(l_i) c_i x_i^(-k_i).

**Theorem.** The group `P=<x_i (i in Z) | R_i (i in I)>` is sofic.

Strict order of the indices is a substantive hypothesis. There is no
claim here that an arbitrary staggered relator has this form.

## 2. Standard inputs

We use the normal-form theorems for amalgamated free products and HNN
extensions. In particular, their specified vertex groups embed when both
edge maps are injective.

We also use the following established sofic permanence results: free groups
are sofic; amalgams of sofic groups over amenable subgroups are sofic; HNN
extensions of sofic groups along amenable associated subgroups are sofic;
and extensions with sofic kernel and amenable quotient are sofic.

The amalgam result is Theorem 1 of Elek--Szabo,
[Sofic representations of amenable groups](https://arxiv.org/html/1010.3424v2).
The HNN version is Proposition 3.2 of Ciobanu--Holt--Rees,
[Sofic groups: graph products and graphs of groups](https://arxiv.org/html/1212.2739v2).
These are inputs, not new results of this note.

For completeness, all parameters needed for a Baumslag-Solitar block are
checked here. The group

    BS(l,k) = <z,t | t^(-1) z^l t = z^k>,       l k != 0,

is an HNN extension of the infinite cyclic group `<z>`, identifying
`<z^l>` with `<z^k>` by `z^(ln) -> z^(kn)`. These maps are injective
because `l,k` are nonzero. Thus `z` has infinite order. The homomorphism
`z->0, t->1` to `Z` shows that `t` also has infinite order. The base is
amenable, hence sofic, and both associated subgroups are cyclic, hence
amenable. Therefore the HNN permanence theorem makes `BS(l,k)` sofic for
all the signs and magnitudes of `l,k` used here.

## 3. Every finite truncation is sofic

For a finite set `D subset I`, retain the full generator set and impose
only its relations:

    P_D = <x_i (i in Z) | R_i (i in D)>.

List `D` in strictly decreasing order. Begin with the free group on
`{x_i : i notin D}`. This group is sofic, and every named generator has
infinite order. The empty-set case already proves the assertion for
`D=empty`.

Inductively let `H` be the group built before processing an index `i`.
Maintain these two assertions:

1. `H` has exactly the relations already processed and exactly the
   generators outside `D` together with the generators already adjoined.
2. `H` is sofic and each of its named generators has infinite order.

Since all indices occurring in `c_i` exceed `i`, their generators already
belong to `H`. In `H`, the element `c_i` is conjugate to the nonzero power
`x_(j_i)^(s_i)`. Hence it has infinite order. This argument does not
require the letters of `U_i` to generate a free subgroup, or `U_i` itself
to represent a nontrivial element.

Form the amalgam

    H *_(Z) BS(l_i,k_i),

where the edge generator maps to `c_i` in `H` and to `t` in the
Baumslag-Solitar block. Both edge maps are injective by the infinite-order
checks. The normal-form theorem embeds both factors. Consequently every
old named generator stays infinite, as does the block's generator `z`.
The amalgam is sofic because its factors are sofic and its edge is cyclic.

Its presentation is the presentation of `H`, with new generators `z,t`
and relations

    t^(-1) z^(l_i) t = z^(k_i),       t = c_i.

Eliminating `t` and renaming `z` to `x_i` introduces exactly `R_i`.
Thus both inductive assertions hold at the next step. After the finite
list has been processed, the resulting group is precisely `P_D`.

## 4. The infinite presentation and the limit step

For finite `D subset E subset I`, the identity on generator names defines
a homomorphism `P_D -> P_E`. These maps may be quotient maps; we make no
claim that they are injective. The directed colimit is `P`: every listed
relation holds eventually, and every relation that follows from the full
presentation uses finitely many of its defining relators.

Here is a direct proof that a directed colimit of sofic groups is sofic,
so no unproved embedding of finite windows is hidden in this step.

Use the finite-table definition: given a finite set `F` containing the
identity and `epsilon>0`, one needs permutations for its elements that are
approximately multiplicative whenever `x,y,xy` all lie in `F`, and have
normalized Hamming distance greater than `1-epsilon` for distinct elements.

Let `L` be a directed colimit of sofic groups. Lift the finitely many
elements of `F subset L` to a common stage, choosing the identity lift to
be the identity. Distinct elements of `F` have distinct lifts at this and
every later stage: an equality at a stage would imply equality in `L`.
For each of the finitely many multiplication triples `xy=z` in `F`, the
equality of the chosen lifts holds at some later stage by the definition
of a directed colimit. Choose one stage beyond all those stages. The
lifts there reproduce every multiplication triple in `F` exactly and
remain distinct. A sofic approximation for this finite set of lifts,
with tolerance `epsilon`, therefore supplies the required permutations
for `F`. This proves the permanence statement.

Applying it to `P=colim_D P_D` completes the theorem. QED.

## 5. Scope and the next application

In a generic Magnus chain, adjacent one-relator windows overlap in a
nonamenable free group. This proof changes the construction for the
specific triangular presentations above: it adjoins a single earlier
generator by an infinite cyclic edge. It does not replace a free edge by
a cyclic edge without proving equality of presentations.

An application is the shift-invariant kernel of

    <a,b | (a^l)^(a^w) = a^k>,       x^y = y^(-1)xy,

when `w=b^d V(a_1,...,a_M)`, `a_j=b^(-j)ab^j`, `d>0`, and `V` uses only
strictly positive indices. In particular, the identity
`b^(-1)ab^2 = b a_2` points to the mixed-conjugator example asked about in
Berlai's introduction. The exact kernel identification, this application,
and an extension to every single-block conjugator are proved in the
[companion artifact](mixed-conjugator-one-relator-proof-2026-09-07.md).
