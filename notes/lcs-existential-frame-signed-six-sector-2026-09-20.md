# An existential six-outcome frame candidate: exact extension and global failure

Date: 2026-09-20. Bounded symbolic attack on
`lcs-weighted-conjugacy-halting-gap-source`. No local computation, build,
remote job, commit, or canonical-node change was made. This note gives one
explicit candidate, including full commuting frame copies, and an exact
countermodel for every finite loopfree input graph. It is not a no-go for
existential quantum completeness in general.

## 1. Source and prior-work boundary

The target has efficiently sampled bounded-width involutory linear rows
and conjugacies, with finite-dimensional normalized-HS energy infimum zero
on HALT and bounded below uniformly on NONHALT. A designated representation
of an auxiliary finite group is not a condition in that syntax.

The primary [Culf--Mastel v2 paper](https://arxiv.org/pdf/2410.21223) was
checked again on this date. Definition 4.11 uses an infimum over
finite-dimensional traces; Theorem 4.14 includes succinct 3-colouring,
and Corollary 4.17 includes the assignment-with-commutation presentation.
These are perfect-value results, not a blanket assertion of exact finite
attainment. The exact YES construction below therefore does not by itself
establish the entire positive clause of that source. Its soundness failure
is already exact, making a further approximate-completeness analysis moot.

Repository checks found the existing claims
`finite-predicate-signed-permutation-sector`,
`finite-packet-central-sign-cannot-enforce-nonlinear-support`, and
`tracial-bcs-has-rational-balanced-hyperoctahedral-atlas`, with their proofs.
The finite selected-sector idea and its general central-sign obstruction
are consequently NOT new claims here. The calculation worth retaining is
the following complete global test: even full commuting edge-frame copies
and involutory transport admit an explicit perfect model on every graph.
It does not use odd tensor powers or literal controlled-Pauli ports.

## 2. Candidate: one marked signed-permutation frame

Let

    S={(a,b): a,b in {0,1,2}, a!=b},
    G=(C_2)^S semidirect Sym(S).

Thus `|G|=2^6*6!=46080`. Write `d_s` for the six diagonal sign flips,
and choose the five adjacent transpositions `t_1,...,t_5` of an ordering
of S. All eleven generators are involutions. Put

    J=product_(s in S) d_s,
    A_a=product_(b!=a) d_(a,b),
    B_b=product_(a!=b) d_(a,b).                         (1)

J is central. The natural signed-permutation representation on `C^S` is
faithful, irreducible, and has `J=-I`. In this representation

    (I-A_a)/2=projection onto first coordinate a,
    (I-B_b)/2=projection onto second coordinate b.     (2)

Their joint nonzero atoms are exactly the six allowed unequal-colour
pairs, each of rank one. This is the designated six-dimensional sector
we would like a successful construction to use.

For a finite loopfree graph with vertices i, introduce three shared
involutions `C_(i,0),C_(i,1),C_(i,2)` per incident vertex. Require each
such triple to commute and have product `-I`, placing these endpoint
requirements in each incident edge bundle. Isolated vertices impose no
target requirements and always extend independently. Use ONE global copy
of G with J marked
negative. For every oriented edge `e=(i,j)` introduce an involution W_e
and a full copy of the eleven anchor generators, denoted `g_e`. Require

    W_e g W_e=g_e                 for every anchor generator g,
    [g,h_e]=1                    for all anchor generators g,h,
    A_(e,a)=C_(i,a),
    B_(e,b)=C_(j,b).                                  (3)

Here A_e,B_e are the two-flip products (1) in the edge copy. Equivalently,
one may impose `W_e A_a W_e=C_(i,a)` and the analogous B relation.
The full copied frame, not just its diagonal selectors, commutes with the
global anchor. One may also impose that every C commutes with the global
anchor; the constructions below satisfy it. No commutation between
different edge frames is assumed when it is not forced by shared data.

This is genuinely in bounded-width linear-plus-conjugacy syntax. A
constant presentation of G uses commuting d's, permutation conjugacies
`t_r d_s t_r=d_(t_r(s))`, distant-transposition commutation, and adjacent
braid relations. A braid is two allowed conjugacies with one shared
auxiliary involution:

    t_r t_(r+1) t_r=u_r,
    t_(r+1) t_r t_(r+1)=u_r.

The marked row has width six; defining A,B uses width-three commuting
rows. Commutation is the conjugacy `g h g=h`. Equalities of involutions
are width-two rows. Thus the global packet is constant size, and each
edge adds a constant-size bundle with bounded-width rows and conjugacies.
The full copied-group relations may be included redundantly if desired.

From a succinct sampler for source edges, a fixed number of extra random
bits selects a requirement in its constant bundle; a separate constant
branch samples the global anchor packet. Names consist of a source
vertex/edge identifier and a fixed role label. Fixed padding can give
positive dyadic weights on all bundle requirements. This establishes
efficient local access to the candidate; it makes no soundness assertion.
Repeated endpoint rows can keep occurrence labels in their sampled
identifiers. No separate succinct vertex sampler is needed.

## 3. Exact existential completeness by global colour symmetrization

Suppose the source graph has an exact finite-dimensional colouring model
on K of dimension d, with vertex PVMs `p_(i,a)`. Assume the endpoint PVMs
of each edge commute, so their six allowed joint atoms form a PVM. This
is the exact assignment-with-commutation source interface.

Take the global direct sum over the six colour permutations:

    K_s=direct-sum_(sigma in S_3) K,
    p'_(i,a)=direct-sum_sigma p_(i,sigma^(-1)(a)).      (4)

Every vertex colour now has rank `2d`. For an edge `(i,j)` and any fixed
ordered unequal pair `(a,b)`, the six inverse-permuted pairs run through
all six allowed pairs exactly once. Hence

    rank(p'_(i,a) p'_(j,b))=d.                        (5)

Consequently there is a unitary identification

    U_e: C^S tensor K_e -> K_s,    dim K_e=d,

under which the six edge atoms are the coordinate projections of C^S.
This identification is chosen separately for each edge, but all vertex
operators in (4) remain globally shared.

On the common space `C^S tensor K_s` put the natural G on the first
factor and

    C_(i,a)=I_6 tensor (I-2p'_(i,a)).

Let W_e swap the first C^S factor with the C^S factor in the U_e
decomposition of K_s:

    W_e=(I_6 tensor U_e)
          (SWAP_(C^S,C^S) tensor I_(K_e))
          (I_6 tensor U_e^*).                         (6)

It is a self-adjoint involution, not an arbitrary unitary conjugator
silently treated as an involution. It sends A,B to the two desired
vertex triples. The entire conjugated G acts on K_s, so it commutes with
the global G on the first factor. This proves every requirement (3).
The exact target dimension is `36d`.

Thus the candidate has a concrete designated-sector YES extension after
symmetrization, with globally consistent source observables and full
edge-frame transport. It is not relying on a promise that the source was
already rank balanced, nor on choosing a classical colouring.

## 4. The other marked sector has all sixteen odd-pattern pairs

Take the left-regular representation of G and restrict to

    H_- = range((I-lambda(J))/2).

Its dimension is `|G|/2=23040`. On the diagonal subgroup `D=(C_2)^6`,
every character occurs with multiplicity `|G:D|=720` in the regular
representation. The J-negative corner retains exactly the characters
labelled by vectors `k in F_2^S` of odd Hamming weight, each still with
multiplicity 720.

On character k, the minus-eigenvalue bits of the A and B triples are

    r_a=sum_(b!=a) k_(a,b),
    c_b=sum_(a!=b) k_(a,b),                            (7)

with sums in F_2. The allowed pairs S are the edges of the bipartite
graph `K_(3,3)` with the three diagonal edges removed. This graph is a
connected six-cycle. Its binary incidence map has kernel exactly the
span of the all-one edge vector: zero incidence forces the two edge
values at each cycle vertex to coincide, hence all six values coincide.
Thus the map k -> (r,c) has rank five. Its image is the pairs whose two
total parities agree.

On odd k, both r and c have odd parity. There are four possible odd
patterns,

    O={100,010,001,111},

so all `4*4=16` pairs in `O x O` occur. Each has exactly two preimages,
because the all-one kernel vector has even weight and preserves parity.
Every pair therefore has multiplicity `2*720=1440` in H_-.

Choose a joint spectral identification

    H_- = C^O tensor C^O tensor R,
    dim R=1440.                                       (8)

Under it A acts by the three sign bits on the first C^O, and B by the
three sign bits on the second. The remaining anchor generators are the
actual regular-corner matrices under this identification; no claim is
made that they preserve either individual factor.

This sector has the same exact central sign as the natural sector but
a different local predicate. In particular it contains both the pattern
111 and equal one-hot endpoint patterns. The distinction is not a small
normalized-trace error.

## 5. Full involutory frame countermodel for every graph

For a graph with n vertices and m edges use

    H = H_- tensor (tensor_(i in V) C^O_i)
                tensor (tensor_(e in E) R_e),
    dim R_e=1440.                                    (9)

Its dimension is

    23040 * 4^n * 1440^m.

These spaces and matrices are specified symbolically; none was generated.
The global G acts in its J-negative regular corner on H_-. The three
C_(i,a) act by the odd-pattern sign bits on the independent C^O_i.
They commute with the entire global anchor and have product -I.

Write the three factors of H_- from (8) as registers L,R_0,T, of
dimensions 4,4,1440 respectively. For the edge e=(i,j), define W_e to
swap simultaneously

    L <-> C^O_i,
    R_0 <-> C^O_j,
    T <-> R_e.                                        (10)

Because i!=j and the three swaps have disjoint supports, W_e is an
involution. Define every copied generator by `g_e=W_e g W_e`.
The entire edge G now acts on `C^O_i tensor C^O_j tensor R_e`, disjoint
from H_-. It therefore commutes with the full global anchor, exactly as
required. Formula (8) shows that its A and B triples are exactly the
shared C_i and C_j triples. Thus ALL relations (3), including transport
of the full finite packet and all global/copied-packet commutations,
hold with zero error.

Every finite loopfree graph therefore has a perfect finite-dimensional
model of this target candidate, regardless of its quantum colourability.
In particular K4 is a counterexample; the unrestricted quantum gap for
its 3-colouring game is proved in
`research/artifacts/lcs-perfect-completeness-attack-2026-09-20.md`.
This is stronger than a failure of
one proposed decoder: the candidate has identically zero matrix-energy
infimum on all such graph inputs, under any positive requirement weights.

For the direct projection readout `q_(i,a)=(I-C_(i,a))/2`, each of the
four odd patterns has weight 1/4. Hence

    ||sum_a q_(i,a)-I||_2^2=1,
    ||q_(i,a) q_(i,b)||_2^2=1/4  for a!=b.            (11)

The edge-variable sharing is exact; the bad model is not an overlap
inconsistency that could be fixed merely by testing the same C more
often. It uses the wrong allowed joint type inside one honest global
marked representation and transports that type consistently everywhere.

The edge reservoirs in (9) are important: omitting them could leave the
conjugated full packets overlapping the global anchor's multiplicity
register. Formula (10) moves that register as well, so the full-packet
commutation checks are actually satisfied.

## 6. Exact scope of the failed sector selection

The natural representation of G is faithful. Therefore any additional
ordinary relation involving only these anchor words which holds in the
designated natural representation already holds in G itself. It also
holds in its negative regular corner. Adding more such anchor relations
cannot distinguish Sections 3 and 4. Likewise, adding further true
relations inside each transported G does not invalidate (10).

This last statement is deliberately narrower than a prohibition on
source-dependent auxiliary extensions. New relations coupling different
edge frames, or a source-specific construction that chooses a different
representation interface, are not covered. Their honest extension and
uniform energy soundness would need their own proofs. Merely requiring
the full finite frame to be copied and to commute with the global frame
has been tested here and does not provide that selection.

The candidate is therefore not a reduction from the Culf--Mastel source.
It does give exact YES models, constant-size succinct local access, and
honest involutory transports, but fails soundness at energy zero on every
loopfree graph. The calculation specializes the already recorded finite
central-sign issue to a complete globally synchronized source candidate;
it is retained as a bounded failed construction, not promoted to a new
canonical obstruction or a refutation of perfect-completeness LCS hardness.

Independent internal review checked the rank-balanced 36d extension,
the sixteen joint types and multiplicity 1440, and transport of the full
packet including its reservoir. It found no mathematical defect. Its
sampling clarification was incorporated: endpoint requirements occur in
edge bundles, and isolated vertices impose no sampled requirements.
