# 2026-08-24 — Gottschalk: nonlinear full-shift attack after the Leavitt audit

This note records the part of the Gottschalk attack that survives a full audit of
the Leavitt lane, together with a new finite nonlinear search.  The point is to
work in the full cellular-automaton monoid rather than mistake a proper-subshift
embedding or a quotient-ring defect for a full-shift counterexample.

## 1. Exact full-shift target: a one-sided unit in the CA monoid

Let `A` be finite.  An injective cellular automaton

    tau : A^G -> A^G

is a homeomorphism from the compact full shift onto its image.  Its inverse on
the image is continuous and equivariant, hence has finite memory.  Extend that
finite local rule arbitrarily from the patterns occurring in `tau(A^G)` to all
patterns on the same memory set.  This gives a cellular automaton

    sigma : A^G -> A^G

with

    sigma tau = id.

If `tau` is not surjective then `tau sigma != id`.  Conversely such a pair is
obviously a strict embedding.  Thus Gottschalk is exactly direct finiteness of
`CA(G,A)` for every finite alphabet `A`.

This is the nonlinear analogue of the group-ring criterion already present in
Cairn.  It is also the right form for finite SAT searches: for fixed memories,
the unknowns are just the two finite truth tables.

## 2. Correction to the Leavitt implication graph

The old sentence in `nonsurjunctive-from-stable-finiteness-failure` saying that
surjunctivity of `G` would not imply direct finiteness of `F_2[G]` was wrong.
Bradford--Fournier-Facio Corollary 3.25 gives

    Surj(G) => stable finiteness of k[G] => direct finiteness of k[G]

for every field `k`.  For the binary Leavitt unit group Cairn proves separately
that stable and direct finiteness of `F_2[G]` are equivalent.  Hence

    Surj(G) => SF(F_2[G]) <=> DF(F_2[G]),

and a scalar one-sided inverse still refutes Gottschalk by contraposition.

The converse positive implication is unavailable: direct/stable finiteness is
equivalent to the appropriate linear/additive surjunctivity statements, not to
full nonlinear finite-alphabet surjunctivity.  Thus the Kaplansky lane can
*refute* Gottschalk, but proving the Leavitt group algebra directly finite would
not prove Gottschalk.

## 3. New theorem: collision-free composition rectangles cannot compress

Let `tau,sigma : A^G -> A^G` have memories `S,T` and local rules `mu,nu`, and
assume

    sigma tau = id.

With the standard convention, `(sigma tau)(x)(1)` reads the input coordinates
`x(t s)` for `(t,s) in T x S`.  Suppose the multiplication map

    T x S -> G,   (t,s) |-> t s

is injective.

Since the composition recovers `x(1)`, there is a unique `(t0,s0)` with
`t0 s0 = 1`.  A pattern on `TS` is then an independent family of row patterns
`p_t in A^S`, and

    nu( (mu(p_t))_(t in T) ) = p_(t0)(s0)                 (1)

for every such family.  If `p(s0) != q(s0)` but `mu(p)=mu(q)`, substitute `p`
and `q` into the `t0` row of (1), keeping all other rows fixed.  The left sides
agree and the right sides differ, contradiction.  Therefore the sets

    I_a = { mu(p) : p(s0)=a }

are nonempty and pairwise disjoint as `a` runs over `A`.  There are `|A|` of
them inside a set of cardinality `|A|`; each is a singleton and together they
exhaust `A`.  Hence

    mu(p) = pi(p(s0))

for a permutation `pi` of `A`.  The encoder is only a coordinate shift followed
by a symbol permutation, so it is bijective.

**Consequence.**  Any strict full-shift embedding with a finite-memory left
inverse must exploit a genuine group multiplication collision

    t s = t' s',   (t,s) != (t',s').

This is an unconditional obstruction for arbitrary groups and arbitrary finite
alphabets.  It explains why merely putting a local rule on a free multiplication
rectangle cannot attack Gottschalk; group relations must enter the decoder
window itself.

## 4. Fixed-memory nonlinear SAT formulation

For binary alphabet, encode the truth tables of `mu : {0,1}^S -> {0,1}` and
`nu : {0,1}^T -> {0,1}` as bit tables.  Let `TS` be the set of distinct products
`t s`.  For every binary pattern `p` on `TS`, the equation `sigma tau=id` is

    nu( ( mu((p(t s))_(s in S)) )_(t in T) ) = p(1).      (2)

Likewise, with `ST` the distinct products `s t`, strictness is witnessed by a
pattern `q` satisfying

    mu( ( nu((q(s t))_(t in T)) )_(s in S) ) != q(1).     (3)

Equations (2)--(3) are a finite SAT problem.  Crucially, they depend only on the
collision partitions of the rectangles `T x S -> TS` and `S x T -> ST`, not on
the names of the group elements.  The implementation therefore canonicalizes
each multiplication rectangle and solves each collision type once.

Reproducer:

    research/artifacts/gottschalk-nonlinear-ca-search-2026-08-24.py

## 5. Exact Thompson witness used in the search

The script implements the finite prefix-table model used by Cairn's Thompson
witness and reconstructs the two standard generators.  In normalized prefix
notation it obtains

    rootRotation = {00->0, 01->10, 1->11}
    a            = {0->00, 10->01, 11->1}
    b            = {0->0, 10->100, 110->101, 111->11}.

It checks `a b != b a` and the two Thompson-F relations used by the Lean
non-LEF witness:

    [a b^-1, a^-1 b a] = 1,
    [a b^-1, a^-2 b a^2] = 1.

The search balls consist of the distinct elements represented by words in
`a,A,b,B` of length at most the stated radius.

## 6. Completed nonlinear fences

For each row below, `S` and `T` contain the identity and have the indicated
sizes.  Every pair of memories in the stated ball was canonicalized by its two
multiplication-collision tables; then every binary local rule `mu` and every
compatible binary decoder rule `nu` was exhausted.  `ok=True` means no pair
satisfies `sigma tau=id != tau sigma`.

| radius | `|S|` | `|T|` | memory pairs | collision types | result |
|---:|---:|---:|---:|---:|---|
| 2 | 2 | 2 | 256 | 3 | no strict split embedding |
| 2 | 2 | 3 | 1,920 | 15 | no strict split embedding |
| 2 | 3 | 2 | 1,920 | 15 | no strict split embedding |
| 2 | 3 | 3 | 14,400 | 171 | no strict split embedding |
| 3 | 2 | 2 | 2,704 | 3 | no strict split embedding |
| 3 | 2 | 3 | 68,952 | 15 | no strict split embedding |
| 3 | 3 | 2 | 68,952 | 15 | no strict split embedding |

The `3 x 3` radius-2 line is the strongest completed genuinely nonlinear
search here: it exhausts `14,400` memory pairs and all `256 x 256` nominal
truth-table pairs after exact decoder forcing, reduced to 171 collision types.
The `2 x 3` and `3 x 2` fences persist over the entire radius-3 word ball.

This is not a linear/group-ring search.  The local rules are arbitrary Boolean
functions, so the fence probes the full CA monoid at those memories.

## 7. A second general localization consequence

A strict embedding with encoder memory `S` can be translated/conjugated by a
coordinate shift so that one memory coordinate is the identity.  The induced
CA then acts independently on cosets of the subgroup generated by the relative
memory.  Therefore a counterexample localizes to a finitely generated
**non-surjunctive** subgroup generated by the relative encoder memory.  In
particular that subgroup is nonsofic, since every sofic group is surjunctive.

For a two-site encoder the relative memory generates a cyclic subgroup, so no
Gottschalk counterexample can have encoder memory of size at most two, over
*any* finite alphabet.  The first possible encoder size is three.

This is the nonlinear counterpart of Liu's support-subgroup localization for a
group-ring one-sided inverse, and it says where the Leavitt search should move:
the encoder memory must already generate a genuinely nonsofic local actor; a
small rule living entirely in a known surjunctive subgroup can never work.

## 8. Kun--Thom firewall

The Kun--Thom wreath products tempt a positive shortcut because they have a
locally finite lamp kernel and residually finite quotient.  Shahryari's
withdrawn arXiv note states that locally-finite-by-surjunctive semidirect
products are surjunctive, but the peer-reviewed Arzhantseva--Gal theorem in this
circle assumes a **finitely generated residually finite kernel**.  The infinite
lamp kernel is not finitely generated.  The withdrawn abstract is therefore not
being promoted to an established Cairn theorem; the root remains fenced pending
an independent proof of that extension statement.

## 9. Net mathematical output of this pass

The useful new object is not another proper-subshift embedding.  It is the
finite nonlinear direct-finiteness problem (2)--(3), plus a theorem that forces
any successful instance to contain multiplication collisions.  Together with
the Leavitt implication correction, this sharply separates three levels:

1. quotient/subshift defects, which do not decide full-shift surjunctivity;
2. group-ring one-sided inverses, which would refute Gottschalk linearly;
3. genuinely nonlinear one-sided units in `CA(G,A)`, which are the full target.

The present bounded nonlinear search finds no counterexample in the tested
Thompson windows.  A complete resolution still requires either an explicit
one-sided unit at a larger/non-Thompson Leavitt window, or a universal argument
showing that every such collision network is information-balanced.
