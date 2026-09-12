# Sofic one-relator groups from one-sided and single-block conjugators

Date: 2026-09-07. All conjugations use `x^y=y^(-1)xy`.
These are written proofs using named standard permanence theorems. They
are not Lean certificates. The universal one-relator soficity question
remains unresolved here.

## 1. Results and sources

For a word `w in F(a,b)` and nonzero integers `l,k`, set

    G(w;l,k) = <a,b | (a^l)^(a^w)=a^k>.

**Theorem A (one-sided support).** Write `a_j=b^(-j)ab^j`. If
`w=b^d V`, where `d>0` and `V` is a finite word in the `a_j` with `j>0`,
then `G(w;l,k)` is sofic.

**Theorem B (one a-block).** For every `p,q,s in Z` and every nonzero
`l,k`, the group `G(b^p a^s b^q;l,k)` is sofic.

**Corollary.** `G(b^(-1)ab^2;1,2)` is sofic.

The last presentation is asked about in the introduction of
[Berlai, A new family of sofic one-relator groups,
arXiv:2502.05064v1](https://arxiv.org/html/2502.05064v1).
That source proves two other families. The present arguments are
deductions recorded in this repository, not assertions that the source
contains these proofs. No claim of priority over all literature is made.

We use amenable-edge amalgam permanence from Theorem 1 of
[Elek--Szabo](https://arxiv.org/html/1010.3424v2), HNN permanence from
Proposition 3.2 of
[Ciobanu--Holt--Rees](https://arxiv.org/html/1212.2739v2), and the standard
sofic-kernel/amenable-quotient permanence recalled and applied there.
The companion [triangular-chain proof](triangular-bs-chain-proof-2026-09-07.md)
checks the Baumslag-Solitar blocks and proves directed-colimit permanence
directly from finite multiplication tables. Those inputs cover every
permanence step below.

## 2. An exact kernel presentation

Suppose `w=b^d V(a_j)` for some integer `d` and a finite indexed word `V`.
Then, already in the free group,

    a^w = V^(-1) a_d V.

Let `V_i` add `i` to every index in `V`, and define

    K = <a_i (i in Z) |
            (V_i^(-1) a_(i+d) V_i)^(-1) a_i^l
            (V_i^(-1) a_(i+d) V_i) = a_i^k (i in Z)>.

The map shifting each index by one preserves all defining relations and
has the inverse shift. Hence it induces an automorphism of `K`. Form the
split extension `E` of `K` by an infinite cyclic element `b` satisfying

    b^(-1) a_i b = a_(i+1).

This is a semidirect product: in the usual convention `b h b^(-1)` is the
action of the generator, that action is the inverse shift. Its kernel
under `b->1,a_i->0` is exactly `K`.

In this presentation of `E`, eliminate every `a_i` other than `a_0` using
`a_i=b^(-i)a_0b^i`. All kernel relations become conjugates of the index-zero
relation. The remaining presentation is exactly `G(w;l,k)` after naming
`a_0` as `a`. Conversely these substitutions define a homomorphism from
the displayed presentation of `E` to `G(w;l,k)`, and the assignment
`a->a_0,b->b` gives its inverse. This verifies the presentation equality
and kernel identification in both directions.

Thus `G(w;l,k)` has sofic kernel if the displayed `K` is sofic, and its
quotient is `Z`. Proving `K` sofic will therefore suffice.

## 3. Proof of Theorem A and the explicit corollary

Under Theorem A's hypotheses, `d>0` and every index of `V_i` exceeds `i`.
The conjugator `V_i^(-1) a_(i+d) V_i` meets the triangular-chain theorem
with `j_i=i+d` and `s_i=1`. Hence `K` is sofic. The extension of Section 2
has amenable quotient `Z`, so `G(w;l,k)` is sofic. This proves Theorem A.

For the requested mixed-conjugator example, direct free reduction gives

    b^(-1)ab^2 = b a_2,
    a^(b^(-1)ab^2) = a_2^(-1) a_1 a_2.

Take `d=1,V=a_2`. Explicitly, the kernel is

    <a_i (i in Z) |
       (a_(i+2)^(-1) a_(i+1) a_(i+2))^(-1)
       a_i^l
       (a_(i+2)^(-1) a_(i+1) a_(i+2)) = a_i^k>.

For any finite set of relation indices, process them in decreasing order.
The only new generator at step `i` is `a_i`; the conjugator uses later
generators and has infinite order because it is conjugate to `a_(i+1)`.
Thus this instance uses precisely the cyclic-amalgam induction already
proved. Taking `l=1,k=2` proves the corollary.

## 4. Three ways to attach one generator

We need a slightly more flexible construction for Theorem B. Let `H` be
a sofic group containing the old elements described below, each of infinite
order. Assume `l,k,s` are nonzero. Consider the single relation

    (z^(-s) y z^s)^(-1) x^l (z^(-s) y z^s) = x^k.       (R)

Exactly one of `x,y,z` will be a new generator. There is no assertion that
the two old elements generate a free subgroup.

### 4.1. New x

The old element `c=z^(-s) y z^s` has infinite order. Form
`H *_(c=t) BS(l,k)`, using `BS(l,k)=<x,t | t^(-1)x^l t=x^k>`.
Both edge maps are injective. Both factors embed, the amalgam is sofic,
and the new `x` has infinite order. Eliminating `t=c` gives exactly `(R)`.

### 4.2. New y

Set `v=z^s x z^(-s)` in `H`, an infinite-order conjugate of `x`.
Conjugating `(R)` by `z^s` gives the equivalent relation

    y^(-1) v^l y = v^k.

Adjoin `y` as an HNN stable letter identifying `<v^l>` with `<v^k>` by
`v^(ln)->v^(kn)`. The nonzero exponents make both maps injective.
The associated subgroups are cyclic, hence amenable, so the extension
is sofic and embeds `H`. Its stable letter `y` has infinite order, as
shown by the homomorphism sending `H` to zero and `y` to one in `Z`.
Conjugating back gives exactly `(R)`.

### 4.3. New z

First form

    J = H *_(x=X) <X,t | t^(-1)X^l t=X^k>.

The element `x` in `H` and the base generator `X` of the Baumslag-Solitar
block have infinite order. Therefore the edge maps are injective; `J`
is sofic and embeds both factors. In particular `y` and `t` have infinite
order in `J`.

Next adjoin a stable letter `h` with `h^(-1)y h=t`. This is an HNN
extension of `J` along the infinite cyclic subgroups `<y>` and `<t>`.
It is sofic, embeds `J`, and its stable letter `h` has infinite order.

Finally form the amalgam with an infinite cyclic group `<z>`, identifying
`h` with `z^s`. Both edge maps are injective, including when `s<0`.
The final group is sofic and embeds the preceding group and `<z>`.
Thus the old generators and the new `z` all retain infinite order.

After eliminating `X`, the new relations are exactly

    t^(-1)x^l t=x^k,       h^(-1)y h=t,       h=z^s.

Eliminating `h` and `t` produces exactly `(R)`. This last elimination is
essential: the construction proves equality with the desired presented
group, not merely a homomorphism to a sofic overgroup.

## 5. Distinct indices in Theorem B

Put `d=p+q`. Free reduction gives

    w=b^p a^s b^q = b^d a_q^s,
    a^w = a_q^(-s) a_d a_q^s.

The kernel of Section 2 therefore has one relation `(R_i)` of form `(R)`
for each integer `i`, with

    x=a_i,       y=a_(i+d),       z=a_(i+q).

Assume first that `0,d,q` are pairwise distinct and `s!=0`. Set
`m=min(0,d,q)`. Every relator has a unique least-index generator `a_(i+m)`.
The other two generator indices are strictly larger.

Fix a finite set `D` of relation indices. Begin with the free group on
all generator names except `{a_(i+m): i in D}`. Process `D` in decreasing
order of `i`. At step `i` the least-index generator is new; both other
names have already been adjoined or belonged to the initial free group.
Maintain the invariant that the current group is sofic, has exactly the
relations processed so far, and every named generator has infinite order.

If `m=0`, apply Section 4.1; if `m=d`, apply Section 4.2; if `m=q`, apply
Section 4.3. Each construction preserves that invariant. This proves that
every finite-relator truncation on the full generator set is sofic.

Their directed colimit is the kernel `K`. The finite-table limit proof in
the companion artifact applies without requiring the transition maps to
be injective. Hence `K` is sofic, and extension by `Z` proves Theorem B
in the distinct-index case.

## 6. All degenerate cases

### 6.1. Pure b-powers

If `w=b^d` with `d!=0`, the kernel relators are

    a_(i+d)^(-1) a_i^l a_(i+d)=a_i^k.

For `d>0` the triangular theorem applies. For `d<0`, replace `b` by
`b^(-1)` and apply the positive case. This proves `G(b^d;l,k)` sofic.

If `w` is any power of `a`, including the empty word, then `a^w=a` and
the relation reduces to `a^(l-k)=1`. The group is the free product of
`Z` with a cyclic group (infinite cyclic if `l=k`), so is sofic.

### 6.2. Vanishing block or end exponent

If `s=0`, use Section 6.1 with `d=p+q`.
If `p=0`, then `w=a^s b^q` and `a^w=a_q`, so use the same section.
If `q=0`, then `a^w=a^(-s)a_p a^s`. Conjugating the defining relator
by `a^s`, which commutes with both `a^l` and `a^k`, reduces it to the
pure-power case `w=b^p`.

### 6.3. d=0 with q and s nonzero

The only remaining index collision is `p+q=0`, with `q,s!=0`. We first
construct the block

    D_s = <x,z | (z^(-s)x z^s)^(-1) x^l (z^(-s)x z^s)=x^k>.

Start from `BS(l,k)=<x,t | t^(-1)x^l t=x^k>`. Adjoin an HNN letter `h`
with `h^(-1)x h=t`, and then adjoin an `s`-th root `z` of `h` by a
cyclic amalgam. All the edge maps are injective because `x,t,h` have
infinite order and `s!=0`. Soficity follows at every step. Eliminating
`h,t` gives exactly `D_s`, and both `x,z` have infinite order.

The kernel in this collision case has one `D_s` relation on each pair
`(a_i,a_(i+q))`. In a finite truncation, process the least-index
generators in decreasing order. Attach a copy of `D_s` along the old
generator: along its `z` if `q>0`, or along its `x` if `q<0`. The shared
subgroup is infinite cyclic, both factors embed, and the new generator
has infinite order. This again proves the finite truncations sofic.
The limit and cyclic extension arguments finish this case.

The cases in Sections 5 and 6 exhaust all integers `p,q,s`. This
completes Theorem B. QED.

## 7. What this changes, and what remains

The construction proves a positive family beyond the rank-one Magnus
overlap case. For `w=b^(-1)ab^2`, the ordinary three-generator window has
a rank-two free overlap, but its alternative construction above uses
only cyclic edges. Rank at least two is therefore an obstruction to the
generic permanence shortcut, not a reason to leave every such example open.

For a general word `w` containing several `a`-blocks, the least indexed
letter may occur in several different places of the conjugating word.
It then need not fit any of the three single-new-generator constructions
in Section 4. For a general one-relator presentation, even the nested
Baumslag shape need not occur. No argument here supplies either missing
reduction. The claims `one-relator-groups-sofic`,
`magnus-staggered-chain-sofic`, and `linton-shell-sofic` remain open.

## 8. Reproducible checks

Run from the repository root:

    python3 experiments/one_relator_cyclic_peeling_check.py --json
    bin/cairn check --changed

The deterministic [replay report](one-relator-cyclic-peeling-replay-2026-09-07.json)
records 3,920 single-block parameter choices, 11,760 shifted Schreier
identities, 1,800 one-sided word identities, 64 sets of attachment and
auxiliary-generator elimination identities, and 360 finite dependency
schedules. All seven cases of Theorem B are exercised. Five negative
controls reject nonkernel words and unsupported one-sided hypotheses.

The word checks independently compare a left-to-right exponent-height scan
against the displayed kernel formulas, and decode the scanned words back
to the original free-group words. They establish exact finite identities
and scheduling conditions. Infinite-order preservation, the exact kernel
identification, the limit argument, and sofic permanence are justified by
the written mathematical proof, not by these computations. Cairn verifies
the research graph's consistency; it is not a proof assistant.
