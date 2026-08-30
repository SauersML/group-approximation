---
rg: 2
id: r5-subquadratic-carmichael-energy
kind: claim
title: Bleak--Quick models carry common-pivot packets of subquadratic Carmichael energy
refuted_by: scalar-phase-refutes-r5-subquadratic-energy
artifacts:
  - research/artifacts/thompson-subquadratic-carmichael-energy-2026-08-24.md
distinct_from:
  thompson-v-r5-coherent-carmichael-family: that demands a uniform per-edge bound `C def_R(U)` on every Carmichael relator of the packet; this demands nothing per edge and instead demands that the total squared edge energy be sublinear in the number of edges, a genuinely different requirement in both directions by `carmichael-energy-uniform-criteria-incomparable`.
  thompson-v-r5-coherent-alternating-packet: that asks for an approximate multiplication table for a whole leaf symmetric group together with a Gowers--Hatami exactification; this asks only for an aggregate `ell^2` estimate on the Carmichael edges of a common-pivot star, with no table and no exactification.
  thompson-v-r5-uniform-common-pivot-centralizers: that is the refuted bounded-area centralizer statement; this charges no filling area at all, which is why the twisted-Schreier area obstruction does not reach it.
  carmichael-edge-hodge-operator-has-root-m-norm: that is the stronger square-function bound `E_M <= C M def_R(U)^2` proposed as the route into this claim; this is the weakest aggregate hypothesis the collapse theorem consumes.
---

Fix the Bleak--Quick prefix-transposition presentation `V=<X|R>` with relation
families R1--R5 and the marked three-cycle `b=(01 10 11)`.  Prove the
following.

There is `delta_0>0` such that for every `d` and every tuple `U in U(d)^X`
with `def_R(U)<=delta_0`, writing `B=U(b)`, there are an unbounded set of
integers `M` and, for each of them, words `g_1,...,g_M` in `X` such that the
packet

```text
X_i = U(g_i)^* B U(g_i)
```

satisfies

```text
E_M = sum_(i<j) ||(X_iX_j)^2-I||_2^2 = o_U(M^2).              (ACE)
```

The implied constant may depend arbitrarily on `U`, hence on `d` and on
`def_R(U)`.  Only one unbounded subsequence of `M` is needed, the packets for
different `M` need not be nested, and the conjugating words may have
unbounded length.

Together with `subquadratic-carmichael-energy-collapse` and the bounded area
of the relator `b^3`, `(ACE)` forces `||U(b)-I||_2 <= C_b def_R(U)` in every
model, which is `thompson-v-one-word-strict-hs-ceiling` and hence
non-hyperlinearity of `V`.  That is the content of
`thompson-v-one-word-ceiling-from-subquadratic-energy`.

The exact group geometry is available and unchanged from
`thompson-v-r5-coherent-carmichael-family`: choose a finite maximal prefix code
`P={p_1,...,p_(M+2)}`, put `x_i=(p_i p_(M+1) p_(M+2))`, and these obey the
Carmichael relations of

```text
A_(M+2)=<x_1,...,x_M | x_i^3=(x_ix_j)^2=1, i!=j>
```

exactly in `V`, each `x_i` being a `V`-conjugate of `b`.  What must be proved
is only that the **aggregate** normalized-HS residual of those relations, over
a whole packet realized by global words in one fixed model, is sublinear in
the edge count.

## Attempts

- **Decisive scalar-phase countermodel.**
  `scalar-phase-refutes-r5-subquadratic-energy` assigns the literal generator
  `b` a scalar `z=e^(it)` and every other Bleak--Quick generator the identity.
  The finite presentation defect is `O(t)`, but every word conjugate of
  `B=zI` is still `B`.  Therefore
  `E_M=binom(M,2)|z^4-1|^2`, which is not `o(M^2)` for any small fixed
  `t` with `z^4!=1`.  This refutes `(ACE)` as stated; no choice of long or
  model-dependent conjugating words can evade centrality.

- **The hypothesis is stronger than the endpoint it feeds, not weaker.**
  `(ACE)` implies `thompson-v-one-word-strict-hs-ceiling` `(TV2)`, but `(TV2)`
  does not visibly imply `(ACE)`: `(TV2)` gives only `||B-I||_2<=C delta`, and
  the constant packet `X_i=B` then has `E_M <= 8C^2 delta^2 M^2`, which is
  `O(M^2)` and not `o(M^2)`.  So this is a real reduction rather than a
  restatement — it names an object `(TV2)` never mentions — but it is not the
  easier statement the source note took it for.  Anyone working it should know
  that `(ACE)` demands genuine cancellation at a **fixed** model with a
  **fixed positive** defect, not merely at small defect.
- **The fixed dimension is the whole difficulty.**  In a finite affine
  subgroup of the model of
  `affine-clone-model-defeats-pure-thompson-prefix-error-spreading` the
  Carmichael star of size `M` is realized exactly, so `E_M=0` — but only in a
  regular representation whose dimension grows with `M`.  `(ACE)` fixes `d`
  first.  The theorem is consistent with this precisely because the covering
  number `N(d,B,r)` is allowed to be enormous; what it forbids is unbounded
  low-energy packets inside one `U(d)`.
- **The area obstructions do not reach it.**
  `finite-mark-centralizer-commutator-area-is-proper` and its averaged form
  `(FMC3)` prove that individual and mean van Kampen **areas** of the endpoint
  corrections diverge.  `(ACE)` charges no area: a long filling still admits a
  small normalized-HS residual, and the bound `||q(U)-I||_2 <= Area * delta`
  is only an upper bound.  Likewise
  `literal-one-cell-carmichael-cliques-are-uniformly-finite` obstructs a fixed
  finite template list of edge words, and `(ACE)` assigns no edge word
  template at all.  This is the one respect in which the new criterion is
  genuinely freer than the uniform one.
- **Free gauge cancellation still gives nothing.**
  `collective-centralizer-cycles-are-free-gauge-identities` shows that the
  cycle-space component of the edge-error field telescopes to the empty word,
  so any collective argument that only multiplies corrections around cycles
  proves `0=0`.  A proof of `(ACE)` must retain a positive quantity, which is
  exactly what a sum of squared edge defects is.  This is the reason the
  energy formulation is the right collective target and the scalar cycle
  product is not.
- **Orthogonal channels are not enough either.**
  `orthogonal-centralizer-channels-retain-area-properness` shows that placing
  the endpoint-correction loops in a fixed finite number of orthogonal
  channels preserves the twisted-Schreier area lower bound.  It does not
  obstruct an `ell^2` estimate on the **combined** Carmichael edge errors,
  which is what `carmichael-edge-hodge-operator-has-root-m-norm` proposes.
  The distinction is that the square-function target never fills the
  individual centralizer commutators.
- **The proposed route.**  Prove the stronger bound
  `E_M <= C M def_R(U)^2` via a Hodge-type splitting of the edge-error field;
  `M = o(M^2)` then gives `(ACE)`.  That is
  `carmichael-edge-hodge-operator-has-root-m-norm`.  The open ingredient there
  is control of the common mode, which the cycle identities cannot supply.
- **Deferred alternatives.**  A direct construction of low-energy packets from
  the R1 local `S_4` chart, and an averaged synchronization inequality over
  the Johnson graph `J(N,2)` of `thompson-v-r5-coherent-alternating-packet`,
  are both untried against the energy formulation.  Neither is blocked by any
  recorded obstruction; both were designed against the uniform formulation and
  would have to be re-derived.
