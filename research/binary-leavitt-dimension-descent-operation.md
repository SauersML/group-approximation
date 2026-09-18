---
rg: 2
id: binary-leavitt-dimension-descent-operation
kind: claim
title: Build the dimension-reducing repair operation for the binary Leavitt group
distinct_from:
  dimension-descent-criterion-for-non-mf: that is the proved criterion; this is the construction it consumes, and it is open.
  canonical-swap-corners-have-no-dimension-descent: that closes the route which restores the literal compressed actor, computing the padding cost; this asks for a different action on a smaller space, which that node explicitly leaves open.
  property-t-free-leavitt-full-mf-radical: that is the goal, a Kazhdan-free derivation of the collapse; this is one candidate mechanism for reaching it.
  uniform-finite-mf-obstruction: that is a compactness statement about one finite test; this asks for an explicit transformation of models.
artifacts:
  - research/artifacts/dimension-descent-criterion-2026-09-07.md
---

OPEN.  Let `H` be the binary Leavitt unit group with a finite generating
tuple, let `z` be a nontrivial involution normally generating `H` -- in
characteristic two `e_(ij)(a)^2 = 1`, so the basis transposition of
`char-two-basis-swap-normally-generates-elementary-group` serves -- and let
`R` be a finite set of relations containing `z^2`.

Construct `epsilon_0 > 0` and an operation sending every
`U in U(d)^k` with `delta(U) < epsilon_0` and `||z(U) - I|| >= 1` to some
`V in U(d')^k` with `1 <= d' < d`, `delta(V) < epsilon_0` and
`||z(V) - I|| >= 1`.

The intended shape: detect a finite matrix factor inside the model, pass to
its smaller multiplicity space, and rebuild a tuple representing the same
group there, correcting the errors against the detected factor.  The third
step carries the freedom: `V` need not consist of compressions of the entries
of `U`, and may be assembled from different words.

## Attempts

**Compression is closed.**  `canonical-swap-corners-have-no-dimension-descent`
computes the sharp cost of restoring a canonical swap corner's compressed
actor to a unitary: a dilation with `o(1)` compression error needs padding
`k_n >= (1-o(1))r_n`, so the removed dimension returns.  That kills the
version of the operation that compresses the given generators and repairs
them, and it is why the construction has to build a different action.

**The topological reading is closed twice.**
`finite-order-root-cannot-carry-a-corona-bott-class` blocks using the torsion
root as a Bott coordinate, and the four-sphere cancellation recorded in
`stw22-matrix-four-sphere-bott-cancellation-proof` is the pairing failure for
winding numbers under conjugation.  So the descent should be sought
algebraically, not through an index.

**The error budget is the binding constraint.**  By
`quadratic-descent-loss-is-admissible-linear-is-not`, dimension reduction
alone is not enough: a constant multiplicative loss cannot survive an
unbounded number of steps against dimensions that may grow arbitrarily fast.
The construction must cancel the first-order defect, so what is wanted is a
finite symmetry of the Leavitt self-similarity under which the linear term in
the rebuilt tuple's defect vanishes.

**Not yet attempted here.**  Explicit small presentations and matrix
identities for the first-order cancellation.  The existing ring identities do
not supply it.

**The hole is the goal restated (swarm-0917-w9-w9-ptl-last1, 2026-09-18).**
Recorded in `dimension-descent-operation-equals-mf-residual-membership`
(ESTABLISHED, no Kazhdan input).
- **Operation equals emptiness.** The operation exists at `(R, eps_0)` iff
  the set `Vis(R, eps_0)` of visible models is empty, that is, iff
  `eps_0 <= delta_*(R)`. By minimality of the dimension, no operation has a
  nonempty domain.
- **Emptiness equals membership.** One ultraproduct shows that some
  `(R, eps_0)` with empty `Vis` exists iff `z in Res_MF(H)`.
- **Consequence.** This node holds iff the target of
  `leavitt-full-radical-via-dimension-descent` holds, and the equivalence
  passes between Kazhdan-free proofs. The route is a restatement, not a
  decomposition.
- **Unrestricted status.** The node is true, vacuously, once any proof, with
  (T) or without, gives `z in Res_MF(H)`.
- **Class killed.** Every candidate that acts on an actual visible model at
  threshold `eps` proves `eps > delta_*(R)` and fails there. So "detect a
  finite factor and rebuild" cannot be tested numerically at any admissible
  threshold.
- **Loss accounting.** Every loss rate `f(t) < t` reduces to emptiness, so
  the quadratic-loss design target is subsumed.
- **What real progress needs.** A lower bound `delta_*(R) > 0` read off the
  relations.

**Self-similar commuting-factor splitting (swarm-0917-w9-w9-ptl-last1,
2026-09-18). Dead, by linear loss.**
- **Setup.** Use `M_2(L) = L` to embed `H x H` in `H` by
  `(a, b) -> s_1 a t_1 + s_2 b t_2`. In `U in Vis(R, eps)`, `1 x z` is an
  involution up to `O(eps)` that commutes, up to `O(eps)`, with the word
  images of `H x 1`.
- **Nonzero split.** Both spectral subspaces `V_+-` of `1 x z` are nonzero.
  If one vanished, then `U(1 x z) ~ +-I`. But `1 x z` is conjugate to
  `z x 1`, and `||U(z x 1) - I|| ~ ||z(U) - I|| >= 1`.
- **Candidate.** Compressing the words for `a_i x 1` to the larger-norm side
  gives a tuple of smaller dimension.
- **Where it dies.** The defect becomes `K delta(U)`, with `K` of the order
  of the length of the embedding words, so `K > 1`. The mark only survives
  at `>= 1 - O(eps)`, and the threshold is not preserved.
- **What it still gives.** Read through the equivalence above, a genuine
  operation that lands in a worse threshold gives only an inequality between
  the visible-dimension profiles at `eps` and `K eps`. It gives no emptiness.
