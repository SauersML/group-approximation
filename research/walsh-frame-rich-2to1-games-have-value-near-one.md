---
rg: 2
id: walsh-frame-rich-2to1-games-have-value-near-one
kind: claim
title: A rich 2-to-1 game whose perfect SDP solution uses Walsh frames f_u chi_c / K (the Guruswami--Khot--O'Donnell--Popat--Tulsiani--Wu vector universe) has value at least 1 - B(K), with B(512) < 0.011, so no enrichment of the GKOPTW perfect-SDP gaps is a basic-SDP gap for Rich 2-to-1 with perfect completeness
distinct_from:
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that kills NP-hardness reductions whose YES instances carry a computable tractable skeleton; this is about a fixed instance's integral value and the vectors of its perfect SDP solution. It needs no reduction and no algorithm, only the pair-sum identity, and it is silent on hardness.
  sd-rich-and-unique-games-sos-gaps-interconvert: that moves SoS gaps between unique games and admissible-design rich games at completeness 1 - eta; this shows that one explicit family of perfect basic-SDP solutions cannot coexist with richness and low value, and transfers no gap.
  dummy-padding-cannot-beat-the-random-guessing-floor: that shows decoding lists of size proportional to the alphabet only reproduce the random-assignment value 2/K; this decodes a single label per component from the SDP vectors and gets value near 1, but only for Walsh-framed perfect solutions.
  clifford-long-codes-realize-pairing-value-in-binary-noise-test: that turns SDP vectors of a rich game into entangled strategies for a noise test; this uses the SDP vectors to produce a classical labelling of the game itself, and only for Walsh frames.
artifacts:
  - experiments/rich-2to1-walsh-frames-2026-09-17/walsh_frame_enrichment_check.py
---

**ESTABLISHED.** Proof: route `walsh-frame-rich-2to1-value-proof`.

**Setting.** A 2-to-1 game `G` has left alphabet `[K]`, right alphabet `[K/2]`,
edge weights `w_e > 0` summing to 1, and 2-to-1 maps `pi_(uv) : [K] -> [K/2]`.
`val(G)` is the largest weight of edges satisfied by a labelling. The *basic
SDP* is Figure 1 of Guruswami, Khot, O'Donnell, Popat, Tulsiani and Wu, *SDP gaps
for 2-to-1 and other Label-Cover variants* (ICALP 2010), verbatim:

> "maximize E e=(u,v)∈E [ ∑ i,j∈ψe ⟨z(u,i), z(v,j)⟩ ] subject to
> ∑ i∈[R] ‖z(v,i)‖² = 1 ∀ v∈V, ⟨z(v,i), z(v,j)⟩ = 0 ∀ i≠j∈[R], v∈V"

A solution is *perfect* if its value is 1.

**Walsh frames.** Let `K = 2^k` and identify coordinates of `R^K` with
`F_2^k`. Write `chi_c(x) = (-1)^(c.x)`. A perfect SDP solution of `G` is
*Walsh-framed* if, after one common isometry, every left vertex `u` has
`f_u : F_2^k -> {+-1}` and a bijection `psi_u : [K] -> F_2^k` with

`z(u,a) = f_u chi_(psi_u(a)) / K` for all `a in [K]`.

The right vectors are not restricted. The GKOPTW 2-to-1 instance (their Section
5) is Walsh-framed: `V` is the set of classes `P_i` of `{+-1}`-functions modulo
characters, and verbatim "z(Pi,α)(x) := 1/K ([Pf]χα)(x)".

**Forcing sets.** For a perfect pairing `P` of `F_2^k`, let
`Gamma(P) = {c + c' : {c,c'} in P}`. A set `Gamma` of nonzero vectors is
*forcing* if every `H : F_2^k -> F_2` with `H(0) = 0` that is additive on
`gamma^perp` for each `gamma in Gamma` is linear. Every `Gamma` that meets every
codimension-2 subspace is forcing (Step 2 of the proof), but not conversely.

For an edge `(u,v)`, `P_(uv)` is the pairing `{psi_u(pi_(uv)^(-1)(b))}_b` of
`F_2^k`. The edge is *forcing* if `Gamma(P_(uv))` is forcing.

**Theorem.** Let `G` have a Walsh-framed perfect SDP solution.

1. **Rigidity.** `Gamma(P_(uv))` depends only on `v`. If it is forcing, then all
   neighbours of `v` have the same vector set `{z(u,a)}_a`.
2. **Value.** `val(G) >= w(forcing edges)`.
3. **Richness.** If `G` is rich (BKM Definition 5), then
   `val(G) >= 1 - q_K`. Here `q_K` is the probability that a uniformly random
   pairing of `F_2^k` has a non-forcing difference set, and
   `q_K <= B(K) := ((K-1)(K-2)/6) prod_(0 <= j < ceil(K/8)) (3K/4 - j)/(K - 1 - 2j)`.
   For `K >= 32`, `B(K) <= (K^2/6)(7/8)^(K/8)`. Numerically `B(512) < 0.0108`,
   `B(1024) < 10^(-8)`, and `B(K) -> 0` faster than any power of `K`.
4. **No Walsh-framed gap.** For every `delta < 1/128`, no rich 2-to-1 game with a
   Walsh-framed perfect SDP solution has `val(G) <= delta`. If `K <= 256`, a
   uniformly random labelling already gives `val >= 2/K >= 1/128`. If `K >= 512`,
   item 3 gives `val >= 0.989`.

**Consequences for `rich-2to1-perfect-completeness-conjecture`.**

* The GKOPTW 2-to-1 gap is far from rich. A right vertex `Q^γ_i` has labels
  "pairs of the form {α,α+γ}", so every edge pairing is the coset pairing of
  `<γ>` and `Gamma(P_(uv)) = {γ}`. At a left vertex only the `K - 1` coset
  pairings occur, out of `(K-1)!!`. GKOPTW themselves note that "our integrality
  gaps are for special cases of the Label-Cover problem where the constraints
  can be expressed as difference equations over F2-vector spaces", and that
  deciding complete satisfiability "can be easily done in polynomial time".
* No enrichment helps. Adding vertices, edges or pairings while every left
  vertex keeps a Walsh frame yields a rich game of value near 1, whatever the
  graph. So the evidence question on the conjecture has a negative answer for
  the GKOPTW vector universe. Their low value comes entirely from non-forcing
  (coset) pairings, and a rich pairing is forcing with probability
  `1 - B(K)`.
* A basic-SDP gap for Conjecture 7 must use left frames that are not
  `+-1`-twisted Walsh bases in any common coordinate system. Such frames can
  still exist, since the SDP value is invariant under independent rotations.
  The theorem does not refute the conjecture or its basic-SDP evidence in
  general.

**Kill (class of approaches).** Approach: *obtain basic-SDP evidence for Rich
2-to-1 with perfect completeness by enriching the GKOPTW instance, or by any
construction whose perfect solution lives in Walsh frames.*

* Invariant: forcing edge mass.
* Every member dies at the same step. Richness makes forcing mass
  `>= 1 - B(K)`. The pair-sum identity plus the hyperplane-character lemma then
  collapses all frames around a forcing right vertex to one vector set, and one
  chosen vector per component labels every forcing edge correctly.

**Computation.** The artifact checks the following:

* all 105 pairings of `F_2^3`, with the pair-sum identity tested by direct
  vector comparison;
* 400 random pairings of `F_2^4` against all `2^15` frames, confirming that the
  frames admitting the same pair sums are exactly the characters iff the
  difference set is forcing;
* the GF(2) forcing test against brute force for every `Gamma` in `F_2^3`;
* exact non-forcing counts: `105/105` at `K = 8` and `550305/2027025` at
  `K = 16`;
* Monte Carlo non-forcing rates of `65/20000` at `K = 32` and `0/20000` at
  `K = 64`;
* Monte Carlo non-2-hitting rates of `17405/20000` at `K = 32`, `2043/20000` at
  `K = 64` and `1/20000` at `K = 128`;
* the rigidity labelling on random Walsh-framed games that mix random pairings
  with GKOPTW-style coset pairings, including right vertices whose neighbours
  have non-character relative frames.

At small `K`, 2-hitting fails almost always (no 2-hitting pairing exists for
`K <= 16`), while forcing already holds for most pairings at `K = 16`. So the
bound `B(K)` is far from tight: empirically `q_K` is below 1% already at
`K = 32`. Only `B(K)` is established.
