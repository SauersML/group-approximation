---
rg: 2
id: digit-group-cores-need-m-adic-coherence
kind: claim
title: The stable-letter core of the k-letter digit group BS_k(1,m) must carry one m-adic position coherently across k branches; the anchored core SFT fails (RS2) for k >= 2, and edge-pinned gluing cannot supply the coherence, because a relative seed of Z has finite boundary while matching at an index-m core edge forces at least m^n boundary points
distinct_from:
  digit-group-stable-letters-carry-an-anchored-core-seed: that claimed (RS1) and (RS2) for the anchored core SFT; this refutes its (RS2) for k >= 2 and explains why.
  edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy: that is the sufficient gluing criterion (DM), (EX), (M); this shows the criterion cannot hold at the core edges of the stable-letter subgroup of BS_k(1,m), for any choice of vertex seed.
---

**Status.** Inputs: `digit-group-stable-letters-carry-an-anchored-core-seed`,
`edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy`, `baumslag-gersten-groups-lie-in-class-c`.
- §§1–2 are **ESTABLISHED** (lane proof, bh-invent-14, 2026-09-19; elementary; not reviewed).
- §3 is a precise reduction, and §4 an open question.

**Notation.**
- `Z_J = BS_k(1,m) = ⟨x, a_1, …, a_k | a_i^{-1} x a_i = x^m⟩`, with `m ≥ 2` and `k ≥ 2`.
- `F(a)` is the free subgroup on the `a_i`, and `T` is the Bass–Serre tree over `⟨x⟩`.
- **Positions.** For a translate `x^r·y_*` of the anchored core seed, with core vertex `v` read at an
  element `h`, the *position* is an `m`-adic integer.
  - Moving up (`h ↦ h a_i`) multiplies the position by `m`.
  - Moving down to a core child drops the lowest digit.
  - The *phase* `φ(h)` is the lowest digit, which says which of the `m` down edges in each direction
    is core.

## 1. The anchored core SFT is not the orbit closure of its seed (`k ≥ 2`)

Take the SFT `Y_F` of `digit-group-stable-letters-carry-an-anchored-core-seed`, with rules (T), (E),
(K), (Ph), (A) and (Sg).
- Let `z = lim x^{r_n}·y_*` be an anchorless point (a limit with `r_n → ∞`, all signs `+`), and let
  `u` be a core vertex of `z`.
- Let `c_1, c_2` be two of its core children, in directions `1` and `2`. Removing `u` splits the core
  (a copy of `Cay(F_k)`) into components, and `K_1 ∋ c_1` and `K_2 ∋ c_2` are two of them.

**Construction.** Keep `z` outside `K_1`. On `K_1`, replace every position by the one obtained from a
new position `ρ'` of `c_1`, where `ρ'` has the same lowest digit as `c_1`'s position but a different
second digit. Keep the signs, and point the non-core cells hanging off `K_1` toward it.

**Every rule still holds.**
- Rules that involve `u` see only the coset `c_1` and its phase: (K) and (Ph)'s index at `u`, and
  sibling equality at `u`. Both are unchanged.
- Every other rule involves vertices of `K_1` only, or of the complement only. `K_1` is a subtree
  with positions propagated consistently from `c_1`, and it meets the rest of the core only through
  the edge `u c_1`.
- (A) is vacuous, since `z` has no anchor. (Sg) holds with the constant sign.

**It is not in the orbit closure.**
- In every translate `g·y_*`, the phases of `c_1`'s children equal those of `c_2`'s children, because
  both are the second digit of one position.
- This is an equality between two letters at group distance at most 4. So it is a closed condition,
  and it holds on the orbit closure.
- The new point violates it. ∎

**Why no local rule repairs this with the same alphabet.**
- The depth-`n` cousins `e a_1^{-1} a_1^{-(n-1)}` and `e a_2^{-1} a_1^{-(n-1)}` are at group distance
  `≥ 2n`. The retraction `Z_J → F_k` killing `x` is 1-Lipschitz, so the distance between the cosets
  is `≥ 2n − 1`.
- They are joined in the core only through `u`. The phases on `u`'s own line are only the residues
  `ρ − r mod m`, so the line carries no higher digit.
- So agreement of depth-`n` cousins is a condition of radius `≥ 2n` that no bounded rule on the core
  implies.
- This is an obstruction for this design, not for all designs. See §4.

## 2. Lemma: relative seeds of `Z` have finite boundary

Let `Y_p ⊆ Σ^Z` be a `Z`-SFT with an isolated point `y_p` whose orbit is dense (RS1, RS2 for `(Z, 1)`).
Then `y_p` is eventually periodic in both directions, and `∂Y_p = Y_p ∖ Z·y_p` is **finite**: it
consists of the two periodic tail orbits.

*Proof.* Let the SFT have memory `M`, and let `{y_p}` be the cylinder of a window `W`.
- If two positions `p < q` to the right of `W` carry the same `M`-block, splice: `y'` equals `y_p`
  left of `p`, and `y'(n) = y_p(n + q − p)` for `n ≥ p`. Then `y'` lies in the SFT and agrees with
  `y_p` on `W`, so `y' = y_p`.
- By pigeonhole some such pair exists with `q − p ≤ |Σ|^M`, so the right tail is periodic. The same
  holds on the left.
- Limits of translates of an eventually periodic sequence are its two periodic tails. ∎

## 3. Edge-pinned gluing cannot produce `(Z_J, F(a))`

**(a) HNN splitting over `⟨x⟩`.**
- `F(a)` acts simply transitively on its core vertices. So there is one vertex class, with vertex
  piece `(⟨x⟩, 1)` and seed `(Y_p, y_p)`.
- Each core edge in direction `i` has two data:
  - the child's up edge, where the edge group is all of `⟨x⟩`, so `O = Y_p`;
  - the parent's down edge, where the edge group is `⟨x^m⟩`, of index `m`, and `O' = cl(⟨x^m⟩·x^j·y_p)`.

**Claim.** (DM) and (M) of `edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy` cannot both
hold at such an edge.

*Proof.*
- (M) gives a homeomorphism `Ψ : Y_p → O'` with `Ψ(x·y) = x^m·Ψ(y)` and `Ψ(x^s y_p) = x^{ms+j}y_p`.
  (DM) says `O'` is clopen.
- So `Ψ^n(Y_p)` is clopen for every `n`, and its orbit trace is one residue class mod `m^n`.
- Its `m^n` translates `x^t Ψ^n(Y_p)` are clopen, pairwise disjoint (they are disjoint on the dense
  orbit), and cover `Y_p`.
- Each is infinite, hence contains an accumulation point. That point is not an orbit point, since
  orbit points are isolated. So `|∂Y_p| ≥ m^n` for every `n`, contradicting §2. ∎

**(b) Amalgam splitting `Z_J = BS_1 *_{⟨x⟩} ⋯ *_{⟨x⟩} BS_k`,** with `BS_i = ⟨x, a_i⟩ ≅ BS(1,m)`.
- The core of `F(a) = ∗⟨a_i⟩` is a star: a centre `⟨x⟩`-vertex with trivial piece `(Z, 1)`, and `k`
  leaves with pieces `(BS_i, ⟨a_i⟩)`.
- At the centre, the edge group `⟨x⟩` has index 1, so `O_centre = Y_c` has finite boundary by §2.
- So (M) forces each leaf seed to induce a compactification `cl(⟨x⟩·y_i)` of `⟨x⟩` with **finite**
  boundary.
- bh-invent-10's line-sink seed (`baumslag-gersten-groups-lie-in-class-c`) does not. Its induced
  boundary consists of the signed lines through the base vertex, `Z_m × {±}`, since the down-end of
  the axis is free.

**(c) What is being asked.** Both splittings say the same thing:
- the core must carry one `m`-adic position coherently across `k` branches;
- every branch meets the others only through a cyclic line;
- and relative seeds of `Z` cannot transmit an `m`-adic parameter.

## 4. Open: forgetting the down-end

**Question (Q_forget).** Does `(BS(1,m), ⟨a⟩)` have a rigid relative seed whose induced
compactification of `⟨x⟩` has finite boundary, that is, one that forgets the axis's down-end far
from the seeds?
- **If yes,** (DM) and (EX) are then finite checks, and by §3(b) edge-pinned gluing gives
  `(Z_J, F(a)) ∈ 𝓡`. Through the automorphism `a_i ↦ a_i x^{-i}` it also gives `(Z_J, Σ)`, and so the
  `J`-pairs of `kurosh-relative-seeds-and-the-b1-digit-splitting`.
- **If no for every seed design,** then `(Z_J, F(a)) ∉ 𝓡` should follow by a hybrid argument, since
  translates with positions agreeing mod `m^N` agree near the cut vertex. The Higman–Clapham tower
  would then have to avoid free digit letters over a distorted cyclic group. This matters because
  `(R1)` needs the digit letters free.

**On the requested RS3 step.** For the anchored core SFT it is moot, since (RS2) fails. One reusable
piece did come out.
- **One-sided trace suffices for neighbours.** If `Γ ∈ 𝒜_v ∩ 𝒜_w` and `𝒜_w Γ ⊆ 𝒜_v`, then `𝒜_v` and
  `𝒜_w` commute.
  - Decompose `X ∈ 𝒜_v` as `XB + XΓ + XC`.
  - `XΓ` commutes because `ZΓ ∈ 𝒜_v`.
  - The pointer pieces commute by atoms and domination.
- **Where it holds here.** The digit core has the down-direction trace (a parent's letters restricted
  to the core edge are functions of the child's), but not the up-direction trace. This is the
  operator form of §1: the missing information is exactly the deeper digits.

## Lesson for general BH

**A machine's counter is not tree data when it branches.**
- One digit letter (`BS(1,m)`) is seedable: its core is a line, and its `m`-adic down-end is a free
  boundary parameter.
- With `k ≥ 2` free digit letters, the core branches, and all branches must agree on one `m`-adic
  position.
- The only channel between branches is a cyclic line. Relative seeds of `Z` are eventually periodic,
  so their boundary is finite, and they cannot carry an `m`-adic parameter.
- So the digit group of the Higman tower meets a coherence wall before the halting pair: counting
  in base `m` along a free monoid of digits needs a non-local, odometer-like consistency.
- Either a seed must *forget* the down-end (Q_forget), or the tower's digits must be routed through a
  vertex group richer than `Z`.
