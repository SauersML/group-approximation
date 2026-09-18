---
rg: 2
id: fp-v-times-subshift-full-groups-force-quantum-rigidity
kind: claim
title: If the full group of V times a free subshift groupoid is finitely presented, the subshift is of finite type and quantum rigid over every field
distinct_from:
  fp-v-times-subshift-full-groups-force-connected-differences: that kills only two-dimensional basis-switch families, stated as coarse connectivity of difference sets; this kills every operator family of every dimension, and recovers that part 1 as the wall case.
  zd-derived-full-group-fp-forces-quantum-rigidity: that is the Z^2 case without the V factor, through a 17-term ideal certificate valid outside characteristics 3 and 5; this multiplies by V, works over every finitely generated acting group and every field, and needs one commutator.
  sft-crossed-product-fp-iff-quantum-rigid: that equates finite presentation of the Z^2 crossed-product algebra with quantum rigidity; this derives quantum rigidity from finite presentation of the V-times-shift full group.
  fp-alternating-full-groups-of-free-subshifts-force-sft: that forces finite type from finite presentation of the full group without V; part 2 here is the same conclusion for the full group with the V factor.
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that asserts finite presentation for minimal free SFTs; this is a necessary condition for it, which makes it imply quantum rigidity of every such SFT.
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `Λ` is a group with finite symmetric generating set `S`, word length `|.|` and balls `B_D`.
- `A` is a finite alphabet, and `X ⊆ A^Λ` is a subshift on which `Λ` acts freely, with
  `(g.x)(h) = x(g^(-1) h)`.
- `G_V` is the groupoid of germs of Thompson's `V` on `C = {0,1}^N`, and `T = G_V × (Λ ⋉ X)`.
- `t_s ∈ F(T)` is the translation by `s ∈ S`. `e_a ∈ F(T)` applies the 3-cycle
  `h : 00w -> 01w -> 1w -> 00w` to the `C` coordinate when `x(1) = a`, and is the identity otherwise.

**Quantum rigidity over `Λ`.** A *`D`-quantum family* on a vector space `W_0` over a field `k` is a
family of idempotents `E_a(q) ∈ End_k(W_0)`, one for each `a ∈ A` and `q ∈ Λ`, with three properties.
- (Q1) For each `q`, the `E_a(q)` are orthogonal and sum to `I`.
- (Q2) `E_a(q)` and `E_b(q')` commute whenever `d(q, q') <= 2D`.
- (Q3) For every `p ∈ Λ` and every pattern `α` on `B_D` that does not occur in `X`,
  `∏_(f ∈ B_D) E_(α(f))(pf) = 0`.

`X` is *`D`-quantum rigid over `k`* if every `D`-quantum family over `k` commutes. For `Λ = Z^2` this
is the notion of `sft-crossed-product-fp-iff-quantum-rigid`. Rigidity is monotone in `D` and does not
depend on the choice of metric at large scale (route, Section 4).

**Theorem.** Let `Γ ≤ F(T)` be finitely presented and contain every `t_s` and `e_a`.
1. **Quantum rigidity.** There is `D_0`, depending only on a presentation of `Γ`, such that for every
   `D >= D_0` and every field `k`, `X` is `D`-quantum rigid over `k`. There is no restriction on the
   characteristic and none on the dimension of `W_0`.
2. **Finite type.** If also `V × {1} ≤ Γ`, then `X` is a subshift of finite type.

**Corollary.** `F(T) = A(T)` (`v-times-ample-full-groups-are-generated-by-transpositions`) contains
every `t_s`, every `e_a` and `V × {1}`. If `A(T)` is finitely presented, `X` is an SFT that is
`D`-quantum rigid over every field for all large `D`.

**Consequences for P2 (`v-times-minimal-free-sft-alternating-full-groups-are-fp`).**
- **P2 implies universal rigidity.** P2 implies that every minimal free SFT over every infinite
  finitely presented `Λ` is quantum rigid over every field at all large scales.
- **Labbé.** Over `Λ = Z^2`, P2 at Labbé's shift gives `labbe-wang-shift-crossed-product-is-finitely-presented`
  over every field (route `labbe-crossed-product-fp-via-v-full-group-fp`), and hence
  `free-minimal-z2-sft-is-quantum-rigid`. So P2 is at least as hard as those two open claims.
- **One noncommuting family refutes P2.** Any of the following, for a single minimal free SFT over a
  single infinite finitely presented `Λ`, refutes P2:
  - a noncommuting `D`-quantum family at arbitrarily large `D`, over any field;
  - over `Z^2`, a periodic quantum tiling at every scale (`periodic-quantum-tilings-refute-quantum-rigidity`),
    for example a proof of `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`;
  - over `Z^2`, an exactly matricial crossed product (`matricial-aperiodic-sft-rings-are-not-quantum-rigid`).
- **Finite type is forced.** Part 2 answers the question left in P2's status. The finite-type
  hypothesis of P2 cannot be dropped.

**Calibration.**
- A wall certificate, meaning two points differing on two far parts with a basis switch on one part,
  is a `D`-quantum family on `k^2`. So part 1 contains part 1 of
  `fp-v-times-subshift-full-groups-force-connected-differences`, and with it the finite-asymptotic-pair
  and zero-entropy kills.
- The `V` factor is what makes the argument one step. Site-conditioned 3-cycles act on `k[C_0]`, and
  `(H - 1)^2 ≠ 0` there in every characteristic, so one commutator relation of `F(T)` gives commutation
  directly. Without `V`, the graph needs the 17-term certificate and excludes characteristics 3 and 5.
- **Not proved: the converse.** Whether quantum rigidity of a minimal free SFT makes `F(T)`
  finitely presented is open. The crossed-product analogue over `Z^2` holds
  (`sft-crossed-product-fp-iff-quantum-rigid`).

Route: `fp-v-times-subshift-full-groups-force-quantum-rigidity-proof`.
