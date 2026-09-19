---
rg: 2
id: magnus-staggered-chain-sofic
kind: claim
title: The staggered Magnus chain of a one-relator kernel is sofic
distinct_from:
  linton-shell-sofic: that is the rational-derived picture of the same difficulty — a semidirect product of the radical by a free group; this is the Magnus picture — a bi-infinite amalgam over free edge groups. Fox--Magnus descent now links their first-order quotients, but no second-order translation across `R'` is known, so a proof of either open claim is still not a proof of the other.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that uses the relation module to close the quotient modulo `R'`; this asks for soficity of the full bi-infinite nonabelian chain beyond exactly that first-order boundary.
  one-relator-groups-sofic: that is the question in full; this is the specific amalgamation theorem that would close it through the Magnus hierarchy, and is strictly weaker than closure under amalgamation over arbitrary free subgroups.
  sofic-radical-soficization: that identifies the sofic radical as the kernel of soficization, a construction applied to an arbitrary group; this is an amalgamation statement about a specific bi-infinite chain of one-relator pieces, and no radical or soficization appears in it.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

OPEN.  Let `G = <a, t | w>` be a two-generator one-relator group with an
epimorphism `χ : G ↠ Z` arranged (after Nielsen moves) so that the exponent sum
of `t` in `w` is zero.  Put `a_i = t^{-i} a t^i`, write the relator as
`W_0 = W_0(a_m, …, a_n)` with `m` and `n` the extreme indices occurring, and let
`W_i` be its shifts.  Then

    K = ker χ = < a_i (i ∈ Z) | W_i (i ∈ Z) >

is the bi-infinite iterated amalgam of the one-relator pieces
`B_i = <a_{m+i}, …, a_{n+i} | W_i>` over the free Magnus subgroups
`C_i = <a_{m+i+1}, …, a_{n+i}>` (Freiheitssatz).

By [[groups-with-staggered-presentations-are-coherent]], every such infinite
staggered chain `K` is coherent. This is a genuine finiteness theorem for all
of its finitely generated subgroups, but it does not imply the finite
permutation approximations required below.

Claim: every such `K` is sofic.

Because `G/K ≅ Z` is amenable and soficity passes to subgroups, `G` is sofic
**iff** `K` is.  So this is not a convenience reformulation — for such a `χ` it
is the whole question, and it routes to [[one-relator-groups-sofic]] via
`one-relator-sofic-via-magnus-staggered-amalgam`.

## Why it is weaker than what one would otherwise ask for

The obvious sufficient statement — "an amalgam of sofic groups over a free
subgroup is sofic" — is a general permanence property nobody has and which would
be a major theorem in its own right.  This claim asks for it only for chains
that actually arise from a one-relator kernel: the vertex groups are shorter
one-relator groups, the edge groups are Magnus subgroups of them, and the
embeddings are the two Freiheitssatz inclusions of consecutive windows.  That is
a much smaller class, and the one-relator origin is the only leverage available.

## Attempts

1. **Rank-one edge groups.**  *Works, and marks the boundary.*  If every
   `rank C_i <= 1` the edge groups are amenable; existing permanence for
   amalgams and HNN extensions over amenable subgroups, plus closure under
   directed unions, makes `K` sofic and hence `G` sofic.  The claim is therefore
   already established on the sub-family `n - m <= 1`.
2. **Induct on relator length.**  *Dies on the window, not on the edge.*  The
   pieces `B_i` are shorter one-relator groups, so induction looks available —
   but a finite interval of the chain is **not** a one-relator group. It carries
   several staggered relators `W_i`. Jaikin-Zapirain--Linton now prove that
   every such finite staggered window is coherent, but the induction hypothesis
   needed here is soficity, so the induction still never starts. The distinction
   matters because "each piece is a smaller one-relator group" is true and
   misleading in the same breath.
3. **Rank `>= 2` edge groups via general amalgamation permanence.**  *Dies for
   want of a theorem.*  When `rank C_i = n - m >= 2` the edge group is a
   nonamenable free group and nothing in the standard permanence toolkit
   applies.
4. **Recent graph-of-groups soficity results.**  *Dies on hypothesis mismatch.*
   Gao--Kunnawalkam Elayavalli--Mj (arXiv:2408.11724) handle doubles and graphs
   with identical or separability-controlled edge embeddings.  A Magnus HNN uses
   **two distinct** embeddings of the free associated subgroup into the base,
   and nothing identifies them or supplies the separability hypothesis.  This is
   the same wall Berlai reports, and the same one the earlier Magnus/HNN
   experiments in this corpus keep meeting.
5. **Turn the obstruction into a witness.**  *Deferred, and the negative
   counterpart.*  Rather than prove the chain sofic, show for a specific
   `π(w) = 2` relator that the finite permutation models of the free-edge
   amalgam violate a rigidity inequality — the shape of attack in
   [[nonsofic-one-relator-group]] attempt 6.  No candidate inequality exists, and
   local indicability rules out the Kun--Thom style of one.
6. **Pass to first-order Fox lamps.**  *Completed, but not a completion of this
   claim.*  [[one-relator-fox-magnus-descent-to-derived-linton-radical]] shows
   that the mod-`k` Magnus map has kernel exactly `R'` in the Linton picture and
   gives a finite-lamp wreath embedding of the quotient.  The free-edge
   coupling that remains here is therefore genuinely second-order and cannot
   be removed by iterating abelian relation modules in the `k = 1` perfect
   regime.
