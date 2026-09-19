---
rg: 2
id: linear-m11-bouquet-recursions-are-not-finitely-presented
kind: claim
title: If the stable relators of a fully self-replicating group lie in two free factors of F that share a sub-basis of finite image, and neither factor maps onto G, then G is not finitely presented; so no two-letter bouquet recursion under (U) and (L1) is finitely presented, in particular none of the 472 linear M_11 bouquets, and no member of the 62,500-recursion family
artifacts:
  - experiments/bouquet-amalgam-obstruction-2026-09-19/bouquet_amalgam.py
  - experiments/bouquet-amalgam-obstruction-2026-09-19/bouquet_amalgam.out
  - experiments/bouquet-amalgam-obstruction-2026-09-19/survivor_kurosh.py
  - experiments/bouquet-amalgam-obstruction-2026-09-19/survivor_kurosh.out
distinct_from:
  pure-loop-self-replicating-groups-are-not-fp: that obstruction needs the stable relators to split along a partition of the basis (a free product); this allows the two factors to share basis letters whose image is finite (an amalgam over a finite group), which is exactly what the bouquet class needs, since both factors contain the loop T.
  same-point-loop-recursions-reduce-to-loop-graph-words: that shows the stable relators of a bouquet are sections of relators in C_z = F(S, T) and leaves the 472 linear bouquets open, because (C'') fails at z; this proves those sections lie in F(S, T) or F(a, e, T) and closes all 472 by amalgamating over the finite group <T>.
  linear-bouquet-recursions-ray-loop-and-contraction: that decides 108 of the 472 through the ray-loop group H and contraction, and leaves 364 open (20 commuting survivors with H = Z x C_k, 212 with H infinite, 132 undecided); this decides all 472 at once and never uses H.
  fp-self-similar-groups-have-fp-ray-loop-subgroups: that constrains finitely presented groups through finite presentability of ray-loop subgroups, which is silent for the 20 survivors (H = Z x C_k is finitely presented); this constrains them through the one-endedness of G against a finite-edge splitting of the stable presentation.
---

**ESTABLISHED (unreviewed).** Proof: `linear-m11-bouquet-recursions-are-not-finitely-presented-proof`.
Items 1 and 2 are proved by hand. Item 3 checks finitely many exact conditions (letter
sections, reduced words, and one certified finite order per recursion), which
`bouquet_amalgam.py` decides. Points are coded `0..10` as in the cited scripts.

**Setting.** As in `pure-loop-self-replicating-groups-are-not-fp`: `G = F/K` is a fully
self-replicating self-similar group (`G = G^X ⋊ P`) with (SF), `ρ : F ↠ G`, and `Q^∞` is the
stable part of the section closure of a finite normal generating set of `K`.

**Theorem.**

1. **Finite-edge amalgam obstruction.** Let `F` have a basis `B_1 ⊔ B_0 ⊔ B_2`, and put
   `F_1 = F(B_1 ∪ B_0)`, `F_2 = F(B_0 ∪ B_2)` and `F_0 = F(B_0)`, so `F = F_1 *_{F_0} F_2`.
   Suppose that
   - (i) `ρ(F_0)` is finite;
   - (ii) whenever `G` is finitely presented, every word of `Q^∞` is conjugate into `F_1` or
     into `F_2`;
   - (iii) `ρ(F_1) ≠ G` and `ρ(F_2) ≠ G`.

   Then `G` is **not finitely presented**. With `B_0 = ∅` this is item 2 of
   `pure-loop-self-replicating-groups-are-not-fp`.

2. **Two-letter bouquets.** Assume (U) and (L1) of
   `same-point-loop-recursions-reduce-to-loop-graph-words`, and assume `P` does not fix the
   point `z` below. Let `s` and `t` be the only state letters, with loop graph `Γ_1` a
   bouquet at `z` (`r_s = w_s = r_t = w_t = z`). Then `G` is **not finitely presented**.
   - By (L1), at most one of `s`, `t` occurs in an off-loop section of the other. Call `t` a
     letter that does not reach `s`.
   - If `s` does not reach `t` either, both letters are bounded, and the bounded kill of that
     node's item 5 applies.
   - Otherwise take the basis `{rooted letters, S = ℓ_s, T = ℓ_t}`, with `B_0 = {T}`,
     `B_2 = {S}` and `B_1` the rooted letters. Then `F_1 = F(rooted, t)` and `F_2 = F(S, T)`.
   - Hypothesis (i) holds because `T` is bounded with a single loop, hence of finite order.
   - Hypothesis (ii) holds because every stable relator is a section of a word in `F(S, T)`,
     and such sections lie in `F(S, T)` (along `z^n`) or in `F_1` (elsewhere).
   - Hypothesis (iii) holds because `ρ(F_2)` fixes `z`, while `ρ(F_1)` consists of bounded
     automorphisms and `s` is unbounded.

3. **The linear M_11 bouquets, and the whole family.** `bouquet_amalgam.py` confirms the
   hypotheses of item 2 on all 472 linear bouquet recursions of
   `same-point-loop-recursions-reduce-to-loop-graph-words` (item 5 there), in the basis
   `{a, e, S = A s B, T = C t D}`:
   - (B) `π_S` and `π_T` fix `z`, and `S|_z = S`, `T|_z = T` as reduced words;
   - (Tb) `t|_x` is a rooted word for every `x ≠ x_t`;
   - (Sb) `s|_x ∈ F(a, e, t)` for every `x ≠ x_s`, and (W) some such `s|_x` contains `t`;
   - (O) `ord T` is finite: it is 11 in 138 cases, 22 in 20 and 44 in 314. `ord S` is
     finite in 390 cases and infinite in 82, which matches the earlier bouquet data.

   So **none of the 472 is finitely presented.** This includes the 20 commuting survivors of
   `linear-bouquet-recursions-ray-loop-and-contraction`, whose loop group
   `H = ⟨S, T⟩ ≅ Z × C_k` is finitely presented, together with its 212 non-commuting
   recursions with `H` infinite and its 132 undecided ones. With the table of item 6 of
   `same-point-loop-recursions-reduce-to-loop-graph-words`, **no member of the
   62,500-recursion M_11 family is finitely presented**. So the family gives no Boone–Higman
   certificate.

**The step's case (468).** Recursion 468 is `π_s = β²`, `π_t = α²`, `s|_0 = β^{-1} s β^{-1}`,
`t|_0 = α^{-1} t α^{-1}` and `s|_3 = t`. It has `σ = τ = 1`, `[S, T] = 1`, `ord T = 11`, and
`S` of infinite order. In the basis `{a, e, S, T}`, the section closure of `{[S, T], T^11}` is
`{[S, T], T^11, a^11}`, and each of these words lies in `F(S, T)` or in `F(a, e)`.
`survivor_kurosh.py` finds the same three words for all 20 survivors. The obstruction does
not need these to be all the relators, because item 2 places every stable relator of every
finite presentation in `F(S, T) ∪ F(a, e, T)`.

**What escapes (design rule).** Item 2 applies to every two-letter bouquet under (U) and
(L1), for any root group `P` that does not fix `z`. A finitely presented self-similar host in this setting therefore needs
one of the following:
- at least three state letters;
- a letter section of weight at least 2, which breaks (U);
- a section cycle through two letters, which breaks (L1), as `R°` does.

In each case the aim is that no loop whose letter block is section-closed has finite order.
When that block does have finite order, the stable presentation splits over a finite group,
and one-endedness forbids the retraction.
