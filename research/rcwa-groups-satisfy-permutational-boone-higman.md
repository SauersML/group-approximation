---
rg: 2
id: rcwa-groups-satisfy-permutational-boone-higman
kind: claim
title: Every finitely generated group of residue-class-wise affine permutations of Z, of a number ring of class number one, of F_q[t] or of Z_(pi), and every RCWA_P group and CT_P(Z), satisfies the permutational Boone-Higman conjecture, because the RCWA hosts are finitely presented, simple and highly transitive
requires:
  - rcwa-groups-satisfy-boone-higman
  - rcwa-groups-over-pids-satisfy-boone-higman
  - fp-simple-highly-transitive-groups-satisfy-pbh
distinct_from:
  rcwa-groups-satisfy-boone-higman: that embeds RCWA groups in finitely presented simple hosts; this shows those hosts are highly transitive, which upgrades the conclusion to the permutational conjecture (type (A) actions, twisted Brin-Thompson groups).
  rcwa-groups-over-pids-satisfy-boone-higman: same relation, for the ax+b hosts over number rings, F_q[t] and Z_(pi).
---

**ESTABLISHED** (lane proof, not reviewed). It combines the two host nodes with
`fp-simple-highly-transitive-groups-satisfy-pbh` (BFFHZ arXiv:2503.21882v2, Theorem C,
(iii) ⟹ (i), "as does every subgroup thereof"). The only new input is the
high-transitivity lemma below. That lemma is standard in substance for full groups of
purely infinite minimal groupoids. BFFHZ Remark 3.5 is the Röver–Nekrashevych case. No
priority is claimed.

Write `B_A` for the class of groups that embed in a group with a type (A) action
(`boone-higman-type-a-class-closed-under-finite-extensions`).

## Statement

1. **The hosts are highly transitive.** The following groups act faithfully and
   highly transitively on every orbit of their groupoids:
   - the hosts `H_P` of `rcwa-groups-satisfy-boone-higman` (over `Z`, the odometer on
     `Λ_P × F_2^+`);
   - the hosts `H_P(R)` and `H_π(A)` of `rcwa-groups-over-pids-satisfy-boone-higman`;
   - Kohl's groups `CT_P(Z)`, for finite `P`.
2. **PBH for RCWA groups.** Let `R` be `Z`, the ring of integers of a number field of
   class number one, `F_q[t]`, or `Z_(π)`.
   - Every finitely generated subgroup of `RCWA(R)` lies in `B_A`. It satisfies the
     permutational Boone–Higman conjecture, and embeds in a finitely presented twisted
     Brin–Thompson group (Theorem C (ii)).
   - For each finite `P` (cases `Z`, (a), (b)), the whole group `RCWA_P(R)` lies in
     `B_A`.
3. **Class transpositions.** `CT_P(Z)` lies in `B_A` for every finite set `P` of odd primes.

## Proof

**Setting.** Let `G` be one of the groupoids above, with unit space `Y`. `Y` is a Cantor
set with a basis of clopen *rectangles*:
- `B × C(w)` for the hosts with a binary rose, where `B` is a box and `w` a binary word;
- boxes `B(r, m)` for `CT_P(Z)`.

The route nodes establish, and we use, three facts:
- every rectangle is mapped onto every other rectangle by a basic compact open bisection
  (minimality, as proved there);
- every rectangle splits into two disjoint rectangles:
  - `B × C(w) = B × C(w0) ⊔ B × C(w1)` for the binary-rose hosts;
  - `B(r, m) = B(r, 2m) ⊔ B(r + m, 2m)` for `CT_P(Z)`, using `2 ∈ P'`;
- `F(G)` acts on `Y` by homeomorphisms, and it is the group of global compact open
  bisections.

**Lemma 1 (clopen equivalence).** For nonempty clopen sets `A, A' ⊆ Y` there is a compact
open bisection `τ` with `s(τ) = A` and `r(τ) = A'`.

*Proof.* Write `A` as a disjoint union of `N ≥ 1` rectangles and `A'` as one of `M ≥ 1`.
Splitting one rectangle raises the count by one, so we may take `N = M`. Then map the
`j`-th rectangle of `A` onto the `j`-th rectangle of `A'` by a basic bisection. ∎

**Lemma 2 (high transitivity).** Let `O ⊆ Y` be a `G`-orbit.
- `O` is countably infinite: it is dense because `G` is minimal, and countable because
  `G` has countably many basic bisections.
- `F(G)` preserves `O`, and it acts faithfully on `O`: an element fixing the dense set `O`
  pointwise is the identity, by continuity.
- `F(G)` acts `k`-transitively on `O` for every `k`.

*Proof of `k`-transitivity.* Let `x_1, …, x_k` and `y_1, …, y_k` be two lists of distinct
points of `O`.
- **Local maps.** For each `i`, pick a compact open bisection `σ_i` containing an arrow
  from `x_i` to `y_i`. Restrict it to a small clopen neighbourhood `U_i` of `x_i`, with
  image `V_i := σ_i(U_i) ∋ y_i`.
- **Shrinking.** Shrinking the `U_i` makes `U_1, …, U_k` pairwise disjoint and
  `V_1, …, V_k` pairwise disjoint. It also makes `A = Y ∖ ⋃U_i` and `A' = Y ∖ ⋃V_i`
  nonempty, since `Y` has no isolated points.
- **Gluing.** Lemma 1 gives `τ : A → A'`. Then `f = τ ⊔ σ_1|_{U_1} ⊔ ⋯ ⊔ σ_k|_{U_k}` is a
  compact open bisection with source and range `Y`. So `f ∈ F(G)`, and `f(x_i) = y_i`. ∎

**Conclusion.**
- **Finitely presented, simple, highly transitive.** By the two host nodes and
  `ct-p-z-is-a-one-vertex-k-graph-full-group`, each group in item 1 is finitely presented
  and simple. By Lemma 2 it is highly transitive, in BFFHZ's sense: a faithful action that
  is `k`-transitive for all `k`.
- **Into `B_A`.** By `fp-simple-highly-transitive-groups-satisfy-pbh`, every subgroup of
  such a group, finitely generated or not, lies in `B_A`.
- **The RCWA groups.**
  - `RCWA_P(R)` embeds in the corresponding host.
  - A finitely generated subgroup of `RCWA(R)` lies in some `RCWA_P(R)`. For `Z_(π)`, it
    first embeds in `RCWA_π(Z[1/N])` (Step 8 of `rcwa-over-pids-bh-via-ax-plus-b-monoid-hosts-proof`).
- **`CT_P(Z)`** is itself one of the hosts. ∎

## Remarks

- **`CT(Z)` itself.** `CT(Z) = ⋃_P CT_P(Z)` is a directed union of groups in `B_A`. It is
  not finitely generated. Whether it, or `RCWA(Z)`, embeds in a single finitely presented
  simple group is open. Every host here involves finitely many primes.
- **Twisted Brin–Thompson targets.** Theorem C (ii) gives, for each finitely generated
  RCWA group, an embedding in a finitely presented simple twisted Brin–Thompson group.
  That group is abstract (from BFFHZ Theorem E) and not explicit.
