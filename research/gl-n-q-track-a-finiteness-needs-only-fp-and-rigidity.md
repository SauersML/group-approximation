---
rg: 2
id: gl-n-q-track-a-finiteness-needs-only-fp-and-rigidity
kind: claim
title: For the GL_n(Q) Track A group (St_10(R_L)*Z) x Z^2, the group-side finiteness gates ask nothing of St_10(R_L) beyond finite presentation, so E3' = P2'a = (A_N) in degree 1, which needs quantum rigidity of the SFT and the open group-side rigidity-to-finite-presentation theorem; St_10(R_L) is not of type FP_3 if its degree-3 Steinberg homology stabilizes by rank 10, which would bar these hosts from type F_3
requires:
  - v-times-subshift-full-group-finiteness-is-horizontal
  - v-times-gluing-presentations-are-exact
  - leavitt-resolvent-k-theory-is-shifted-rational-k-theory
  - gl-n-q-bh-via-track-a-over-st-10-times-free-group
distinct_from:
  gl-n-q-bh-via-track-a-over-st-10-times-free-group: that is the route and its gate map; this settles which finiteness properties of the acting group the group-side gates E3', (A_N) and P2' need there, and records the higher-finiteness limit coming from K_3.
  v-times-subshift-full-group-finiteness-is-horizontal: that proves (B_N) for every finitely generated group and topologically free subshift; this reads it for one acting group and adds the finiteness bookkeeping of that group.
  leavitt-resolvent-k-theory-is-shifted-rational-k-theory: that computes K_*(R_L) = K_(*-1)(Q); this uses K_3(R_L) = K_2(Q) to bound the finiteness type of St_10(R_L).
---

**ESTABLISHED** for parts 1–3, as a reading of the cited nodes, which are unreviewed lane proofs (P2′b is under
referee). Part 4 is a **conditional** statement, and it is proved as stated. Lane bh-gln-tracka, 2026-09-18; no
priority claimed.

## Setting

- `Λ_0 = (St_10(R_L) * Z) × Z^2`, the Track A group for `GL_n(Q)` from bh-g1-simulation
  (`gl-n-q-bh-via-track-a-over-st-10-times-free-group`, Update).
- `X` is the minimal free SFT over `Λ_0` from `free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2`.
- `F = F(G_V × (Λ_0 ⋉ X))` is the group-side host.

## Statement

1. **What the acting group must satisfy.**
   - `Λ_0` is finitely presented: `St_10(R_L)` is (Krstić–McCool / gq-referee-c), and free products with `Z` and
     direct products with `Z^2` keep finite presentation.
   - `Λ_0` has solvable word problem (`leavitt-resolvent-k2-stability-holds`, item 4) and contains every `GL_n(Q)`.
   - Nothing else about `St_10(R_L)` enters the group-side finiteness gates.
     - The descending-link condition (B_N) holds in every degree for every finitely generated `Λ` and every
       topologically free `X` (`v-times-subshift-full-group-finiteness-is-horizontal`, part 2).
     - Topological freeness makes all cell stabilizers finite, so no finiteness of `Λ_0` or of its stabilizers is
       used there.
2. **P2′b is free.** `v-times-gluing-presentations-are-exact` gives `K = 1` for every `Λ` and every `X`. For finitely
   presented `Λ_0` it reduces finite presentation of `F` to that of `N_X = LC(X, V) ⋊ Λ_0`.
3. **So E3′ comes down to rigidity for this `Λ_0`.** By part 2, `F` is finitely presented iff `N_X` is. That is P2′a
   (`rigid-sfts-give-fp-v-boolean-power-crossed-products`, OPEN), which asks for finite presentation from quantum rigidity of `X`. Rigidity is necessary
   (`topologically-free-subshift-full-groups-force-quantum-rigidity`), and it is the only input beyond part 1. By the horizontal criterion (part 3 there), this is the same as the degree-1 horizontal
   condition (A_N) for this `X`. For 5.3(5) the open list is therefore:
   - quantum rigidity of `X` (the plane-constant layers, `plane-constant-simulation-computation-layers-are-quantum-rigid`,
     where bh-g1-simulation reports that bounded determination is impossible);
   - the group analogue of the ring FTR, `rigid-sfts-give-fp-v-boolean-power-crossed-products`;
   - lemma (E) of `identifier-markers-give-decidable-free-subshifts` (review-critical, per bh-g1-simulation).
4. **Higher finiteness: a conditional limit from `K_3`.**
   - `H_3(St(R_L); Z) ≅ K_3(R_L) ≅ K_2(Q)`, and this is not finitely generated. The first isomorphism is Gersten's
     theorem (*K_3 of a ring is H_3 of the Steinberg group*, Proc. AMS 37 (1973); recalled, not re-read). The second
     is `leavitt-resolvent-k-theory-is-shifted-rational-k-theory`. And `K_2(Q) ≅ Z/2 ⊕ ⊕_(p odd) F_p^×` by Tate
     (recalled).
   - **Hence:** if `H_3(St_10(R_L); Z) → H_3(St(R_L); Z)` is surjective, `St_10(R_L)` is not of type `FP_3`. Then
     neither is `Λ_0`: a free product with `Z`, or a direct product with `Z^2`, of a non-`FP_3` group is not `FP_3`.
   - If, as expected from the domain/Rips analogy of the horizontal criterion (not proved), type `F_3` of `F` forces
     type `F_3` of `Λ_0`, then no host built over `St_10(R_L)` in this way is `F_3`. That concerns only
     `F_∞`-host questions (Zaremsky's question, BBMZ Q1.2), not Boone–Higman, which needs finite presentation only.

## Proof

**1.** The finite-presentation and word-problem facts are the cited nodes, plus the standard closure of finite
presentation and solvable word problem under free products and direct products. The (B_N) statement is part 2 of
the horizontal criterion. Its setting assumes only that `Λ` is finitely generated and that `X` is topologically
free; the finite-stabilizer clause is its part 1c.

**2–3.** These are the "Consequences" of `v-times-gluing-presentations-are-exact` and parts 1–3 of the horizontal
criterion, read for `Λ_0`.

**4.**
- Suppose `St_10(R_L)` were `FP_3`. Then `H_3(St_10(R_L); Z)` would be finitely generated, and so would its image.
  Under the surjectivity hypothesis that image is `K_2(Q)`, which is not finitely generated. So `St_10(R_L)` is not
  `FP_3`.
- *Retracts.* A retract of an `FP_n` group is `FP_n` (standard, recalled). `St_10(R_L)` is a retract of
  `St_10(R_L) * Z` (kill `Z`), and that is a retract of `(St_10(R_L) * Z) × Z^2` (project).

So `Λ_0` is `FP_3` only if `St_10(R_L)` is. ∎

## Reading

- For Boone–Higman on this route, the group side has been emptied of everything except rigidity.
  - Links: (B_N), every `Λ`.
  - Gluing: P2′b, every `Λ`.
  - Finite presentation of `Λ_0`: supplied by `St_10(R_L)`.
  - What is left is (A_N) degree 1, i.e. P2′a, i.e. quantum rigidity of one explicit minimal free SFT over
    `(St_10(R_L) * Z) × Z^2` plus the group-side finite-type-plus-rigidity theorem.
- The acting group enters only through finite presentation. So the Kazhdan property, the huge centre `Q^×` and the
  absence of finite quotients of `St_10(R_L)` are irrelevant to the group-side gates, provided the SFT is rigid.
- Higher finiteness is a different matter. `K_3(R_L) = K_2(Q)` records every prime's tame symbol. If degree-3
  stability holds at rank 10, this is exactly the obstruction that stops `St_10(R_L)` at type `F_2`. Then `F_∞`
  hosts of `GL_n(Q)` need a different finitely presented overgroup, one whose `K_3`-type homology is finitely
  generated.

## Lesson for general BH

The group-side master route consumes exactly one property of the acting group: finite presentation.
- Descending links and gluing are universal: (B_N) holds for every finitely generated `Λ`, and P2′b for every `Λ`.
- So once the acting group is finitely presented, the whole route is quantum rigidity of one SFT, together with
  the open theorem that rigidity gives finite presentation on the group side.

Higher finiteness of the host, by contrast, sees the higher homology of the acting group. For Steinberg-type
overgroups that homology is algebraic K-theory. There the arithmetic that finite presentation absorbed, one tame
symbol per prime, reappears in `K_3`.
