---
rg: 2
id: finitary-permutations-force-singleton-domains
kind: claim
title: In a Farley–Hughes certificate with the compact ultrametric property and point-separating domains, every point moved by a transposition in Γ_S is a singleton domain; so for seed full groups, which contain all finitary permutations of the seed orbit, orbit points always have finite addresses, and the seed-address loophole of the complexity cap is closed
distinct_from:
  finite-type-farley-hughes-groups-are-exponentially-capped: that caps certificates in which the seed is a domain; this proves that for seed full groups the seed is always a domain, removing the review's qualifier 1.
  farley-hughes-complexity-caps-review: that leaves open certificates in which the seed has an infinite address, where hardness could hide in addr(y_*); this closes that door for every group containing FSym of the orbit.
---

**ESTABLISHED** (lane bh-invent-03, 2026-09-19; elementary; **Referee PASS** bh-ref-q11 2026-09-19, with one precision on item 2). The Farley–Hughes notions are from
arXiv:2010.08035: Def. 3.12, Cor. 3.8, Remark 3.15.

## Statement

Let `S` be an inverse semigroup of partial bijections of a set `X`, with `D_S^+` nested and with finite
complementation (FH Def. 3.12). Assume the domains **separate points**: for `x ≠ z` some domain contains `x` but not
`z`.

1. If the transposition `(x z)` lies in `Γ_S`, then `{x}` and `{z}` are domains.
2. **Seeds.** Let `F = [[Γ ⋉ Y]]` be a seed full group with seed orbit `O`, so `F ⊇ FSym(O)`
   (`seed-full-groups-act-oligomorphically-on-the-seed-orbit`). Then for any such certificate on any `X ⊇ O`
   (for instance `X = O` or `X = Y`) with `F ≤ Γ_S`, every point of `O` is a singleton domain. In particular
   `addr(y_*)` is finite.

## Proof

1. **Setting up.** Write `τ = (x z)` as a finite disjoint union of S-maps `s_i : D_i -> D_i'`, with the `D_i`
   partitioning `X`. Let `D` be the piece containing `x`, and `s` its map.
   - **Refining the piece.** Choose a domain `E` with `x ∈ E` and `z ∉ E`. Since `D` and `E` meet, they are
     nested. If `E ⊊ D`, then `D ∖ E` is a finite disjoint union of domains (Remark 3.15). Replace the piece `D` by
     `E` and those domains, restricting `s` to each; restrictions of S-maps are S-maps (Cor. 3.8). So we may assume
     `z ∉ D`.
   - **Where `s` sends `D`.** On `D`, `s` agrees with `τ`: it sends `x ↦ z` and fixes `D ∖ {x}`, because `z ∉ D`.
     So `s(D) = (D ∖ {x}) ∪ {z}`, which is a domain.
   - **The contradiction.** If `|D| ≥ 2`, then `D ∩ s(D) = D ∖ {x} ≠ ∅`, so `D` and `s(D)` are nested. But
     `x ∈ D ∖ s(D)` and `z ∈ s(D) ∖ D`. Hence `D = {x}`.
   - **The same for `z`.**
2. Apply 1 to `(y_* z)` for any `z ∈ O ∖ {y_*}`. ∎

## Consequence for the hard-actor row

- **Where the review left it.** `farley-hughes-complexity-caps-review` left two doors open for a hard seed certified
  by an FH engine: (a) a seed with an infinite address, and (b) non-restriction-closed structures, as in Röver's
  certificate, whose maximal structure groups are infinite.
- **Door (a) is closed** for seed full groups by item 2, as long as the domains separate points. Non-separating
  certificates cannot distinguish points that no domain separates, which is a degenerate case.
- **Only door (b) remains.** Every FH certificate of a seed full group gives the seed a finite address. The cap of
  `finite-type-farley-hughes-groups-are-exponentially-capped` then applies whenever the S-maps are finite-state. So a
  hard seed must come from a certificate whose S-maps have **infinitely many states**, necessarily through a
  non-restriction-closed chosen structure with finite-state-violating sections.
  - Röver's certificate is of this kind, but it is finite-state through Grigorchuk's automaton.

## Lesson for general BH

**Finitary permutations pin points.** Any finiteness certificate of Farley–Hughes type for a group containing all
finitary permutations of an orbit must make each orbit point its own domain. Hardness can therefore never hide in
*where* the seed is. It can hide only in *how the structure maps act*: in infinite-state S-maps, which in
Röver-type certificates arise from the sections of the ambient maximal structure groups.

## Referee (bh-ref-q11, 2026-09-19): PASS; one precision on item 2

**Sources, checked at arXiv:2010.08035v1.**
- Cor. 3.8: `s|_D ∈ S` for every domain `D ⊆ dom s`.
- Def. 3.12: nested domains, and `X − D` is a finite union of domains.
- Remark 3.15: the finite difference property `D_2 − D_1`, which the refinement step uses.

**Item 1, the "forced own domain" step: correct.**
- After refining the piece `D ∋ x` by a separating domain `E` (if `E ⊊ D`, replace `D` by `E` and the finitely many domains of `D − E`), the piece containing `x` misses `z`.
- There `s = τ`, so `s(D) = (D ∖ {x}) ∪ {z}`. This is a domain, since images of S-maps are domains of their inverses.
- If `|D| ≥ 2`, then `D` and `s(D)` meet in `D ∖ {x}`, while `x ∈ D ∖ s(D)` and `z ∈ s(D) ∖ D`. That contradicts nestedness. So `{x}` is a domain, and symmetrically `{z}`.
- Point separation is used exactly once, to pick `E`.

**Item 2: correct**, with a precision on the hypothesis. It needs the element of `F` realizing `(y_* z)` on `O` to act on the certificate's `X` as the transposition, fixing `X ∖ {y_*, z}`.
- This holds for `X = O`.
- It holds for `X = Y` when the seed orbit consists of isolated points of `Y`, as for SFT compactifications with an isolated seed (C1). There the transposition of two isolated points is a homeomorphism, locally given by one group element.
- For an arbitrary `X ⊇ O` on which `F` acts, "any such certificate on any `X ⊇ O`" should add this as a hypothesis, or be restricted to `X ∈ {O, Y}`.
- The full-group containment `F ⊇ FSym(O)` is imported from `seed-full-groups-act-oligomorphically-on-the-seed-orbit`, which I did not re-referee.

**Consequence.** Door (a) of the review is closed for point-separating certificates, as stated.
- The remark that non-separating certificates are degenerate is heuristic, but it does not affect the claim.
- "Only door (b) remains" is conditional on the exponential-cap node, as the text says.
