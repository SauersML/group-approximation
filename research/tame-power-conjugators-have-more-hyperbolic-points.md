---
rg: 2
id: tame-power-conjugators-have-more-hyperbolic-points
kind: claim
title: If tame homeomorphisms a, b of a perfect compactum satisfy b a b^-1 = a^k with |k| >= 2 and a of infinite order, then b has strictly more hyperbolic periodic points than a; so Baumslag--Gersten and Higman groups have no action in which the relevant generators are tame and of infinite order
distinct_from:
  bs-conjugators-of-wandering-maps-have-invariant-compacta: that treats a with finite non-wandering set only (no periodic clopen part) and conjugate b; this allows a clopen region where a has finite order, needs no conjugacy between a and b, and covers Higman's cyclic chains.
  baumslag-gersten-equicontinuous-generator-acts-trivially: that kills equicontinuous images of the Baumslag--Gersten generator; this kills the opposite, tame (Thompson-type, attractor--repeller) images.
  higman-group-embeds-in-no-almost-automorphism-group: that excludes one host family for H4 by its structure; this is a statement about arbitrary homeomorphisms of arbitrary perfect compact metric spaces, conditional only on the generators being tame.
---

**ESTABLISHED** by `tame-power-conjugator-proof` (lane proof, elementary; not
independently reviewed; no priority claimed).

## Definitions

`X` is a compact metric space with no isolated points. For `g ∈ Homeo(X)`, `Ω(g)` is the
non-wandering set, `W_g = X \ Ω(g)` the wandering set, and `Per(g)` the set of periodic
points. Call `g` **tame** if

- `Ω(g) = P_g ⊔ F_g` with `P_g` clopen, `g(P_g) = P_g`, `g|P_g` of finite order, and `F_g`
  finite; and
- `⟨g⟩` acts properly and cocompactly on `W_g` (properly: for compact `C ⊆ W_g` only
  finitely many `n` have `g^n C ∩ C ≠ ∅`; cocompactly: `W_g = ⋃_n g^n D` for a compact
  `D ⊆ W_g`).

`F_g` is the set of **hyperbolic periodic points** of `g`. A tame `g` has finite order iff
`W_g = ∅` iff `F_g = ∅` (see the route, Step 1).

Examples: north--south and attractor--repeller homeomorphisms of the Cantor set, with or
without a clopen region of finite order; these are the dynamics that revealing pairs
describe for elements of Thompson's group `V` (Brin; Salazar-Díaz; Belk--Matucci; not
re-read here, and not used).

## Statement

1. **Strict growth.** Let `a, b ∈ Homeo(X)` be tame, with `a` of infinite order, and
   suppose `b a b^-1 = a^k` for an integer `k` with `|k| ≥ 2`. Then `F_a ⊊ F_b`.
2. **Baumslag--Gersten groups.** Let `BG_k = ⟨a, t | b a b^-1 = a^k, b = t a t^-1⟩`,
   `|k| ≥ 2` (`k = 2` is the Baumslag--Gersten group). In any action of `BG_k` on `X` in
   which `a` acts tamely, `a` acts with finite order.
3. **Higman groups.** Let `n ≥ 1` and `H_n = ⟨a_1, …, a_n | a_(i+1) a_i a_(i+1)^-1 = a_i^2,
   indices mod n⟩` (`H_4` is Higman's group). In any action of `H_n` on `X` in which every
   `a_i` acts tamely, every `a_i` acts with finite order.
4. **Hosts.** If `Λ ≤ Homeo(X)` and every element of `Λ` is tame, then neither `BG_k` nor
   `H_n` (`n ≥ 4`) embeds in `Λ`. More precisely, in any homomorphism `BG_k → Λ`
   the generator `a` has finite-order image, and in any `H_n → Λ` every `a_i` does.

## Scope

- Item 1 is sharp in form: `BS(1,2)` acts on the circle by `a(x) = x + 1`, `b(x) = 2x`,
  with `F_a = {∞} ⊊ F_b = {0, ∞}` (the circle is not totally disconnected, but the proof
  never uses total disconnectedness). So item 1 does not exclude `BS(1,k)` from groups of
  tame maps; it excludes only relations that force `|F_b| ≤ |F_a|`.
- Item 4 is not new for `V`: `BG ⊇ BS(1,2)` has exponentially distorted cyclic subgroups,
  and `higman-group-embeds-in-no-almost-automorphism-group` already excludes `H4` from
  almost-automorphism groups, which contain `V`. Its point is that the obstruction is
  purely topological: it applies to any perfect compact metric space and any group of
  tame maps, and in mixed hosts (`nV`, Röver--Nekrashevych groups, `2V_τ`, germ
  extensions of `V`) it says which elements can play the roles of `a` and `b`.
- Nothing here constrains non-tame images: equicontinuous parts are handled by
  `baumslag-gersten-equicontinuous-generator-acts-trivially`, and wandering sets with no
  compact fundamental domain, or infinite `F`, are not covered.
