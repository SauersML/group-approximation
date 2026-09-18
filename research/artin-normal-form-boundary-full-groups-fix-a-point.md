---
rg: 2
id: artin-normal-form-boundary-full-groups-fix-a-point
kind: claim
title: The Deligne normal-form boundary of a finite-type Artin group has a global fixed point, so its topological full group is never simple
distinct_from:
  spherical-artin-groups-satisfy-boone-higman: that is Boone--Higman for spherical Artin groups, established on main through the characteristic-zero linear route; this is a structural fact about one boundary action, and proves no embedding.
  automatic-groups-satisfy-boone-higman: that is the open survey item 5.3(11); this constrains how the Belk--Bleak--Chatterji--Matucci--Perego rational boundary of a finite-type Artin group can feed it.
artifacts:
  - research/artifacts/gq-bh-bh-free-15-2026-preprints.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Setting

- `A` is an Artin group of finite type with at least two Artin generators, and `Δ` is
  its Garside element.
- `τ(x) = Δ x Δ^{-1}` is the involution that permutes the simple elements `(1,Δ]` and
  fixes `Δ`.
- `L` is the Deligne normal form over `X = (1,Δ] ∪ {Δ^{-1}}`, as in
  Belk--Bleak--Chatterji--Matucci--Perego (preliminary 2026, §2.3, Theorem 2.4;
  artifact `gq-bh-bh-free-15-2026-preprints.md`).
- `∂L ⊆ X^ω` is its normal-form boundary. By their Theorem 2.4, `A` acts
  continuously and faithfully on `L ∪ ∂L`.
- `[[A | ∂L]]` is the topological full group: homeomorphisms of `∂L` that agree
  with an element of `A` on each piece of some finite clopen partition.

## Statement

Let `p = Δ^{-1}Δ^{-1}Δ^{-1}⋯ ∈ X^ω`.
1. `p ∈ ∂L`, and every element of `A` fixes `p`.
2. Every element of `[[A | ∂L]]` fixes `p`.
3. The germ of `Δ` at `p` has infinite order in the group of germs at `p`.
4. Let `N_p ⊴ [[A | ∂L]]` be the kernel of the germ map at `p`, i.e. the elements
   that are the identity near `p`. Then `1 ≠ N_p ≠ [[A | ∂L]]`, and
   `[[A | ∂L]] = A · N_p`. In particular `[[A | ∂L]]` is not simple, and
   `[[A | ∂L]] / N_p` is the germ group of `A` at `p`, a quotient of `A` in which
   `Δ` has infinite order.

## Proof

1. **`p` is a boundary point.** `Δ^{-j} ∈ L` for each `j ≥ 0`: the least `k` with
   `Δ^k Δ^{-j} ∈ A^+` is `k = j`, and the left-greedy form of `1` is empty. Also
   `Δ^{-j} → p`, so `p ∈ ∂L`.
2. **Generators fix `p`.** Let `s ∈ X`. By continuity, `s·p = lim_j s·Δ^{-j}`.
   - `s = Δ^{-1}` gives `Δ^{-(j+1)}`, and `s = Δ` gives `Δ^{-(j-1)}`. Both tend to `p`.
   - Let `s ∈ (1,Δ)`. Then `s Δ^{-j} = Δ^{-j} τ^j(s)`, and `τ^j(s)` is a simple element
     other than `1` and `Δ`. For `k < j`, `Δ^k Δ^{-j} τ^j(s) ∈ A^+` would force
     `Δ^{j-k}` to left-divide `τ^j(s)`. That is impossible, since
     `|τ^j(s)| = |s| < |Δ|`. So the Deligne normal form of `s·Δ^{-j}` is the word
     `Δ^{-j} τ^j(s)`, which shares its first `j` letters with `p`. Hence `s·p = p`.
   - `X` generates `A` as a monoid (`a^{-1} = Δ^{-1}(a^{-1}Δ)` with `a^{-1}Δ` simple),
     so every `g ∈ A` fixes `p`.
3. **Full-group elements fix `p`.** Let `f ∈ [[A | ∂L]]` agree with `g_i ∈ A` on a
   clopen piece `U_i` containing `p`. Then `f(p) = g_i(p) = p`.
4. **Points near `p`.**
   - By their proof of Theorem 2.4, `w = a^∞ ∈ ∂L` for any Artin generator `a`, and
     its first letter `a` is not `Δ`.
   - So `r_j = Δ^{-j} w` is a valid infinite normal form. It is the limit of
     `Δ^{-j} a^n ∈ L`, so `r_j ∈ ∂L`, and `r_j → p`.
5. **The germ of `Δ` has infinite order.** For `m ≠ 0` and `j > |m|`,
   `Δ^m · r_j = Δ^{-(j-m)} w`. That is a normal form with `j - m ≠ j` leading
   letters `Δ^{-1}`, so it differs from `r_j`. Hence `Δ^m` is not the identity on
   any neighborhood of `p`.
6. **`N_p` is a proper normal subgroup.** The germ map at `p` is a homomorphism,
   since all of `[[A | ∂L]]` fixes `p`. So `N_p` is normal. It is proper because
   `Δ ∉ N_p`, by step 5.
7. **`N_p` is nontrivial.**
   - Pick `a ∈ A`, `a ≠ 1`. The action is faithful, so some `x` has `a·x ≠ x`, and
     `x ≠ p`.
   - Choose a clopen `U ∋ x` with `p ∉ U` and `aU ∩ U = ∅`. Then `p ∉ aU`, because
     `a·p = p`.
   - Let `t` be `a` on `U`, `a^{-1}` on `aU`, and the identity elsewhere. Then
     `t ∈ [[A | ∂L]]`, `t ≠ 1`, and `t` is the identity near `p`.
8. **`[[A | ∂L]] = A · N_p`.** Take `f` as in step 3. Then `g_i^{-1} f` is the
   identity on `U_i ∋ p`, so it lies in `N_p`. So every element is in `A · N_p`, and
   the quotient is the image of `A` in the germ group. ∎

## Consequence (lane remark)

Belk--Bleak--Chatterji--Matucci--Perego (their p. 6) propose passing from
`[[G | ∂L]]` to a finitely presented simple twisted Brin--Thompson group, as for
hyperbolic groups. For finite-type Artin groups that program cannot use
`[[A | ∂L]]` itself as the simple host. Every simple subgroup lies in `N_p`, or maps
injectively onto a simple subquotient of the germ group, and `A` meets `N_p`
trivially whenever `A` acts with nontrivial germ at `p`. A Boone--Higman host for
`A` along this route needs one of:
- the `A ∗ Z` boundary (their Theorem 2.9, a Cantor space with a faithful action);
- a type (A) step;
- a doubling of `∂L` that removes the fixed point.
Their Question 1.12 (Artin groups of finite type into finitely presented simple
groups) stays open in the literature. On main it is marked ESTABLISHED only through
the characteristic-zero linear route (see `bh-verify-artin`, `bh-verify-linear`).
