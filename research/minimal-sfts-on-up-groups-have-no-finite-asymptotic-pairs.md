---
rg: 2
id: minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs
kind: claim
title: A minimal subshift of finite type over a group whose real group ring has no nonnegative zero divisor, in particular over any unique-product group, has no finite asymptotic pairs and is boundary-deterministic
distinct_from:
  fp-crossed-products-force-connected-differences: that derives no finite asymptotic pairs and boundary determinism from finite presentation of a crossed product; this derives them from minimality and finite type alone, over unique-product groups, so parts 2 and 3 there carry no extra content over such groups.
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is the open finiteness premise P2; this shows that a counterexample to P2 through a finite asymptotic pair must use an acting group with a nonnegative zero divisor, for example one with torsion.
  positive-entropy-sft-crossed-products-are-not-fp: that kills positive entropy over Z^2 through a measure and recurrence; this is a measure-free descent that works over non-amenable unique-product groups, where entropy says nothing.
---

**ESTABLISHED (unreviewed).** Proof: `minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs-proof`.
The proof is self-contained apart from Gordan's theorem of the alternative (1873), a standard fact
of finite-dimensional linear algebra. No novelty is claimed. Over `Z^d` the conclusion also
follows from the Quas--Trow zero-entropy theorem (context only, not re-read).

## Setting

- `Λ` is a countable group, `A` a finite alphabet, and `(g.x)(h) = x(g^(-1) h)`.
- `X ⊆ A^Λ` is a nonempty subshift of finite type. Fix a finite symmetric `B ∋ 1` and allowed
  patterns `W ⊆ A^B`, so that `x ∈ X` iff `(k^(-1).x)|_B ∈ W` for every `k ∈ Λ`. Put `B^2 = BB`.
- `Δ(x, y) = {h : x(h) ≠ y(h)}`. A *finite asymptotic pair* is `x ≠ x'` in `X` with `Δ(x, x')`
  finite.
- For a finite `F ⊆ Λ`, `∂F = {p ∈ F : pB^2 ⊄ F}`, and `L_F(X)` is the set of restrictions
  `x|_F` for `x ∈ X`.
- **Condition (NZ).** For every finitely supported `a : Λ -> [0, ∞)` with `a ≠ 0` and every
  nonzero `ν ∈ R[Λ]`, the convolution `a * ν`, `(a*ν)(k) = Σ_g a(g) ν(g^(-1) k)`, is nonzero.

## Theorem

1. **Descent.** If `X` is minimal and `x, x'` is a finite asymptotic pair of `X`, with
   `ν_b(h) = [x(h) = b] - [x'(h) = b]`, then for every finite `L ⊆ Λ` large enough there is a
   nonzero `a : L -> [0, ∞)` with `a * ν_b = 0` for every `b ∈ A`.
2. **No finite asymptotic pairs.** If `Λ` satisfies (NZ) and `X` is minimal, then `X` has no
   finite asymptotic pair.
3. **Boundary determinism.** For any SFT `X` over any group, the following are equivalent:
   (i) `X` has no finite asymptotic pair; (ii) restriction `L_F(X) -> L_(∂F)(X)` is injective for
   every finite `F`. So under (2), `|L_F(X)| <= |A|^|∂F|`; over `Z^d`,
   `log |L_([0,N]^d)(X)| = O(N^(d-1))`.
4. **Groups satisfying (NZ).** Every unique-product group, by a one-line argument. This includes
   every bi-orderable group, with the same proof, and so `Z^d`, free groups, torsion-free
   nilpotent groups, and direct products of these, for example `F_2 x F_2 x Z^2`. Left-orderable
   groups have unique products (standard; context only). A group with an element `t` of finite
   order `n > 1` fails (NZ): `a = 1 + t + ... + t^(n-1)` and `ν = 1 - t`.
5. **Finite index.** If `Λ` is infinite and has a finite-index subgroup satisfying (NZ), part 2
   still holds. This covers `Z^2 x C_2` and every virtually bi-orderable group, torsion
   included. The obstruction of part 1 is therefore not torsion alone: it needs torsion that
   survives in every finite-index subgroup.

## Consequences for the V-times route

- **The finite-asymptotic-pair refutation of P2 is closed over unique-product groups.** The
  necessary condition of `fp-v-times-subshift-full-groups-force-connected-differences` (worker
  bh-break, on the live bus and not yet on main) kills P2 at a minimal free SFT with a finite
  asymptotic pair. By part 2 no such SFT exists over any (NZ) group. A counterexample of that kind
  must use an acting group with a nonnegative zero divisor, for example one with torsion. Part 1
  names the invariant that has to be present.
- **Parts 2 and 3 of both connected-difference theorems are automatic over (NZ) groups.** Over
  such groups the only remaining content of those necessary conditions is part 1: coarse
  connectivity of *infinite* difference sets.
- **Screening Durand--Romashchenko hierarchies over `Z^2`.** Every minimal SFT on `Z^2`
  automatically has no finite asymptotic pairs, has zero entropy, and has at most `e^(O(N))`
  patterns on an `N x N` square. To separate a candidate from P2 one must test two-part splits
  of infinite difference sets, such as a pair of faults bounding a strip.
- **Torsion.** Descent gives nothing over groups with torsion, which can include the input
  `K` of the route. The route may pick `Λ`, but P2 quantifies over all `Λ`, so torsion is where
  a refutation through finite asymptotic pairs has to live.
