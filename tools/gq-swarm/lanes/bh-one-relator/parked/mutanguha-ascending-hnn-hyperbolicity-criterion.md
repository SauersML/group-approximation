---
rg: 2
id: mutanguha-ascending-hnn-hyperbolicity-criterion
kind: claim
title: Mutanguha -- an ascending HNN extension of a finitely generated free group is word-hyperbolic exactly when it has no BS(1,d) subgroup, and the Sapir group F(a,b)*_(a->ab, b->ba) is word-hyperbolic
distinct_from:
  ascending-hnn-extensions-of-free-groups-contain-no-z-localized: that excludes one subgroup, Z_(l), from every ascending HNN extension of a free group; this is the hyperbolicity criterion for those groups.
  hyperbolic-groups-satisfy-boone-higman: that is the Boone--Higman theorem for hyperbolic inputs; this imports the theorem that identifies which ascending HNN extensions of free groups are hyperbolic inputs.
---

**ESTABLISHED (literature import).** Both statements were read from the TeX e-prints,
fetched through MSI (`gqsrc/bh-one-relator/`).

1. **J. P. Mutanguha, *The dynamics and geometry of free group endomorphisms*,
   arXiv:2005.11896v2 (Adv. Math. 384 (2021) 107714), Theorem `main`.** Let `φ : F → F`
   be an injective endomorphism of a finitely generated free group. Then the following
   are equivalent:
   1. `F*_φ` is word-hyperbolic;
   2. `F*_φ` contains no `BS(1,d)` subgroups with `d ≥ 1`;
   3. `[φ]` has no invariant cyclic subgroup system with index `d ≥ 1`;
   4. all/some topological representatives of `[φ]` are based-hyperbolic and all strictly
      bidirectional annuli in their mapping tori are shorter than some integer.

   Here `BS(1,1) = Z^2` is included. The paper's standing convention (its §2, line 218 of
   the TeX) is: "`F` will always be a free group with finite rank at least `2`." For rank
   `1`, `F*_φ = BS(1,m)` with `m = φ(1) ≠ 0`, which always contains a `BS(1,d)` and is never
   hyperbolic, so the equivalence of items 1 and 2 holds for every finite rank. The paper's
   Main Theorem also covers HNN extensions `F*_A` over a free factor `A`, which are not used
   here.
2. **J. P. Mutanguha, *Irreducible nonsurjective endomorphisms of F_n are hyperbolic*,
   arXiv:1908.08214v3 (Bull. Lond. Math. Soc. 52 (2020) 960–976).**
   - *Theorem `hypthm`:* "If `φ:F → F` is represented by a clean immersion, then `F*_φ` is
     word-hyperbolic. In particular, if `φ` is nonsurjective and irreducible, then `F*_φ`
     is word-hyperbolic."
   - *Example `sapir`:* for `F = F(a,b)` and the nonsurjective endomorphism
     `φ(a) = ab`, `φ(b) = ba`, the Sapir group `F*_φ = ⟨a, b, t | t^{-1}at = ab, t^{-1}bt = ba⟩`
     is word-hyperbolic.
   - *Contrast in the same example:* `ψ(a) = aba`, `ψ(b) = bab` has `ψ(ab) = (ab)^3`, so
     `BS(1,3) ≤ F*_ψ`, and `F*_ψ` is not hyperbolic.
   - *Definition used for "irreducible":* `φ` is reducible if there are a free factorization
     `A_1 * ⋯ * A_k * B` of `F` (with `B ≠ 1` if `k = 1`) and elements `g_i` with
     `φ(A_i) ≤ g_i A_{i+1} g_i^{-1}`, indices mod `k`.

**Convention.** Mutanguha writes `t^{-1} x t = φ(x)`, and this graph writes
`t x t^{-1} = φ(x)` (for example `power-map-free-mapping-tori-satisfy-permutational-boone-higman`).
The two presentations define isomorphic groups via `t ↦ t^{-1}`.

**Not read.** The companion papers (arXiv:1809.04761, Theorem 6.3; Reynolds) that the
proofs cite. Only the statements above are imported.
