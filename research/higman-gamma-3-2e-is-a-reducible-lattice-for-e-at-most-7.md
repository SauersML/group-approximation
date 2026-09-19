---
rg: 2
id: higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7
kind: claim
title: For every e >= 3 both tree kernels of Gamma(3,2^e) are infinite and contain b^(m/4); for e <= 7 Gamma(3,2^e) is a reducible lattice; the resulting reduction of ord(a) in Gamma(3,2^e)/<<[a,c]^2>> to an explicit 2-generator group is certified for e <= 6 and provably fails for every e >= 9
distinct_from:
  higman-torsion-generator-quotients-factor-through-tree-lattices: that builds Gamma(n,m) as a uniform lattice in Aut(T_m) x Aut(T_m) and leaves its reducibility open; this computes the two tree kernels, proves they are infinite for every m = 2^e >= 8, and proves that the lattice is reducible (virtually F x F) for e <= 7.
  higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz: that refutes the A-splitting Freiheitssatz and proposes the B-splitting one; this shows that the B-tree action cannot certify it (L1 never embeds in Gamma/Lambda_B), and replaces it by the quotient Q_B = Gamma/Lambda_B, in which A does embed and ord(a) reduces to an explicit finitely presented group.
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that leaves open whether H4(3)/<<[a,c]^2>> has generators of infinite order; this does not settle that, but proves ord(a) = 2^e for e = 3..6 in Gamma(3,2^e)/<<[a,c]^2>> by a route independent of the 2-quotient tower, and names the uniform statement that would give infinitely many e.
artifacts:
  - experiments/higman-b-splitting-2026-09-18/pathstab.py
  - experiments/higman-b-splitting-2026-09-18/ball.py
  - experiments/higman-b-splitting-2026-09-18/d1.g
  - experiments/higman-b-splitting-2026-09-18/d1-output.txt
  - experiments/higman-b-splitting-2026-09-18/d3.g
  - experiments/higman-b-splitting-2026-09-18/d3-output.txt
  - experiments/higman-b-splitting-2026-09-18/enum.g
  - experiments/higman-b-splitting-2026-09-18/twists.py
  - experiments/higman-b-splitting-2026-09-18/twists.g
  - experiments/higman-b-splitting-2026-09-18/twists-e3-output.txt
  - experiments/higman-b-splitting-2026-09-18/twists-e4-output.txt
  - experiments/higman-b-splitting-2026-09-18/twists-e5-output.txt
  - experiments/higman-b-splitting-2026-09-18/twists-e6-output.txt
  - experiments/higman-b-splitting-2026-09-18/qbar.g
  - experiments/higman-b-splitting-2026-09-18/qbar-e3-output.txt
  - experiments/higman-b-splitting-2026-09-18/qbar-e4-output.txt
  - experiments/higman-b-splitting-2026-09-18/coset.g
  - experiments/higman-b-splitting-2026-09-18/coset-e6-output.txt
  - experiments/higman-b-splitting-2026-09-18/hfail.py
  - experiments/higman-b-splitting-2026-09-18/hfail-output.txt
  - experiments/higman-b-splitting-2026-09-18/anti.py
  - experiments/higman-b-splitting-2026-09-18/anti2.py
  - experiments/higman-b-splitting-2026-09-18/a7.out
  - experiments/higman-b-splitting-2026-09-18/a7b.out
---

**ESTABLISHED** (proposed) by `higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7-proof`.
- Items 1 and 3 are proved by hand for every `e >= 3`.
- Item 2 is proved by hand from one finite computation per `e`: the orders of two permutation
  groups, in `d1.g` and `d3.g`.
- Item 4 is a certified finite computation for `e = 3..6`: `enum.g`, `twists.py` and `twists.g`.
- Item 5 is proved by hand from item 4 of
  `higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz`. `hfail.py` exhibits an explicit
  failing `beta` at `e = 9`.

**Setting.**
- `m = 2^e` with `e >= 3`, `t = 3^-1 mod m`, and `Gamma = Gamma_e = Gamma(3,m) = H4(3)/<<a^m,b^m,c^m,d^m>>`.
- These facts are from `higman-torsion-generator-quotients-factor-through-tree-lattices`:
  - **A-splitting:** `Gamma = K1 *_A K2`, with `A = <a,c> = Z/m * Z/m`.
  - **B-splitting:** `Gamma = L1 *_B L2`, with `L1 = <d,a,b>`, `L2 = <b,c,d>` and
    `B = <b,d> = Z/m * Z/m`.
  - `Gamma` acts properly and cocompactly on `T_A x T_B`, where `T_A`, `T_B` are the two
    `m`-regular Bass–Serre trees.
- **Exact factorization.** `Gamma = A · B` with `A ∩ B = 1`, and `L1 = <a> · B`. This is proved in
  the proof node, section 0.
- **Tree kernels.** `Lambda_B` is the kernel of the action on `T_B`, and `Lambda_A` is the kernel of
  the action on `T_A`. Then `Lambda_B <= B` and `Lambda_A <= A`, both normal in `Gamma`. Write
  `Bbar = B/Lambda_B`.
- **Symmetry.** `sigma: a -> b -> c -> d -> a` is an automorphism of `Gamma`. It carries the
  A-splitting to the B-splitting, so `Lambda_A = sigma^-1(Lambda_B)`. `sigma^2` swaps `a <-> c` and
  `b <-> d`.
- **Relator.** `R = [a,c]^2`, `Gammabar_e = Gamma_e/<<R>>`, and `Q_B = Gamma/Lambda_B`.

**Statement.**
1. **Torsion in both kernels, every e >= 3.**
   - `b^(m/4)` and `d^(m/4)` lie in `Lambda_B`: they fix every edge of `T_B`.
   - `a^(m/4)` and `c^(m/4)` lie in `Lambda_A`.
   - `Lambda_A` and `Lambda_B` are infinite, and `Lambda_A ∩ Lambda_B = 1`.
   - `Lambda_A Lambda_B = Lambda_A x Lambda_B` is normal in `Gamma`, and
     `Gamma/(Lambda_A x Lambda_B)` is in bijection with `A/Lambda_A x B/Lambda_B`.
   - `b^(m/4)` commutes with `c`, and `a^-1 b^(m/4) a = b^(-m/4)`.
   - Consequently `L1 -> Q_B` is never injective: its kernel `Lambda_B` contains `b^(m/4)`.
     So the B-splitting Freiheitssatz (`L1` embeds in `Gammabar_e`) cannot be proved by passing to
     the faithful quotient `Q_B` of the B-tree action. By contrast, `A` does embed in `Q_B`,
     because `A ∩ B = 1`, and this is what item 3 uses.
2. **Reducibility for e <= 7.** Let `r = 2` for `e <= 6` and `r = 3` for `e = 7`. Then:
   - `Lambda_B` is exactly the pointwise stabilizer in `B` of the ball of radius `r` about the base
     vertex of `T_B`.
   - The indices are:

     | e | `[B : Lambda_B]` | `[L1 : Lambda_B]` | `Bbar` |
     |---|---|---|---|
     | 3 | `2^2` | `2^5` | `(Z/2)^2` |
     | 4 | `2^4` | `2^8` | `(Z/4)^2` |
     | 5 | `2^6` | `2^11` | `(Z/8)^2` |
     | 6 | `2^9` | `2^15` | nonabelian, `b` and `d` of order 16 |
     | 7 | `2^13` | `2^20` | nonabelian, `b` and `d` of order 32 |

   - Hence `Lambda_A x Lambda_B` has index `[B:Lambda_B]^2` in `Gamma_e`. Each factor is a
     finite-index subgroup of `Z/m * Z/m`, so it is virtually free of rank at least 2.
   - `Gamma_e` is commensurable with `F_p x F_q` for some `p, q >= 2`: it is a **reducible** lattice
     in `Aut(T_m) x Aut(T_m)`, and both projections are discrete.
   - Reducibility is inherited downward: if `Gamma_e` is reducible, then so is `Gamma_(e')` for
     every `e' <= e`, since `Gamma_e` maps onto `Gamma_(e')` compatibly with the trees.
3. **Reduction lemma, every e.**
   - For `beta in B`, write `beta R beta^-1 = S_beta · beta''` with `S_beta in A` and `beta'' in B`,
     using the exact factorization. The word `S_beta` is computed syllable by syllable, and has
     syllable length at most 8.
   - **Hypothesis (H_e):** `beta'' in Lambda_B` for every `beta in B`. Under (H_e):
     - the normal closure of `R` in `Q_B` is `<< S_beta : beta in Bbar >>_A`, which lies in `A`;
     - `Abar_e := < a, c | a^m, c^m, S_beta (beta in Bbar) >` embeds in
       `Qbar_B = Q_B/<<R>>` with index `|Bbar|`;
     - `Gammabar_e` maps onto `Qbar_B`, so `ord(a in Gammabar_e) >= ord(a in Abar_e)`.
   - `beta = b^(±1)` and `beta = d^(±1)` always satisfy `beta'' = 1`. For `b^(±1)` this is the twist
     identity of `higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz`, and `d^(±1)` follows
     by `sigma^2`.
4. **Certificates for e = 3..6.**
   - (H_e) holds: all `|Bbar|` elements `beta''` are trivial in a faithful permutation model of
     `Bbar`.
   - `Abar_e` has exactly `|Bbar|` distinct twisted relators, up to rotation and inversion.
   - `Abar_e` has a finite 2-quotient in which `a` has order `2^e`, and every relator is re-checked in
     that quotient:

     | e | class | order |
     |---|---|---|
     | 3 | 3 | `2^9` |
     | 4 | 4 | `2^14` |
     | 5 | 7 | `2^47` |
     | 6 | 9 | `2^114` |

   - Hence `ord(a) = 2^e` in `Gammabar_e` for `e = 3..6`.
   - The lower bound is already known from the 2-quotient tower. This proof is independent: the
     index-`|Bbar|` subgroup `Abar_e` of `Qbar_B` is 2-generated, with relators of syllable length at
     most 8.

5. **Obstruction: (H_e) fails for every e >= 9.**
   - Under (H_e), `Qbar_B = Abar_e · Bbar` exactly, with `Bbar` embedded.
   - By `higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz` item 4, for `e >= 7`,
     `b^(64v)` lies in `Abar` in `Gammabar_e`, and hence in `Qbar_B`, for some odd `v`.
   - Exactness then forces `b^(64v)` into `Lambda_B`. But `b^q` lies in `Lambda_B` only if
     `m/4 | q`, because `b^q` sends the vertex `c L1` to `c^(t^q) L1`, and `t` has order `m/4`.
   - So `m/4 | 64`, which means `e <= 8`.
   - Explicitly, at `e = 9` the element `beta = b d` has `beta'' = b^320`, and `b^320` moves `c L1`.
     At `e = 10` it has `beta'' = b^832`, which also moves `c L1`. At `e = 7, 8` the same `beta` has
     `beta'' = b^64`, which lies in `Lambda_B`. All of this is in `hfail-output.txt`.
   - Hence for `e >= 9`, `<<R>>_{Q_B}` is not contained in `A`, and the reduction of item 3 is
     unavailable. The Q_B route to `ord(a) = 2^e` for infinitely many `e` must treat
     `<<R>>_{Q_B} ∩ B-part != 1`, exactly as the A-splitting route had to treat `d^64 in Abar`.

**What this does to the target question.**
- The target question needs `ord(a) = 2^e` in `Gammabar_e` for infinitely many `e`.
- Item 1 closes one route. The B-splitting Freiheitssatz cannot be reached through `Q_B`, the
  quotient on which `Gamma` acts faithfully on `T_B`.
- Items 3 and 5 settle the other route. The alternative (growth of `ord(a)` through `Q_B`) has a
  clean form, `Abar_e` of index `|Bbar|` in `Qbar_B`. That form exists for `e <= 6` and is
  impossible for every `e >= 9`. For `e = 7, 8` it is open: the test element `b d` passes, with
  `beta'' = b^64` in `Lambda_B`, but the full check over `Bbar` (`2^13` elements at `e = 7`) was
  cut off by a container restart.
- So neither route of the brief can give infinitely many `e` through the tree action alone.
- **What remains** is the quotient `Qbar_B` itself, where `<<R>>` now meets the `B`-part. The
  relation to exploit is item 5's: `b^(64v) · alpha in <<R>>_{Q_B}` for some `alpha in A`. It is
  the B-side mirror of `d^64 in Abar`. Two concrete next steps:
  - **(i)** Decide whether `Gamma_e` is reducible for all `e`. The first unknown case is `e = 8`.
    Observed stabilization radius: `r = 2` for `e <= 6` and `r = 3` for `e = 7`. `[B:Lambda_B]`
    is `2^(2e-4)` for `e <= 5`, then `2^9` and `2^13`. If `Gamma_e` is irreducible for large `e`,
    then `Q_B` is not virtually `A`, and the tree-kernel method stops.
  - **(ii)** For `e >= 9`, describe `M = <<R>>_{Q_B}`. By item 5 it is not contained in `A`: it
    contains `S_beta · beta''` with `beta'' notin Lambda_B`, for example `beta = b d` at `e = 9`.
    Look for a subgroup `H = A · Bbar_0` of `Q_B`, with `Bbar_0 <= Bbar`, that contains `M`, and
    present `H/M` the way item 3 presents `Abar_e`.
- For `e <= 6`, `Abar_e` is a 2-generated quotient of `Z/m * Z/m` by `|Bbar|` relators, each of
  syllable length at most 8. For `e <= 5`, `Bbar = (Z/(m/4))^2` is indexed by `b^i d^j`, and the
  relators form an explicit two-parameter family `S_(i,j)`.

**Dead ends recorded here.**
- **Irreducibility via infinite-order sections.** This approach tried to show that `Bbar` is
  infinite, via an element of `B` whose section at a vertex of even depth is conjugate to itself
  after a nontrivial orbit (`anti.py` and `anti2.py`). It found no certificate at `e = 4, 6, 7`
  (`a7.out`, `a7b.out`), and item 2 shows that none exists for `e <= 7`.
- **GAP Reidemeister–Schreier.** Presentations of `<a,c> <= Qbar_B` obtained this way were
  inconsistent with the certified 2-quotients (one of them made `c` trivial). They are not used.
  Item 4 builds the presentation of `Abar_e` directly from the exact factorization instead.
- `qbar.g` and `coset.g` are corroboration only. They present `Lbar_1` from a permutation group,
  so they are not load-bearing.
  - `qbar.g`: 2-quotients of `Qbar_B` itself reach `ord(a) = 2^e` with `ord(b) = 2^(e-2)`, and keep
    growing up to class 12.
  - `coset.g`: `[Qbar_B : Abar] = |Bbar|` at `e = 3..6`.

## Attempts

- w13-053 (2026-09-18): computed the kernels of the B-tree action. Items 1 to 4 above;
  proof in `higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7-proof`.
