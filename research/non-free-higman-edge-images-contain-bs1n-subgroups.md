---
rg: 2
id: non-free-higman-edge-images-contain-bs1n-subgroups
kind: claim
title: In every quotient of a base-n Higman group a non-free edge image with infinite-order generators contains two copies of BS(1,n), so it has no faithful action of subexponential orbit growth; this rules out topological full groups, IET groups, wobbling groups and groups of subexponential growth as hosts for question (a)
distinct_from:
  higman-edge-closure-absorbs-b-powers: that puts powers of b and d into the finite or profinite closure of the edge group; this puts them into the edge group itself, in the discrete quotient, with an explicit exponent, and deduces BS(1,n) subgroups and a host obstruction that no closure statement gives.
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that proves the dichotomy (free, or finite abelianization) and asks question (a); this uses the dichotomy as input and removes every host of subexponential orbit growth from question (a).
  subexponential-schreier-growth-excludes-sl3z-and-bs1k: that excludes BS(1,k) subgroups from groups with a faithful action of subexponential orbit growth; this is used as input, and the new content is that non-free Higman edge images contain BS(1,n) at all.
  nontrivial-higman-quotients-have-tower-distorted-generators: that forces tower distortion of the generators of a nontrivial quotient of H4; tower distortion is compatible with every finitely generated host, while this gives an exponential lower bound on orbit growth inside the edge image alone.
  higman-group-embeds-in-no-almost-automorphism-group: that is an embedding obstruction for the whole group in one host family; this is an obstruction for the two-generator edge image in every host of subexponential orbit growth, in every base.
artifacts:
  - experiments/higman-diagonal-pro2-2026-09-18/b_pair_free.g
  - experiments/higman-diagonal-pro2-2026-09-18/b_pair_free-output.txt
  - experiments/higman-diagonal-pro2-2026-09-18/diag_tower.g
  - experiments/higman-diagonal-pro2-2026-09-18/diag_tower-output.txt
---

**ESTABLISHED** (proposed) by `non-free-higman-edge-images-contain-bs1n-subgroups-proof`
(direct elementary proof, 2026-09-18; not yet refereed).

**Setting.** `H4(n) = < a, b, c, d | b^a = b^n, c^b = c^n, d^c = d^n, a^d = a^n >` with `n >= 2` and
`x^y = y^-1 x y`, so `H4 = H4(2)` is Higman's group. For a quotient `Q` write `A = <a, c>`,
`B = <b, d>`, `A_M = <a^M, c^M>` and `B_M = <b^M, d^M>`. For a word `w` in `a, c`, `e_a(w)` and
`e_c(w)` are its exponent sums. `BS(1,n) = < x, t | t^-1 x t = x^n >`.

**Statement.** Let `Q` be any quotient of `H4(n)`.

1. **Discrete absorption.** Let `w` be a word in `a, c` with `w = 1` in `Q` and `Y = e_a(w) != 0`.
   Let `N >= 0` be such that `N + e_a(u) >= 1` for every prefix `u` of `w` that is followed by a
   letter `a^-1`. Then `b^(n^N (n^|Y| - 1))` lies in `A` (if `Y > 0`), resp.
   `b^(n^(N+Y) (n^|Y| - 1))` lies in `A` (if `Y < 0`). If `w` is a word in `a^M, c^M`, the element
   lies in `A_M`. The same holds with `(a, b)` replaced by `(c, d)` and `e_a` by `e_c`, and, by the
   cyclic automorphism `a -> b -> c -> d -> a`, for the pair `B` absorbing powers of `c` and `a`.
   This holds in `Q` itself, not only in its finite images.
2. **Non-free edge images absorb b and d.** If `A` is not free on `a, c`, there are `m, m' >= 1` with
   `b^m, d^m'` in `A`. Then `(a, b^m, c, d^m')` satisfies the Higman relations with bases
   `(n, n^m, n, n^m')`, so `A` is a quotient of the mixed-base group `H(n, n^m, n, n^m')` generated
   by the images of its first and third generators.
3. **BS(1,n) subgroups.** If moreover `b` has infinite order, then `<a, b^m>` and `<c, d^m'>` are
   subgroups of `A` isomorphic to `BS(1,n)`. By the target's Lemma 3.1 (torsion goes around the
   cycle), `b` has infinite order as soon as any of `a, b, c, d` does.
4. **Host obstruction.** Hence a non-free edge image `A` with infinite-order generators has no
   faithful action of subexponential orbit growth (in the sense of
   `subexponential-schreier-growth-excludes-sl3z-and-bs1k`). In particular `A` is not isomorphic to
   a subgroup of any of the following:
   - a group of subexponential word growth (Grigorchuk-type groups included);
   - a topological full group `[[X, T]]` of any action of `Z^d` on a compact space (every `[[T]]` of
     a minimal Cantor system included, the Juschenko–Monod amenable, non-elementary-amenable groups);
   - the interval exchange group `IET`, or any group of piecewise translations of an interval;
   - the wobbling group `W(Γ)` of a connected bounded-degree graph `Γ` of subexponential growth
     (so `W(Z^d)` and every subgroup of it).
5. **Whole-group version (the orbit-count spark).** Let `G` have a faithful action of subexponential
   orbit growth, and let `phi : H4(n) -> G` be a homomorphism. Then `phi(a), ..., phi(d)` all have
   finite order. For `n = 2`, `phi` is trivial.
6. **Amenable edge images (one-directional reduction).** Suppose `A` is amenable and not free, and
   `b` has infinite order. Put `L = lcm(m, m')`. Then `C = B_L` lies in `A ∩ B`, it contains powers
   `a^k'` and `c^k` (`k, k' >= 1`), and it equals `<a^k', b^L, c^k, d^L>`. So `C` is an amenable
   quotient of the mixed-base group `H(n^k', n^L, n^k, n^L)` with four infinite-order generators, and
   it is generated by its second and fourth generators `b^L, d^L` alone. So a positive answer to (a)
   yields an amenable, doubly power-perfect quotient of a mixed-power-base Higman group sitting in
   `A ∩ B`. The converse is not claimed.

**What it kills.** Question (a) of `higman-power-pair-collapse-is-base-uniform-up-to-torsion` asks
for an amenable power-perfect edge image with infinite-order generators in an odd base. The two
standard sources of amenable groups that are not elementary amenable (and so escape item 2 there)
are topological full groups of minimal Cantor systems and groups of intermediate growth. Item 4 kills
both, together with every subgroup of `IET` and of `W(Z^d)`. It also covers non-amenable hosts of
subexponential orbit growth, such as the Elek–Monod topological full group of a `Z^2`-action. So the
w9-053 dead end "topological full groups of minimal Z-systems" becomes a theorem for every `Z^d` and
every host of subexponential orbit growth. It dies at one step: the edge image contains
`<a, b^m> ≅ BS(1,n)`, and `b^m` has only logarithmic word length in `a, b^m` (Horner's rule). For
`n = 2`, combining with `nontrivial-higman-quotients-have-tower-distorted-generators` gives: **in
every nontrivial quotient of Higman's group, the edge image `<a, c>` is free or contains the two
subgroups `<a, b^m> ≅ <c, d^m'> ≅ BS(1,2)`.** A counterexample to (a), and any amenable
edge image in a nontrivial quotient of `H4`, must have exponential orbit growth in every faithful
action. The candidate hosts that remain are groups of exponential activity, for example
automaton groups such as bounded-automaton or Basilica-type groups, which may contain `BS(1,n)`.

**Calibration.**
- `D_oo x D_oo` in odd base: `b^2 = 1`, so item 3 does not apply. That is consistent, since this `A`
  is virtually cyclic and acts on `Z`.
- `(Z/(n-1))^4`: all generators are torsion. That is consistent.
- `H4(3)/<<[a,c]^2>>`, universal pro-2 quotients `G_k`, classes 1 to 8
  (`experiments/higman-diagonal-pro2-2026-09-18/b_pair_free.g`):
  - `log2|B_k| = 2, 5, 10, 18, 32, 55, 94, 161` against the free pro-2 values
    `2, 5, 10, 18, 32, 55, 96, 167`, so the pro-2 closure of `B` is not free pro-2 from class 7
    on. That does not show that the discrete `B` is not free;
  - `B_k^ab = (Z/64)^2` at classes 6 to 9, but `Z/64 x Z/128` at class 10
    (`experiments/higman-diagonal-pro2-2026-09-18/diag_tower.g`, classes 1 to 11), so the pro-2 abelianization of `B` is not
    known to stabilize;
  - `A_k ∩ B_k = 1` through class 8, which is consistent with item 1 only because `b^64 = 1` there.
    The absorbed power `b^(2^6)` (with `2^6 || 3^16 - 1`) is trivial until `ord(b) > 64`. So a
    residually-2 image of this group with `b` of infinite order must have `A_k ∩ B_k != 1` from
    some class on. That is the finite shadow of item 1 (`b^m ∈ A`);
  - item 6 predicts that an amenable candidate is doubly power-perfect, with both `A^ab` and
    `B_L^ab` finite. For this group `A_k^ab = (Z/16)^2` is stable from class 4, while the `B`-side
    is undecided by the data. This is evidence only, since the finite groups `G_k` are all
    amenable.
