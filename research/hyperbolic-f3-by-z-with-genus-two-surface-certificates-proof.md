---
rg: 2
id: hyperbolic-f3-by-z-with-genus-two-surface-certificates-proof
kind: route
title: A 16-letter pairing passes every local hypothesis of the legal criterion, and the matrix test makes the mapping torus hyperbolic
target: hyperbolic-f3-by-z-with-genus-two-surface-certificates
requires:
  - legal-f-folded-fatgraphs-give-surface-subgroups
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi1028.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi192.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surfaces_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/unroll_phi1028_n5.log
---

Conventions follow `legal-f-folded-fatgraphs-give-surface-subgroups`. Upper case is inverse.
`f` is the rose map of the positive automorphism `phi`. Standard facts used, not re-read at
source: Bestvina--Handel's classification of fully irreducible non-atoroidal automorphisms;
Brinkmann's theorem (atoroidal implies `F_n x|_phi Z` hyperbolic); free-by-cyclic groups with
`n >= 2` are one-ended.

**Step 1: automorphism.** For `phi_1 = (a -> abb, b -> ca, c -> babb)`:

- `phi_1(cA) = babb BBA = b`;
- `phi_1(aaCaC) = a`;
- `phi_1(bcAcAA) = c`.

So `phi_1` is onto, and `F_3` is Hopfian, so it is an automorphism. For `phi_2` the same
argument gives `psi(b) = cA`, `psi(a) = aaCaC`, `psi(c) = bcAcAAcAA`.
`verify_surface.py` finds these inverses by length-decreasing Nielsen moves and checks
`phi(psi(x)) = psi(phi(x)) = x` by free reduction, for all 24 automorphisms.

**Step 2: hyperbolic.** Let `M` be the transition matrix. Its characteristic polynomial is
`t^3 - t^2 - 5t + 1` for `phi_1` and `t^3 - 2t^2 - 6t + 1` for `phi_2`. Neither has a root
`±1`, so both are irreducible over `Q`, and `M^3 > 0`. Then:

- *Fully irreducible.* Suppose `phi^k` fixes the conjugacy class of a proper free factor.
  Its image in `H_1 = Z^3` is a proper nonzero `M^k`-invariant summand. So `chi_{M^k}` has a
  rational root `mu^k`, where `mu` is a root of `chi_M`. That root is an algebraic integer
  unit, so `mu^k = ±1`. Every Galois conjugate of `mu` then has modulus 1, which contradicts the
  Perron--Frobenius root `> 1`.
- *Atoroidal.* A fully irreducible non-atoroidal automorphism of `F_3` comes from a
  pseudo-Anosov map of a compact surface with one boundary component and `pi_1 = F_3`. That
  surface is `N_{3,1}`, since orientable surfaces with one boundary component have even rank.
  Its boundary class `2(x + y + z) ≠ 0` in some basis is fixed by `M` up to sign, so `±1` is an
  eigenvalue of `M`, which is false.

By Brinkmann, `F_3 x|_phi Z` is hyperbolic. The 22 relabelled or reversed variants have
isomorphic mapping tori, and the checker re-verifies the matrix test for each of them anyway.

**Step 3: the fatgraph.** The certificate file gives:

- `phi0`, `power = 1`;
- the `partial^-` words `w, w^-1` (for `phi_1`, `w = bc`);
- a pairing `p` of the boundary letters.

`verify_surface.py` imports nothing from the search code. It rebuilds everything else:

- the four boundary circles `w`, `f(w)^-1`, `w^-1`, `f(w^-1)^-1` and their darts;
- the face permutation `nxt`;
- the vertex permutation `sigma = nxt o p`. A fatgraph is given by an edge involution and a
  vertex rotation, and its boundary cycles are the orbits of `sigma o p = nxt`. So `S(X)` has
  exactly these boundary circles.

It then checks:

1. `p` is a fixed-point-free involution with `label(p d) = label(d)^-1`. So `X` has 8 edges
   (10 for `phi_2`), each carrying a letter, and `g: X -> R` is defined.
2. Every boundary word is cyclically reduced. So `partial^+` reads `f(partial^-)` without
   cancellation, as an `f`-fatgraph requires.
3. **(L).** At every vertex the outgoing letters lie in pairwise distinct gates. Gates are
   computed from `Df(x) = F(f(x))` and `Df(X) = L(f(x))^-1`, with `d ~ d'` iff
   `Df^j d = Df^j d'` for some `j <= 24`. With 6 directions, `j <= 6` suffices. For `phi_1`
   and `phi_2` the gates are `{a}, {b}, {c}, {A, C}, {B}`, since `Df = (a->a, b->c, c->b,
   A->B, B->A, C->B)`. Distinct gates give distinct letters, so `X -> R` is an immersion.
4. **(2), (3).** The *`f`-corners* are the corners of `partial^+` between two blocks
   `f(x)^-1`, including the cyclic wrap-around. There are 4 of them. Each vertex carries at
   most one, and a vertex carrying one is 2-valent.
5. **(4).** No edge has `partial^-` on both sides, and no vertex carries two `partial^-`
   corners. So `partial^- -> X` is an embedding.
6. `X` is connected and `chi(X) = V - E = 6 - 8 = -2` (`8 - 10` for `phi_2`).

Outputs are in `verify_surfaces_m1.log` (24 × `CERTIFICATE OK`).

Two cross-checks:

- `sat4.verify4`, independent code, passes the same pairings.
- It also builds the stacked graphs `X_n` and confirms `X_n -> R` immerses for `n <= 5` for
  `phi_1` (`unroll_phi1028_n5.log`), as the criterion's proof predicts.

**Step 4: conclusion.** `phi` is a positive automorphism, so it satisfies (TT). By Step 3, `X`
is an `f`-fatgraph with (L), (2), (3), (4). By `legal-f-folded-fatgraphs-give-surface-subgroups`,
`S*_f(X) -> K` is `pi_1`-injective. Gluing boundary circles in pairs with opposite orientations
gives a closed orientable surface. It is connected because `X` is, and
`chi(S*_f(X)) = chi(X) = -2`. So its genus is 2, and `pi_1(S_2)` embeds in `F_3 x|_phi Z`.
That group is one-ended and hyperbolic by Step 2. `QED`

**How the certificates were found (not needed for the proof).**

- `lp_allwords.py` sets up a word-free relaxation of the certificate LP over all boundaries,
  for the 6420 automorphisms of `phi_scan4.json`. The census is still running; the partial log
  has 24 entries with optimum `-1/2`.
- For each of them, `surface_batch.py` tried `partial^- = {w, w^-1}` over legal words of length
  2 and asked the SAT model `sat4.solve4` for a pairing. Every entry succeeded at the first
  length.
