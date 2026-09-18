---
rg: 2
id: torus-degree-regular-on-prime-power-residual-support-proof
kind: route
title: Reduce to the support subgroup, detect kernel vectors mod p in a p-group quotient where the augmentation ideal is nilpotent, and build the Bezout zero divisor otherwise
target: torus-degree-regular-on-prime-power-residual-support
requires:
  - torus-automata-over-rf-or-domain-groups-are-surjunctive
  - torus-automata-with-regular-degree-are-surjective
artifacts:
  - research/artifacts/torus-degree-prime-power-support-2026-09-17.md
  - experiments/torus-prime-power-2026-09-17/check_prime_power_dichotomy.py
---

Artifact Sections 1–3.

1. **Constants.** The periodic-point lemma of
   `torus-automata-over-rf-or-domain-groups-are-surjunctive` with `N = G` gives
   `epsilon(D) in GL_d(Z)` for every injective `tau` over every group.
2. **Support subgroup (Lemma 1).** `Q[G]^d` is the direct sum of the `r Q[H]^d` over a
   left transversal `r`. Right multiplication by `D in M_d(Z[H])` preserves each summand.
   So injectivity on `Q[H]^d` gives injectivity on `Q[G]^d`.
3. **Nilpotence (Lemma 2, Corollary 3).** Over a finite `p`-group `P`, the augmentation
   ideal of `F_p[P]` is nilpotent: induct through a central `z` of order `p`, using
   `(z - 1)^p = 0`. So `E in M_d(F_p[P])` with `epsilon(E)` invertible is invertible.
4. **Detection (Theorem 4).** Take `0 != v in Z[H]^d` with `v D = 0`.
   - Take a `p`-group quotient `P` injective on `supp v`, and divide `v` by the largest
     power of `p`.
   - Its image in `F_p[P]^d` is then nonzero and killed by an invertible matrix.
   - This contradiction gives regularity. Step 2 and
     `torus-automata-with-regular-degree-are-surjective` give surjectivity.
5. **Sharpness (Proposition 6).** In `Q[K]`, the left ideals killed by `e_s` and by `e_t`
   have dimensions `|K|(1 - 1/p)` and `|K|(1 - 1/q)`. They intersect nontrivially because
   `1/p + 1/q < 1`, and any `xi` in the intersection kills `a P_s + b P_t`.
6. **Check.** The experiment verifies (b) exactly over `Q` for `Z/6, Z/10, Z/15, S_3, A_4,
   S_4`. It verifies (a) on 200 random degree matrices over five small `p`-groups.
