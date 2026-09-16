---
rg: 2
id: rr0-separativity-from-prime-case-and-k1-bijectivity
kind: route
title: Under Zhang's conjecture a critical quotient of a separativity failure is prime, so the prime case suffices
target: rr0-c-star-algebras-are-separative
requires: [prime-rr0-algebras-are-separative, rr0-algebras-are-k1-bijective]
artifacts:
  - research/artifacts/rr0-separativity-prime-reduction-2026-09-16.md
---

Full proof in the artifact.  Outline:

1. **Normal form** (Section 1).  A failure `p (+) p ~ p (+) q ~ q (+) q`,
   `p` not equivalent to `q`, over `M_n(A)` gives the unital real rank zero
   corner `B = (p (+) q) M_(2n)(A) (p (+) q)` with `1 = P + Q`,
   `P (+) P ~ Q (+) P ~ Q (+) Q` in `M_2(B)`, `P` not equivalent to `Q`, and `Q`
   full.
2. **Critical quotient** (Section 2).  The ideals `J` with `P` not equivalent to
   `Q` modulo `J` are closed under closures of increasing unions: an
   equivalence modulo the closure is approximated at a finite stage and
   corrected by polar decomposition.  Zorn gives a maximal one, and
   `B' = B/J_0` has `P ~ Q` modulo every nonzero ideal.
3. **Primeness** (Section 3).  If nonzero ideals `K_1, K_2` of `B'` meet in
   `0`, `B'` is the pullback of `B'/K_1` and `B'/K_2` over `D = B'/(K_1 + K_2)`.
   Partial isometries `v_i` from `P` to `Q` on the two sides differ in `D` by a
   unitary `w~` of `Q~ D Q~`.  The witness `W` of `P (+) P ~ Q (+) P` makes the
   unitaries `Z_i = W_i (v_i* (+) P_i)` satisfy
   `rho_2(Z_2)* rho_1(Z_1) = w~ (+) P~`.  Full-corner invariance of `K_1`
   (proved in the artifact) turns this into
   `[w~] = rho_1* x_1 - rho_2* x_2` with `x_i` in `K_1(Q_i B_i Q_i)`.
   K1-surjectivity of the corners `Q_i B_i Q_i` realizes `x_i` by unitaries
   `u_i`, and K1-injectivity of `Q~ D Q~` puts
   `rho_2(u_2)* rho_1(u_1) w~*` in the identity component.  That component lifts
   to `Q_2 B_2 Q_2`, so after correcting `u_2` the partial isometries `u_i v_i`
   agree in `D` and glue to `P ~ Q` in `B'`, a contradiction.
4. **Conclusion** (Section 4).  `B'` is a unital prime real rank zero algebra
   with `2[P] = [P] + [Q] = 2[Q]` and `[P] != [Q]`, contradicting
   `prime-rr0-algebras-are-separative`.

Standard inputs used without proof: real rank zero passes to matrix algebras
and corners (Brown--Pedersen 1991), and closed ideal arithmetic
(`K_1 + K_2` closed, `K_1 ∩ K_2 = K_1 K_2`).  Everything else, including
full-corner invariance of `K_1` and lifting of the identity component of the
unitary group, is proved in the artifact.

With `rr0-k1-bijectivity-via-separativity`, separativity of all real rank zero
algebras is equivalent to Zhang's conjecture together with the prime case.
With `stw99-lx-via-rr0-separativity` and `rr0-separativity-via-lx`, the same
holds for Problem LX.
