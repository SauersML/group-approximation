---
rg: 2
id: mod-s2-instability-via-bielliptic-delocalized-dadarlat
kind: route
title: The bielliptic sector carries rational H^2, so delocalized Dadarlat vanishing refutes matricial stability of Mod(S_2)
target: mod-s2-is-not-point-norm-matricially-stable
requires:
  - weak-matricial-stability-kills-centralizer-even-cohomology
  - dadarlat-matricial-stability-obstruction
  - mod-s2-bielliptic-centralizer-has-rational-h2
  - mod-s2-is-linear
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
artifacts:
  - experiments/mod-s2-bielliptic-sector-2026-09-17/check.py
---

## Why sufficient

Let `M = Mod(S_2)`. Suppose, for a contradiction, that `M` is point-norm matricially stable in the sense of
`mod-s2-is-point-norm-matricially-stable`: every asymptotic homomorphism `V_n : M -> U(d_n)` is pointwise
operator-norm close to honest representations. This is word for word Dadarlat's matricial stability, as quoted in
`dadarlat-matricial-stability-obstruction` §1.

1. **Weak matricial stability.** That claim records that matricial stability implies weak matricial stability, so `M`
   is weakly matricially stable.
2. **`M` is finitely generated and linear.**
   - Finite generation: `genus-two-mapping-class-group-homology-and-symplectic-quotient`, item 1, gives a finite
     presentation.
   - Linearity: `mod-s2-is-linear` embeds `M` in `GL_64(C)`.
   - So the general claim applies to `G = M` with `K = C`.
3. **A finite-order element with an even rational sector.** Take the bielliptic involution `g` of
   `mod-s2-bielliptic-centralizer-has-rational-h2`. It has order 2, and item 2 of that claim gives
   `H^2(Z_M(g);Q) != 0`.
4. **Contradiction.** `weak-matricial-stability-kills-centralizer-even-cohomology`, with `k = 1` and this `g`, gives
   `H^2(Z_M(g);Q) = 0`. This contradicts step 3.

So some asymptotic homomorphism of `M` has no pointwise-close honest representations, which is the target.

## What this route does and does not do

- **Where the one open input sits.** The only open prerequisite is the general vanishing claim. The rest is either
  established here (the bielliptic class) or imported with a verbatim citation (linearity, the Dadarlat notions, the
  finite presentation). So Mod(S_2) is now a *test case* of the general claim, alongside `SL_4(F_q[t^±1])`: a proof of
  the general claim refutes the strong form of `mod-s2-is-point-norm-matricially-stable`.
- **It kills a recorded belief.** Before this, the graph treated the Dadarlat-type obstruction on `M` as absent.
  - `mod-s2-is-point-norm-matricially-stable`, Evidence: "The known cohomological obstruction is absent".
  - The w10 attempts: commuting-twist tests factor through `H_2(M;Q) = 0`.

  That is true in the trivial sector only. In the `(g)`-sector the torus `<T_c, T_c'>` is rationally nonzero.
- **What any witness must look like.**
  - Let `V_n` be a witness, compressed to the two eigenspaces of `V_n(g)`. Granting additivity of the pairing,
    the Bott indices satisfy `beta_{+1} + beta_{-1} = 0`, since the uncompressed pair sees `H_2(M;Q) = 0`.
  - Induced models from a normal finite-index `N` with `g` not in `N` have `beta_{+1} = beta_{-1}`, so both vanish.
  - A witness is therefore non-induced. Constructing one directly is the realization problem (P1)–(P3) of
    `research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md`. It is not attempted here.
- **The weak downstream form is untouched.** `deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability` only uses
  the weaker form, for maps with `V_n(t_s) -> omega I`. This route produces its witness by contradiction, with no
  control on `V_n(t_s)`. So it says nothing about that form, and the flagship route survives provided its node is
  restated in the weak form.
