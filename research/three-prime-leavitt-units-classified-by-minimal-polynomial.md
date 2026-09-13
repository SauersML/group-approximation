---
rg: 2
id: three-prime-leavitt-units-classified-by-minimal-polynomial
kind: claim
title: Units of finite order prime to three in the ternary Leavitt unit group are conjugate iff they have the same minimal polynomial, and lie in the signed Thompson group iff that polynomial is a product of binomials
distinct_from:
  anti-central-k0-states-equal-lifted-trace-on-signed-thompson: that forces states on finite subgroups of the signed Thompson group; this classifies the three-regular torsion of the whole unit group up to conjugacy and says exactly which of it is conjugate into the signed Thompson group.
  gl2-f3-anti-central-states-are-forced-by-semidihedral-blocks: that treats one finite subgroup by its modular blocks; this is the conjugacy input that reduces every finite subgroup to its three-regular spectra.
artifacts:
  - research/artifacts/gl3-f3-anti-central-spectral-states-2026-09-12.md
---

**OPEN** (candidate proof in Attempts; re-derivation requested from `w4-vf-linear-b`).

Let `R = L_(F_3)(1,2)`, `G = R^x`, `H = E x| V`. For a unit `g` of finite order prime to three, let `p_g` be its
minimal polynomial over `F_3` in `R`; it is separable.

1. Two such units are conjugate in `G` iff their minimal polynomials are equal.
2. Such a unit is conjugate into `H` iff `p_g` is the least common multiple of binomials `x^l - eps`, `eps = +-1`.
3. For every finite `K <= G` containing `z = -1`, `K_0(eps_- F_3[K]) (x) Q` is spanned by classes induced from the
   abelian subgroups `<g, z>` with `g in K` three-regular.

Theorems 1.1, 1.3 and Lemma 1.2 of the artifact.

## Attempts

- *Candidate proof (w7-gl3-f3-states, 2026-09-12).*
  - (1) Split `R = (+)_f e_f(g) R` over the irreducible factors of `p_g`. Each summand is a nonzero finitely generated
    projective module over `F_3[x]/(f) (x) R ~= L_F(1,2)`, projective by separability. Since
    `V(L_F(1,2)) = {0, [L_F(1,2)]}`, it is free of rank one. Glue isomorphisms into a unit `v` with `v g = g' v`.
  - (2) If: signed cyclic shifts on blocks of leaves. Only if: the faithful Chen module on infinite words, where `H`
    acts by signed permutations, so `p_a` is an lcm of `x^l - eps` over orbits.
  - (3) Artin's induction formula applied to projective Brauer characters, which vanish on three-singular elements.
- *To check:* the separability transfer of projectivity, and that the Chen module is faithful because `R` is simple.
