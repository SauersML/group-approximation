---
rg: 2
id: bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect
kind: claim
title: On the hyperbolic Leavitt cover, sizes read from bounded-multiplicity Kazhdan sectors of the kernel are compressor invariant and blind to host twists
distinct_from:
  component-space-sizes-miss-leavitt-cover-defect: that covers the invariant sector of Gamma, the measure space of components; this covers every finite-dimensional isotype of the kernel at bounded multiplicity over the block algebra, where the ambient group, Gamma and its compressed images all act inside the kernel closure.
  conjugation-invariant-sizes-miss-relative-defect: that shows sizes of realizer sets alone are compressor invariant and leaves the position of Gamma_s as the only untransported datum; this shows that on bounded-multiplicity Kazhdan sectors of the kernel that position is not a datum either.
  kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure: that is the general representation-theoretic statement for any unitary representation; this applies it to sofic representations of the Leavitt cover and to realized relative twists.
artifacts:
  - research/artifacts/rnorm-kazhdan-projection-sizes-2026-09-12.md
---

**ESTABLISHED.** Take the cover `1 -> N -> G -> R^x -> 1` of
`hyperbolic-kazhdan-cover-of-leavitt-unit-group`, and the configuration of
`relative-defect-iff-surjective-compressor-endomorphisms`: `M = N`,
`Gamma_hat = pi^-1(EL_alpha(R))`, and the compressors `t`. Let `sigma : G -> S_U`
be a sofic representation, acting by Koopman unitaries on the Loeb space
`H = L^2(X_U, mu_U)`.

- **Block algebra.** Let `A` be the weak closure of the `sigma(N)`-invariant
  diagonal algebra `D^N`. By block invariance
  (`kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`), `A` commutes
  with `sigma(G)`.
- **The sector.** Let `H_b` be the closed span of all `V_rho (x) E`. Here `rho`
  ranges over finite-dimensional irreducible types of `N`, and `E` ranges over the
  subspaces of the Kazhdan multiplicity space `W_rho` that are invariant under `A`
  and `W_rho(G)` and have bounded `A`-multiplicity. Write `P_b` for the projection
  onto `H_b`.
- **Realizers.** The realizer sets are `R(q) = x M_s C_s` as in
  `realized-relative-twists-embed-in-outer-twist-group`. For each realized twist
  `q` let `S_b(q)` be the strong closure of `T . P_b R(q) P_b`.

1. **Everything acts through the kernel closure.** `P_b` commutes with `sigma(G)`.
   For every `g in G`, `sigma(g)|_(H_b)` lies in the strong closure of
   `T . sigma(N)|_(H_b)`. In particular, on `H_b` the groups `sigma(Gamma_hat)`,
   `sigma(t Gamma_hat t^-1)`, `sigma(G)` and `sigma(N)` have the same strong
   closure times `T`.
2. **Compressors change nothing.** `S_b(eps_t(q)) = S_b(q)` for every realized
   twist `q` and every compressor `t`.
3. **Host twists look trivial.** If `z in G` and `[z, Gamma_hat] <= N`, then
   `S_b([sigma(z)]) = S_b(1)`. This covers `Q = C_(R^x)(EL_alpha(R))`, including
   the subgroup `A = <eps_u^k(V_(1000))>` on which `eps_u` is a strict
   self-embedding.
4. **No such size sees the defect.** A size may read `S_b`, the positions of
   `Gamma_hat` and its compressed images on `H_b`, the isotypic projections,
   multiplicity functions and `A`-module structure of `H_b`, the Kazhdan
   projections of twisted representations `rho-bar (x) sigma|_N` restricted to
   `H_b`, and transport costs of `sigma(G)` on `H_b`. Every such size takes the
   same value on `B` and on `eps_t(B)`, and the same value on every subgroup of
   host twists as on the trivial group.

Derivation: `bounded-multiplicity-kazhdan-sectors-defect-proof`.

**Red-flag check.** Property (T) of `N` enters through Wang finiteness.
Nonsoficity of `R^x` enters through block invariance, which puts `A` in the
commutant of `sigma(G)`. No soficity of `G` is used. The claim is an obstruction
to a method and holds whether or not the cover is sofic. It says nothing about
Thompson's `V`.

**What survives.** Every finite-dimensional Kazhdan sector outside `H_b` has
unbounded multiplicity over the block algebra. There `W_rho` is a projective
representation of `R^x` that can be non-scalar, and the position of `Gamma_hat`
is a genuine datum: the fixed spaces of `W_rho(EL_alpha(R))` and of
`W_rho(u^-1 EL_alpha(R) u)` are unitarily conjugate and nested. On the weakly
mixing part of `sigma|_N` every Kazhdan projection vanishes. A size there must be
a relative index, invariant under conjugation and quantized, for instance a Jones
index bounded below `2` by a median argument. None is constructed (artifact,
Section 4).
