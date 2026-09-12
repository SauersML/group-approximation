---
rg: 2
id: component-space-sizes-miss-leavitt-cover-defect
kind: claim
title: On the hyperbolic Leavitt cover, sizes read from the measure space of Gamma-components are compressor invariant and blind to host twists
distinct_from:
  finite-orbit-indices-miss-twists-without-finite-quotients: that shows positive-mass cluster type data has finite orbits, so it cannot see twists from groups without finite quotients; this covers the whole measure space of components, including diffuse type data with infinite orbits, and shows that compressors act on it trivially and host twists act on it as the centralizer does.
  conjugation-invariant-sizes-miss-relative-defect: that shows sizes read from conjugacy invariants of realizer sets alone are compressor invariant, with no property (T); this concerns sizes read relative to sigma(Gamma), the candidates that claim leaves open, and shows they are compressor invariant on the cover because sigma(G) fixes the component algebra pointwise.
  kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient: that shows sigma(G) fixes the block algebra of the kernel; this derives that the compressor refinement factor is trivial, that compressed twists act on components exactly as the original twists do, and that host twists act as centralizer elements.
  realized-relative-twists-embed-in-outer-twist-group: that embeds realized twists in the outer twist group of the pair; this computes their action on the measure space of components and, for the cover, embeds the outer twist group in the centralizer of EL_alpha(R) in Out(N).
  relative-normalization-modulo-kazhdan-kernel: that is the open normalization statement; this rules out, on the cover, size arguments for it read from the measure space of components.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED.** Let `1 -> M -> G -> G/M -> 1` be exact with `G` countable,
`M` infinite and Kazhdan, and every homomorphism `G/M -> S_U` trivial. Let
`M <= Gamma <= G` be a rigid pair, and let `sigma : G -> S_U` be a sofic
representation, i.e. the ultraproduct of a sofic approximation, so trace zero.
Notation as in `realized-relative-twists-embed-in-outer-twist-group`:
`Gamma_s`, `M_s`, `C_s`, the realized twist group `Q_s`, the realizer sets
`R(q) = x M_s C_s`, the compressor endomorphisms `eps_t`, and `s = sigma(t)`.

For `K <= G` write `D^K` for the `sigma(K)`-invariant part of the diagonal
ultraproduct `D_U`. By Kun--Thom Lemma 2.3, `D^Gamma` is the block algebra of
the `Gamma_s`-components. It is the measure space of components.

**Component data.** A realizer `x` normalizes `Gamma_s`, so `Ad(x)` preserves
`D^Gamma`. Put

```text
Act(q) = { Ad(x)|_(D^Gamma) : x in R(q) }        for q in Q_s.
```

The ambient data are:
- the corner classes `p -> [sigma|_Gamma p]`: the `S_U(p)`-conjugacy classes of
  the restrictions of `sigma|_Gamma` to projections `p` in `D^Gamma`;
- for each compressor `t`, the refinement inclusion `D^Gamma <= D^(t Gamma t^-1)`
  and its fibre counts;
- the transports `Ad(s) : D^Gamma -> D^(t Gamma t^-1)`.

A **component-level quantity** of a subgroup `B <= Q_s` is a function of the
family `{Act(q) : q in B}` and the ambient data. Examples:
- orbit relations and orbit masses of realized twists on components;
- the precomposition action of `B` on corner classes, which covers the atomic
  *and the diffuse* parts of the cluster type distribution. For `x in R(q)` it
  sends `[sigma|_Gamma p]` to `[sigma|_Gamma (x p x^-1)]`, so it is read off
  `Act(q)`;
- fibre counts of compressor refinement factors.

These are Kun--Thom's orbit and isotropy sizes with counting replaced by measure,
the shape that `finite-orbit-indices-miss-twists-without-finite-quotients` left
open.

1. **The component space is fixed by `sigma(G)`.** For every compressor `t`,

   ```text
   D^M  =  D^(t Gamma t^-1)  =  D^Gamma  =  D^G .
   ```

   So the refinement factor is the identity with fibre counts `1`, every
   `sigma(g)` fixes `D^Gamma` pointwise, and every transport `Ad(s)` is the
   identity. Kun--Thom's compressor map on components is the identity.
2. **Compressors act trivially on the component data.** `Act(eps_t(q)) = Act(q)`
   for every `q in Q_s` and every compressor `t`. So every subgroup `B <= Q_s`
   has the same component-level quantities as `eps_t(B)`.
3. **Host twists act as the centralizer.** If `z in G` and `[z, Gamma] <= M`,
   then `Act([sigma(z)]) = Ad(C_s)|_(D^Gamma) = Act(1)`. So every subgroup of the
   host quotient `Q = Z/(M . C_G(Gamma))`, embedded in `Q_s` by item 5 of
   `realized-relative-twists-embed-in-outer-twist-group`, has the component-level
   quantities of the trivial group.
4. **No such size registers a strict compressor self-embedding.** If
   `eps_t(B) < B` strictly, every component-level quantity takes the same value
   on `B` and on `eps_t(B)`. On every subgroup of `Q` it takes the value it takes
   on `1`.
5. **The cover, in `Out(N)`.** Take the cover `1 -> N -> G -> R^x -> 1` of
   `hyperbolic-kazhdan-cover-of-leavitt-unit-group`, with `M = N`,
   `Gamma = Gamma_hat = pi^-1(EL_alpha(R))`, the compressor `u_hat`, and
   `A = <eps_u^k(V_(1000)) : k >= 0>` as in
   `finite-orbit-indices-miss-twists-without-finite-quotients`. `R^x` is simple
   and not sofic, so items 1-4 apply: `A`, `eps_u(A)` and `1` have the same
   component-level quantities. Moreover:
   - `phi -> [phi|_(M_s)]` embeds `Out_M(Gamma_s)` in `Out(N)`, with image in
     the centralizer `C_Out(N)(EL_alpha(R))`, and `eps_u` becomes conjugation by
     the class of `u_hat^-1`;
   - for a lift `z` of the defect element, `[z]` lies outside
     `eps_u(Out_M(Gamma_s))`, whatever `sigma` is;
   - for every projection `p` in `D^Gamma`, the stabilizer `Q_s(p)` of
     `[sigma|_Gamma p]` contains `[z]` and satisfies `eps_u(Q_s(p)) <= Q_s(p)`.
     So the compression is strict at every corner;
   - if `sigma(G)` normalizes `N_rel(sigma)`, then `Q_s <= C_Out(N)(R^x)`, and
     this centralizer meets `R^x` trivially.

Derivation: `component-space-sizes-miss-cover-defect-proof`.

**This is an obstruction to a method, not evidence about soficity.** Unlike
`conjugation-invariant-sizes-miss-relative-defect` and
`finite-orbit-indices-miss-twists-without-finite-quotients`, it consumes
property (T). Property (T) of `M` enters through the expander decomposition,
together with the absence of sofic representations of `G/M`. These inputs are
what fix the component space pointwise. The obstruction uses no soficity of `G`
and holds whether or not the cover is sofic. Amenable hosts such as `BS(1,2)`
have no infinite Kazhdan kernel, so it says nothing there. Nothing about
Thompson's `V` follows.

**What survives.** Kun--Thom Theorem 4.1 has two halves.
- **Between components:** orbit sizes, the median, and the pigeonhole along the
  compressor map. On the cover that map is the identity, so this half has
  nothing to run on; items 1-4 are the precise form.
- **Within a component:** isotropy counts. The relative isotropy at an invariant
  corner `p` is `Q_s(p)`. It is infinite, it contains `A`, and `eps_u`
  compresses it strictly at every corner. So cardinality cannot run the
  integer-index step either.

A size that detects the cover's defect has to be read inside single `N`-blocks,
where `sigma(G)` acts as one approximate `G`-set. It has to separate twists that
centralize `EL_alpha(R)` in `Out(N)` from twists that centralize all of `R^x`.
By `bounded-blockwise-inner-realizers-fail-off-kernel`, it cannot do so at
bounded word length in `N`. None is constructed.
