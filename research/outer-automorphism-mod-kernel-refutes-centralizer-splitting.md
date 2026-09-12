---
rg: 2
id: outer-automorphism-mod-kernel-refutes-centralizer-splitting
kind: claim
title: An outer automorphism trivial modulo a Kazhdan kernel prevents any M-times-centralizer splitting
distinct_from:
  relative-element-splits-into-m-times-centralizer: that is the proposed splitting sigma(z) in sigma(M).C(sigma(Gamma)) for all relatively centralizing z; this is the established counterexample, in a residually finite group, where the splitting fails in every injective representation.
  sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels: that is the relative defect criterion, which holds in the counterexample here; this shows only that one proposed proof of it is unsound.
---

**ESTABLISHED.** The splitting premise `relative-element-splits-into-m-times-centralizer`
is false.

**Obstruction.** Let `sigma : H -> K` be any injective homomorphism into any
group. Suppose `M <= Gamma <= H`, `z in H`, and

```text
sigma(z) = sigma(m_0) c    with   m_0 in M,  c in C_K(sigma(Gamma)).
```

Then `sigma(z gamma z^-1) = sigma(m_0 gamma m_0^-1)` for every `gamma in Gamma`.
By injectivity, `z` acts on `Gamma` as the inner automorphism by `m_0`.

**Witness (normal pair).**

- `P = SL_3(Z) ⋊ <alpha>`, with `alpha(x) = (x^T)^-1`.
- `M = Gamma = G = SL_3(Z)` and `z = alpha`.

Checks:

- `P` is residually finite, as a finite extension of a linear group, so it is
  sofic.
- `SL_3(Z)` is Kazhdan and normal in `P`, and `Gamma` is trivially infranormal
  in `G = Gamma`.
- `[z, Gamma] <= M`.

But `alpha` is not inner on `SL_3(Z)`. The companion matrix `C` of
`t^3 - 2t^2 - 1`, that is `[[0,0,1],[1,0,0],[0,1,2]]`, has determinant `1` and
trace `2`. Its image `alpha(C) = C^-T` has trace `tr(C^-1) = 0`. Conjugation
preserves trace, so no `m_0` realizes `alpha`, and the splitting fails for
every injective sofic representation of `P`.

**Witness (non-normal pair).** Take `H = G_KT x P`, where `Gamma_KT < G_KT` is
the Kun--Thom Theorem E pair, which is residually finite. Put
`M = 1 x SL_3(Z)`, `Gamma = Gamma_KT x SL_3(Z)`, `G = G_KT x SL_3(Z)` and
`z = (1, alpha)`. Then:

- `H` is residually finite;
- `Gamma` is infranormal and not normal in `G`;
- `[z, Gamma] <= M`;
- the same trace argument on the second factor kills the splitting.

The relative defect criterion holds here: `g z g^-1` lies in `1 x P`, so its
commutators with `Gamma` lie in `M`. So this refutes the splitting premise,
not the relative criterion.

Derivation: `outer-automorphism-mod-kernel-splitting-proof`.

**Lesson for the hinge.** Any correct absorption of the mod-`M` ambiguity must
tolerate automorphisms of `Gamma` that are trivial modulo `M` but not inner.
The target must be transportable by `sigma(G)` and must land commutators with
`sigma(Gamma)` in `sigma(M)`. An exact form that survives: `d in M` if and only
if `sigma(d)` lies in the von Neumann algebra `W*(sigma(M))`, since
`E_(L(M))(u_d) = 0` for `d` outside `M`.
