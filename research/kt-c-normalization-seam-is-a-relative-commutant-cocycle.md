---
rg: 2
id: kt-c-normalization-seam-is-a-relative-commutant-cocycle
kind: claim
title: Closing the mixed C-normalization seam is exactly a relative-commutant one-cocycle equation
distinct_from:
  kt-c-normalization-is-the-first-finite-normalizer-seam: that identifies the finite quotient words and their maximal energy in the AFP paste; this identifies the exact nonabelian cohomology class and its gauge action.
  kt-ab-normalizer-row-forces-wall-gauge-propagation: that gives a two-copy HS inequality for one row; this is an exact all-Gamma cocycle identity in an arbitrary normalizer lift.
  kun-thom-finitary-action-lifts-to-normalizer: that asks for the whole actor lift; this isolates the first necessary correction equation after the one-compressor and external lifts have already been pasted.
---

**ESTABLISHED EXACT EQUIVALENCE.**  Let

```text
u:P_A=H_A *_<A> S -> N_(R^omega)(R)
```

be any homomorphic normalizer lift of the amalgam action.  Put

```text
K=U(R' cap R^omega),
rho_gamma=u_(alpha_C(gamma)),
v_gamma=u_C u_gamma u_C^*,
k_gamma=v_gamma rho_gamma^*.                          (KCC1)
```

The two unitaries `v_gamma` and `rho_gamma` induce the same automorphism of
`R`, so `k_gamma in K`.  For

```text
beta_gamma=Ad(rho_gamma)|K
```

one has the nonabelian one-cocycle identity

```text
k_(gamma delta)=k_gamma beta_gamma(k_delta).            (KCC2)
```

If `z in K` and the compressor-normalizer lift is changed from `u_C` to
`z u_C`, then

```text
k'_gamma=z k_gamma beta_gamma(z^*).                     (KCC3)
```

Consequently all finite seam rows

```text
(z u_C)u_gamma(z u_C)^*=rho_gamma                      (KCC4)
```

hold for every `gamma in Gamma` if and only if

```text
k_gamma=z^* beta_gamma(z)                              (KCC5)
```

for every `gamma`, equivalently if and only if the class of `k` is a
nonabelian coboundary.  It is enough to check `(KCC4)` on one finite
generating set of `Gamma`.

This equivalence concerns the `C`-normalization seam only.  A gauge used in a
full lift must additionally preserve the finite `SL_3(Z)` relations involving
`A,C`, and further quotient-kernel relations may remain after `(KCC4)`.
Thus `(KCC5)` is a precise necessary first correction equation, not a claim
that one arbitrary coboundary solves the whole actor.

DERIVATION
kt-c-normalization-relative-cocycle-proof
