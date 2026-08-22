---
rg: 2
id: affine-haar-process-fourier-modulus-compiler
kind: claim
title: Fourier modulus zero-or-one exactly characterizes affine Haar processes and still compiles to a group factor corner
distinct_from:
  infinite-label-process-is-haar-linear-iff-fourier-binary: that requires every Fourier moment itself to be zero or one and obtains Haar measure on a subgroup; this permits nontrivial finite-field phases and obtains an invariant affine coset.
  finite-field-convolution-haarizes-affine-support: that constructs the affine Haar support hull as a weak limit; this is the exact intrinsic test on the original process and the group-factor compiler when it passes.
  thom-central-corner-criterion: that selects a scalar-character corner of a finite central extension; this uses an invariant base-space fiber in one elementary homogenized module.
---

In the notation of `infinite-label-process-is-haar-linear-iff-fourier-binary`,
the translate-name law `nu` is Haar measure on an invariant affine linear
subshift

```text
A=x_0+K <=_aff (F_p^I)^H                              (AHF1)
```

if and only if every finite Fourier moment satisfies

```text
|M(a)| in {0,1}.                                       (AHF2)
```

The moments of modulus one form `K^perp`; their phases specify the affine
offset.  Thus `(AHF2)` is strictly more permissive than the zero-or-one test:
deterministic nonzero coordinates and affine parity equations are allowed.

If the translates of the labels generate the source probability algebra,
the source action is conjugate to the affine Haar action on `A`.  Although
`A` need not contain zero, it has a canonical one-coordinate homogenization

```text
K_tilde={(t x_0+k,t):t in F_p, k in K}
        <= (F_p^I)^H x F_p.                            (AHF3)
```

The actor fixes `t`, acts by continuous group automorphisms on `K_tilde`, and
the invariant fiber `t=1` has Haar mass `1/p`.  Hence

```text
L^infinity(A,m_A) rtimes H
```

is a positive central corner of

```text
L^infinity(K_tilde,m_Ktilde) rtimes H
   = L(K_tilde-hat rtimes H).                          (AHF4)
```

Therefore any non-CE action admitting generating labels satisfying `(AHF2)`
already produces a non-hyperlinear semidirect product.  For direct IRS
membership labels, the constantly-one identity coordinate is no longer an
obstruction: it is an affine phase absorbed by `(AHF3)`.  The genuine hurdle
is whether all joint membership moments have modulus zero or one, equivalently
whether the entire stabilizer-name law is affine Haar; subgroup closure is
nonlinear and is not made automatic by homogenization.
