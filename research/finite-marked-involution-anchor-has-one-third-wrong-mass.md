---
rg: 2
id: finite-marked-involution-anchor-has-one-third-wrong-mass
kind: claim
title: A finite marked involution anchor has at least one-third wrong Plancherel mass
distinct_from:
  regular-finite-controlled-phase-has-half-wrong-mass: that treats a central nonlinear Boolean phase and gets an exact half; this treats an arbitrary noncentral involution proposed as a spectral anchor for the controlled reflection.
  finite-group-selector-induction-barrier: that forces affine selector characters; this uses only the marked regular trace and applies without a commuting selector family.
  controlled-reynolds-density-has-no-fixed-physical-carrier: that compares physical trace with adjoint rank under a direct sum; this shows a finite auxiliary packet cannot even supply a universally pure trace-one-half anchor.
---

**ESTABLISHED.**  Let `F` be finite, let `J` be a central involution, put

```text
q=(1-J)/2,
```

and let `a in F\{1,J}` be an involution.  For each irreducible
representation `pi` with `pi(J)=-I`, define

```text
nu_pi=tr_pi(pi(a)),
w_pi=dim(pi)^2/(|F|/2).                                 (FMA1)
```

The weights sum to one and the normalized marked regular trace gives

```text
sum_pi w_pi nu_pi=0.                                   (FMA2)
```

Since `a` is an involution, every `nu_pi` is real and lies in `[-1,1]`.
Consequently the total Plancherel weight of types satisfying

```text
nu_pi=1/2                                               (FMA3)
```

is at most `2/3`.  At least one-third of the marked regular sector therefore
has the wrong trace for a literal controlled-Z reflection, whose normalized
spin trace is `1/2`.

More robustly, for `0<=epsilon<1/2`, the weight `g_epsilon` of types with

```text
|nu_pi-1/2|<=epsilon
```

obeys

```text
g_epsilon <=1/(3/2-epsilon),
1-g_epsilon >=(1/2-epsilon)/(3/2-epsilon).              (FMA4)
```

Thus replacing the coarse Pauli reflection in an odd row
`t=W a W^*` by an element of a larger **finite** marked packet cannot
authenticate the pure orientation.  On a controlled spin block the row
requires

```text
tr(t)=mu/2=nu_pi,                                       (FMA5)
```

so only the types in `(FMA3)` can have `mu=1`, and the finite marked regular
representation retains at least one-third wrong orientation mass.  If the
marked sector has a unique irreducible type, `(FMA2)` is sharper: every
noncentral element has normalized trace zero, so the unique type is entirely
wrong for this purpose.

This eliminates the smallest finite nonnormal anchor repair.  A viable
self-similar odd row must obtain its trace-one-half anchor from a genuinely
infinite/type-selective coefficient mechanism, or couple the wrong finite
types to the forbidden payload so they cannot extend.  Merely choosing a
more elaborate finite group element cannot supply the missing averaged
Reynolds return.
