---
rg: 2
id: primitive-shell-sorted-matcher-has-no-fourier-return-proof
kind: route
title: Compare the flat entries of a hypothetical monomial square
target: primitive-shell-sorted-matcher-has-no-fourier-return
requires:
  - primitive-shell-sorted-matcher-is-one-phase-torus
---

Write `omega=exp(2 pi i/L)`.  Replacing `omega` by its inverse changes none
of the argument, so choose the Fourier convention

```text
K_(a,b)=r_a L^(-1/2) omega^(f(a)b),       |r_a|=1.       (1)
```

The first primitive ranks are

```text
f(0)=0,  f(1)=1,  f(3)=5.                             (2)
```

Indeed the corresponding least positive residues are `1,2,8`; these are
all below `q` when `n>=2` except that for `q=9` the last one is still the
least positive residue, and their ranks among positive integers prime to
`3` are `0,1,5`.  Thus `f` is not the identity permutation of `Z/LZ`.

## Symmetry

If `K_(a,b)=K_(b,a)`, putting `b=0` in (1) gives `r_a=r_0` for every `a`.
After cancelling this common phase, symmetry says

```text
f(a)b = f(b)a mod L                                  (3)
```

for all `a,b`.  Taking `b=1` and using `f(1)=1` makes `f(a)=a` for every
`a`, contrary to (2).  Hence no `RH` is symmetric.

## Monomial square

Suppose instead that `K^2=M` is monomial.  Write

```text
M_(a,c)=m_a delta_(c,sigma(a)),       |m_a|=1,
```

for a permutation `sigma`.  Since `K` is unitary, `K^2=M` implies
`K=M K^*`.  Comparing its `(a,b)` entry using (1) gives

```text
r_a omega^(f(a)b)
 = m_a conjugate(r_b) omega^(-f(b)sigma(a)).          (4)
```

At `b=0`, because `f(0)=0`, equation (4) yields
`m_a=r_a r_0`.  At `a=0`, after that substitution, it yields

```text
r_0 conjugate(r_b)=omega^(f(b)sigma(0)).              (5)
```

Substituting (5) back into (4) leaves the phase-free congruence

```text
f(a)b = f(b)(sigma(0)-sigma(a)) mod L.                (6)
```

Put `b=1`.  Since `f(1)=1`, (6) says
`sigma(0)-sigma(a)=f(a)`.  Now put `a=1` in (6); it says

```text
b=f(b) mod L
```

for every `b`, again contradicting (2).  Therefore `K^2` cannot be
monomial.

The last conclusion rules out the standard Fourier/Clifford return, but not
a hypothetical phase choice for which `K^2` is a dense involution.  No such
stronger conclusion is asserted.
