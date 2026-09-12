---
rg: 2
id: conjugation-image-obstruction-proof
kind: route
title: Permute a basis indexed by the group and model it by partial bijections on growing balls
target: conjugation-image-of-a-torsion-free-mf-group-is-arbitrary
requires:
  - lef-implies-operator-mf
artifacts:
  - research/artifacts/conjugation-image-obstruction-and-self-centralizing-kernel-2026-09-08.md
---

## The group

With `F` free onto `G` by `q`, kernel `R`, define `A`, `H` and the action as
in `(CI2)`; the group law is `(a,f)(b,h) = (a + f.b, fh)`.

**Torsion-freeness.**  If `(a,f)^m = 1` with `m > 0`, projecting to `F` gives
`f^m = 1`; a free group is torsion-free, since a nontrivial element is
conjugate to a nonempty cyclically reduced word whose positive powers do not
cancel.  So `f = 1`, and then `ma = 0` in the free abelian `A` gives `a = 0`.

**Centralizer.**  Conjugation by `(a,f)` sends `e_g` to `e_(q(f)g)`, since `A`
is abelian.  Testing on `e_1` shows this is the identity exactly when
`q(f) = 1`.  So `C_H(A) = A x| R`, and `R` acts trivially on `A`, giving the
direct product and `(CI1)`.

**Generation.**  The `r` free generators and `e_1` generate: conjugating `e_1`
by a preimage of `g` gives `e_g`.

## Finite models, using no finite quotient of `G`

Let `X_n` be increasing finite subsets exhausting the free generating set, let
`D_n` be the radius-`n` ball of the free group on `X_n` inside `F`, and let
`B_n = q(D_n)`.  Both increase with union `F` and `G`.

For `x in X_n`, left multiplication by `q(x)` is a bijection from
`{g in B_n : q(x)g in B_n}` onto its image, two subsets of `B_n` of equal
size; extend it by any bijection of the complements to a permutation
`sigma_(x,n)` of `B_n`, and set `sigma_(x,n) = 1` for `x` outside `X_n`.
Because `F` is free these choices define a homomorphism

```text
sigma_n : F -> Sym(B_n),
```
and for each fixed `f` and `g` every point traversed while the word `f` acts
on `g` lies in `B_n` for large `n`, so

```text
sigma_n(f)g = q(f)g     eventually,                                 (1)
```
simultaneously for any fixed finite set of `g`.  The same construction applied
to left multiplication on `D_n` gives `tau_n : F -> Sym(D_n)` with

```text
tau_n(f)(1) = f != 1     eventually, for each fixed f != 1.         (2)
```

Choose `m_n -> infinity`, `m_n >= 2`, and set

```text
P_n = (Z/m_n)^(B_n) x| (Sym(B_n) x Sym(D_n)),
Phi_n(a,f) = (a|_(B_n) mod m_n, sigma_n(f), tau_n(f)),
```
with `Sym(D_n)` acting trivially on the abelian base.

For fixed `b in A` and `f in F`, the support of `b` is finite, so `(1)` on
that support and eventual inclusion of it and its translate in `B_n` give
`(f.b)|_(B_n) = sigma_n(f) . b|_(B_n)` for large `n`.  Since `sigma_n` and
`tau_n` are exact homomorphisms, for each fixed `u,v in H`

```text
Phi_n(uv) = Phi_n(u) Phi_n(v)     eventually.
```

Separation: if `f != 1`, `(2)` detects it; if `f = 1` and `a != 0`, a fixed
nonzero coefficient of `a` has its coordinate in `B_n` eventually and stays
nonzero once `m_n` exceeds its absolute value.

So on every fixed finite pattern all required multiplications eventually hold
and distinct elements eventually have distinct images: `H` is LEF, hence
operator MF by the prerequisite.  Concretely, composing with the left regular
permutation representations of `P_n` gives `V_n` with `V_n(1) = I`, eventual
exact multiplicativity on each fixed pair, and
`||V_n(h) - I|| >= sqrt 2` eventually for `h != 1`.

**No finite quotient of `G` appears.**  Only partial bijections on finite
subsets of `G` and `F` are used, which is what makes the construction work for
inputs that are not residually finite.

## The exact finite-dimensional calibration

Compute in `H`:

```text
(0,f)(e_1,1)(0,f)^-1(e_1,1)^-1 = (e_g,1)(-e_1,1) = (e_g - e_1, 1),
```
nonzero exactly when `g = q(f) != 1`, which is `(CI3)`.

Let `rho : H -> U(d)` be exact.  The commuting unitaries `rho(A)` have
finitely many joint character spaces; `A` preserves each, so `H` permutes them
through a homomorphism `G -> Sym(k)` with finite image.  If `g` lies in the
finite residual of `G` it acts trivially there, so `rho((0,f))` preserves each
space, on which `rho(e_1)` is scalar; hence the commutator is killed.
