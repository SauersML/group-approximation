---
rg: 2
id: stw78-countable-ordinal-gluing-proof
kind: route
title: Extend layer traces and reduce every limit to a sequence or a stabilized stage
target: stw78-countable-ordinal-regular-targets
requires:
  - stw78-nuclear-strong-pi-extension-gluing
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

## Every successor layer is purely infinite

Fix `beta<lambda` for which `D_beta` is nonzero.  The layer `D_beta` is an
ideal of the unital nuclear quotient `B/I_beta`.  Suppose it admitted a
nonzero densely finite lower
semicontinuous 2-quasitrace.  It is finite on the Pedersen ideal, and
`Ped(D_beta)=D_beta` by algebraic simplicity.  It is therefore everywhere
finite and bounded.  Exactness of `D_beta` then makes this bounded
2-quasitrace a trace.

A bounded trace on an ideal extends to the containing algebra.  Explicitly,
for an increasing positive contractive approximate unit `(e_n)` of
`D_beta`, its extension on `(B/I_beta)_+` is

```text
tau_tilde(x)=lim_n tau(x^(1/2)e_n x^(1/2)).              (2)
```

The nonzero extension normalizes at the unit of `B/I_beta`; composing with
`B->B/I_beta` would give a normalized trace, hence a normalized
2-quasitrace, on `B`.  This contradiction works for every `beta`, including
successors of limit ordinals: no unitality of `I_beta` or `D_beta` is used.

The sigma-unital simple almost-unperforated dichotomy now excludes the
stably finite alternative for `D_beta`, because that alternative supplies a
nonzero densely finite lower semicontinuous 2-quasitrace.  Thus every layer
is simple purely infinite, hence strongly purely infinite.  It is separable
and nuclear, so it is `O_infinity`-stable.

## Transfinite gluing

The zero algebra `I_0` is `O_infinity`-stable.  We prove by transfinite
induction that every `I_gamma`, `0<gamma<=lambda`, is `O_infinity`-stable.
At a successor stage with nonzero layer, apply
Toms--Winter Theorem 4.3 to

```text
0 -> I_beta -> I_(beta+1) -> D_beta -> 0.               (3)
```

All three algebras in (3) are separable, and `O_infinity` is separable,
unital, strongly self-absorbing, and `K_1`-injective, exactly the hypotheses
of that theorem.  If the layer is zero, then `I_(beta+1)=I_beta` and there is
nothing to prove.

Let `gamma` be a nonzero limit ordinal.  If `cf(gamma)=omega`, choose a
strictly increasing cofinal sequence `(beta_n)` in `gamma`.  Continuity of
(1) gives

```text
I_gamma = closure(union_n I_(beta_n))
        = lim_n I_(beta_n).                             (4)
```

Every term in (4) is `O_infinity`-stable by induction, so Toms--Winter
Corollary 3.4 makes `I_gamma` `O_infinity`-stable.

Suppose instead that `cf(gamma)>omega`.  The ideal `I_gamma` is separable.
Choose a dense sequence `(x_n)` in it.  For every pair `(n,k)`, continuity
of the filtration supplies an ordinal `alpha_(n,k)<gamma` and an element
`y_(n,k) in I_(alpha_(n,k))` such that

```text
||x_n-y_(n,k)||<1/k.
```

Put

```text
beta=sup_(n,k)(alpha_(n,k)+1).
```

Uncountable cofinality gives `beta<gamma`.  Every `y_(n,k)` belongs to
`I_beta`, so closedness gives `x_n in I_beta` for every `n`.  Density then
gives `I_gamma subset I_beta`; the reverse inclusion is automatic.  Hence

```text
I_gamma=I_beta.                                          (5)
```

The induction hypothesis at `beta` proves `O_infinity`-stability of
`I_gamma`.  Thus every limit stage is handled either by one sequential
inductive limit or by literal stabilization at an earlier stage; no
uncountable inductive-limit theorem is used.

The induction gives `B=I_lambda` `O_infinity`-stable and therefore strongly
purely infinite.  Gabe's Theorem 9.7 then makes every nuclear map from a
separable exact domain into `B` strongly `O_infinity`-stable.  Maps from an
LXXVIII domain are nuclear because that domain is nuclear.
