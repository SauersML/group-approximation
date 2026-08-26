---
rg: 2
id: sp4-maslov-circle-survives-in-bernoulli-l0-cohomology
kind: claim
title: The small Maslov circle survives as constant cocycles in Bernoulli L0 cohomology
distinct_from:
  sp4-fd-projective-multiplier-is-finite: that says only finitely many scalar classes are realized by finite-dimensional projective representations; this proves that arbitrarily small nontrivial scalar classes nevertheless survive after passing to Bernoulli measurable coefficients.
  sp4-isw-theorem-c-embeddable-twist-data-exists: that additionally requires Connes embeddability of all twisted crossed products; this establishes the complete cohomological half of its constant-cocycle construction.
artifacts:
  - research/artifacts/lifting-program-2026-08-21.md
---

**ESTABLISHED.**  Let `Gamma=Sp_4(Z)` and let it act by the Bernoulli shift
on `X=T^Gamma`.  There are normalized scalar cocycles

```text
c_n in Z^2(Gamma,T),       c_n(g,h)->1 for every g,h,       (MSC1)
```

such that the corresponding constant cocycles in
`Z^2(Gamma,L^0(X,T))` are non-coboundaries for every `n`.

Indeed `H^2(Gamma,R)` has a nonzero Maslov class.  Choose a real cocycle `b`
representing it and put

```text
c_theta(g,h)=exp(2 pi i theta b(g,h)).                    (MSC2)
```

By the universal coefficient theorem with divisible trivial coefficients,
the nonzero real class evaluates nontrivially on some
`z in H_2(Gamma,Z)`; write this value as `alpha!=0`.  If `[c_theta]=0`, its
evaluation on `z` is one, so `theta alpha in Z`.  The exceptional parameters
are therefore contained in the discrete set `alpha^(-1)Z`.  We may choose
`theta_n->0` outside it.  Then `(MSC1)` holds and
`[c_(theta_n)]!=0` in `H^2(Gamma,T)`.

The final passage is the natural one, not an abstract copy.  Jiang,
*A remark on T-valued cohomology groups of algebraic group actions*,
Lemma 2.9 and Remark 2.10 (arXiv:1509.08278; source checked 2026-08-25),
proves that for a Bernoulli action of a property `(T)` group the map

```text
H^2(Gamma,T) -> H^2(Gamma acting on X;T)                  (MSC3)
```

induced by regarding a scalar cocycle as constant in `x` is injective.
Since `Sp_4(Z)` has property `(T)`, every class chosen above remains a
non-coboundary in `L^0(X,T)`.  Thus conditions (a) and (b) of the ISW
Theorem-C packet are fully established for the constant Maslov circle; only
Connes embeddability remains.
