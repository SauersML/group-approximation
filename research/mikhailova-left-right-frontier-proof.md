---
rg: 2
id: mikhailova-left-right-frontier-proof
kind: route
title: Separate exact Schreier models from the surviving Hamming-chart problem
target: mikhailova-left-right-action-current-frontier
requires:
  - commuting-sofic-actions-need-not-combine
  - mihailova-left-right-local-models-do-not-see-q
---

## Presentation independence

Let `q_i:F_i->H` be two finite free presentations. Choose lifts in `F_1` of
a free basis of `F_2`; they define a homomorphism `s:F_2->F_1` with
`q_1 s=q_2`. The action belonging to `q_2` is the pullback of the action
belonging to `q_1` along `s x s`. Restriction to `im(s x s)` and pullback
through `F_2 x F_2 -> im(s x s)` preserve soficity by GKP Proposition 2.15.
Reversing the roles of the presentations proves equivalence.

## Residually finite action

For a transitive action `G` on `G/M`, residual finiteness as a `G`-set—finite equivariant quotients separating every finite subset—is equivalent to separability of `M` in `G`.

If `H` is residually finite and `(u,v) notin M_H`, choose a finite quotient
`c:H->C` with `c(q(u)) != c(q(v))`. Then `(c q) x (c q)` sends `M_H`
into `Delta C` but does not send `(u,v)` into `Delta C`; hence `M_H` is
separable.

Conversely assume `M_H` is separable. If `q(w) != 1`, then
`(w,1) notin M_H`, so some finite quotient
`theta:F_m x F_m->K` satisfies

```text
theta(w,1) notin theta(M_H).                           (MLF2)
```

Put `A=theta(F_m x {1})` and `D=theta(N x {1})`. The subgroup `D` is
normal in `A`, and `(MLF2)` implies `theta(w,1) notin D`. Thus
`F_m->A/D` kills `N` but not `w`, so it factors through a finite quotient
of `H` separating `q(w)`. Therefore `H` is residually finite.

## Why the published counterexample does not transfer

Kun--Thom plus GKP gives a nonsofic action

```text
G x G acts on (G x G)/Delta Gamma
```

with `Gamma<G` infranormal and Kazhdan. It proves that two commuting sofic
coordinate actions need not combine. It supplies no permanence of
nonsoficity under precomposition by an epimorphism. GKP Proposition 2.15
gives the opposite one-way statement: a sofic quotient action pulls back to
a sofic action. The reverse implication is false as a general proof
principle: `F_m` acting on `F_m/N` is sofic for every `N`, although the
quotient group `F_m/N` can be nonsofic. Finite normal generation of `N`
does not change this.

## Exact remaining criterion

By GKP Proposition 2.9, `(MLF1)` is sofic exactly when there are a free
ultrafilter `U`, a homomorphism

```text
Phi:F_m x F_m -> product_U Sym(A_n),
```

and a map `Pi:H->X_U` such that

```text
S_U(Phi(u,v))(Pi(h))=Pi(q(u)h q(v)^(-1)),
d_U(Pi(h),Pi(k))=1 whenever h!=k.                      (MLF3)
```

Condition `(MLF3)` is the positive-density Hamming coherence absent from
local metric models. The two free coordinate actions provide its
restrictions, but `commuting-sofic-actions-need-not-combine` proves that
those restrictions cannot be glued formally. Ioana's
non-very-flexible-P-stability theorem for products of free groups blocks
replacing `Phi` by exact finite actions in general.

## Attempts closed

- **Finite equivariant quotients / residually finite action:** equivalent to
  residual finiteness of `H`, so impossible for the compiler host.
- **Arbitrary finite metric patches:** universal for the residually finite
  actor and therefore quotient-blind.
- **Separate left and right charts:** invalidated as a permanence principle
  by the commuting-action counterexample.
- **Descent from the nonsofic `H x H` action:** no such descent theorem
  exists; free-cover pullback can erase quotient nonsoficity.
- **Levelwise correction of approximate product actions:** unavailable
  because `F_m x F_m` is not even very flexibly permutation stable.

None of these failures proves soficity or nonsoficity. They leave precisely
`(MLF3)` open.

## References

GKP, *Research in the Mathematical Sciences* 12 (2025), Propositions 2.9 and
2.15 and Theorem 2.19; Ioana, arXiv:1909.00282; Kun--Thom, arXiv:2608.06222
via the existing verified node.
