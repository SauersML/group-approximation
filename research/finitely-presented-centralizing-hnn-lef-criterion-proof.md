---
rg: 2
id: finitely-presented-centralizing-hnn-lef-criterion-proof
kind: route
title: Promote one exact local chart to a separating finite quotient and apply the profinite edge criterion
target: finitely-presented-centralizing-hnn-lef-criterion
requires:
  - centralizing-hnn-is-residually-finite-iff-edge-is-separable
---

Choose a finite presentation `K=<S|R>` and a finite generating set
`T={t_1,...,t_m}` of `L`, with each `t_i` represented by an `S`-word.  Then

```text
Gamma=<S,v | R, [v,t_1],...,[v,t_m]>                       (LHCP1)
```

is a finite presentation: commuting with the `t_i` and their inverses makes
`v` commute with every word in `T`.

We use the standard finite-presentation lemma in a form that exposes its one
quantifier.  Let `G=<A|U>` be finitely presented and LEF, and fix
`g in G\{1}` represented by `a_1...a_d`.  Form a finite set `Omega subset G`
containing:

1. `1`, every generator and inverse generator;
2. every prefix of every defining relator in `U`;
3. every prefix of `a_1...a_d`; and
4. every pairwise product from 1--3 that is used in taking the next prefix.

Take an injective local homomorphism `theta:Omega->Q` to a finite group.
Define `rho` on the generators by `rho(a)=theta(a)`.  Successive use of local
multiplicativity along each relator-prefix chain gives `rho(u)=1` for every
`u in U`.  Therefore `rho` extends to a homomorphism `G->Q`.  The same prefix
calculation gives `rho(g)=theta(g)`, while injectivity on `{1,g}` gives
`theta(g)!=theta(1)`.  Hence every nontrivial `g` survives in a finite
quotient and `G` is residually finite.  The reverse implication, residually
finite implies LEF, follows by separating all unequal products in a finite
window with one finite product of quotient maps.

Apply the lemma to the finite presentation `(LHCP1)`.  It gives

```text
Gamma LEF  iff  Gamma residually finite.                    (LHCP2)
```

Since `K` is residually finite,
[[centralizing-hnn-is-residually-finite-iff-edge-is-separable]] gives

```text
Gamma residually finite  iff  L is profinitely closed in K. (LHCP3)
```

Combining `(LHCP2)` and `(LHCP3)` proves the claim.  Notice why no conclusion
about soficity follows: local multiplicativity in a sofic model is only true
off a small Hamming exceptional set, so the relator-prefix calculation does
not produce a genuine homomorphism to the finite symmetric group.
