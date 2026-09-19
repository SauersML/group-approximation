---
rg: 2
id: fixed-word-restriction-transfers-approximate-radical-proof
kind: route
title: Restrict every output microstate through the finitely many embedding words
target: marked-approximate-radical-survives-solution-group-embedding
requires:
  - slofstra-solution-group-embedding-preserves-marked-involutions
---

Choose finite presentations for `G` and `Gamma`.  For every generator `s` of
`G`, fix a word `W_s` in the generators of `Gamma` representing `phi(s)`.
For a unitary tuple `rho` write

```text
Def_G(rho)=max_(r in R_G)||rho(r)-1||_2,
Def_Gamma(rho)=max_(t in R_Gamma)||rho(t)-1||_2.
```

For each source relator `r`, let `A_r` be the area, in the chosen output
presentation, of the fixed trivial word `r(W)`, and let `B` be the area of
the fixed word expressing `phi(J')=J`.  Put `A=max_r A_r`.  These are finite
constants depending only on the two presentations and the embedding words.
The elementary van Kampen estimate gives, for every dimension and every
output tuple `rho`,

```text
sigma(s)=rho(W_s),
Def_G(sigma) <= A Def_Gamma(rho),                         (FWR1)
||rho(J)-sigma(J')||_2 <= B Def_Gamma(rho).               (FWR2)
```

Indeed a word of area `N` is a product of `N` conjugates of defining
relators, and normalized Hilbert--Schmidt norm is unitarily invariant and
subadditive.  This is a dimension-independent quantitative decoder, although
it need not come from a group retraction `Gamma -> G`.

For Slofstra's constructive embedding the constants are effective without
solving a word problem.  The first involution/collegial conversion makes the
substituted source relators and the marked equality explicit defining
relators of the intermediate presentation.  A collegial relator of length
`l` is then filled by its displayed wagon-wheel picture, which has `3l`
vertices.  If the solution group is given the finite picture presentation
with every local ordering as a relator, this is an explicit area-`3l`
certificate.  Thus `A` and `B` can be read directly from the finite output of
the construction (and converting to any other fixed finite presentation only
multiplies them by another computable constant).

More explicitly, define the marked collapse modulus

```text
kappa_G(epsilon)=sup { ||sigma(J')-1||_2 :
                        d>=1, Def_G(sigma)<=epsilon }.
```

Equations `(FWR1)--(FWR2)` prove the quantitative transfer

```text
kappa_Gamma(delta) <= kappa_G(A delta)+B delta.             (FWR3)
```

The same statement for total squared relator energy follows by replacing
`delta` with `sqrt(E)`.  Consequently any dimension-independent collapse
modulus for the marked source word survives the wagon-wheel embedding.

In particular, given any normalized-HS asymptotic representation `rho_n` of
`Gamma`, define

```text
sigma_n(s)=rho_n(W_s).
```

Then `(FWR1)` says that `sigma_n` is an asymptotic representation of `G`.

By hypothesis, `||sigma_n(J')-I||_2->0`, while `(FWR2)` gives

```text
||rho_n(J)-sigma_n(J')||_2->0.
```

Therefore `||rho_n(J)-I||_2->0` for every asymptotic representation of
`Gamma`.  Injectivity of `phi` and `J'!=1` give `J!=1`.  A hyperlinear
approximation would have to separate this nontrivial element, a contradiction.
