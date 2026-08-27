---
rg: 2
id: two-site-a5-center-has-exact-boundary-countermodel
kind: claim
title: A finite canonical A5 packet has exact two-site boundary interference
distinct_from:
  bernoulli-center-measurement-retains-boundary-interference: that computes the one-site defect in the canonical infinite wreath trace; this gives a finite-dimensional regular representation, uses the full marked pair, and satisfies all actor character tests exactly.
  two-site-a5-plancherel-center-separates-mark: that produces the positive exclusive-or carrier and its covariance; this proves those same fixed center data do not make the compressed actor couplings multiplicative.
  finite-cylinder-mixed-traces-kill-normalizer-holonomy: that classicalizes an invariant finite PVM under an exact finite actor table; this countermodel's measured two-site PVM is not invariant and proves that invariance cannot be replaced by a fixed shared-conjugation identity.
---

**ESTABLISHED EXACT MATRIX COUNTERMODEL TO FIXED-PAIR
CLASSICALIZATION.**  Let

```text
Y={p,q,r,s},       B=A5^Y,
H=<g | g^2=1>,     g:(p q r s) |-> (r s p q).          (ABC1)
```

Thus `g` sends the marked pair `{p,q}` to the disjoint pair `{r,s}` and
back.  On

```text
V=ell^2(B) tensor ell^2(H)                             (ABC2)
```

represent `B` by its left regular representation on the first factor and
put

```text
U_g=P_g tensor lambda_H(g),                            (ABC3)
```

where `P_g delta_b=delta_(g.b)`.  This is the left regular representation
of the finite semidirect product `B semidirect H`: for `b!=1` the lamp trace
vanishes, and for every `b`, the trace of
`lambda_B(b)P_g tensor lambda_H(g)` vanishes because the second factor has
zero trace.  Hence every group relator and every canonical mixed group-word
trace is exact.

Let `z` be the rational five-dimensional central idempotent of `A5`, put

```text
a=tau(z)=5/12,                 mu=(1-a,a),              (ABC4)
```

and let `(P_omega)_(omega in {0,1}^2)` be the four-atom center PVM of
`(z_p,z_q)`.  Its law is

```text
nu=mu tensor mu.                                         (ABC5)
```

The marked exclusive-or atom has the required canonical mass
`2a(1-a)=35/72`.  All central-idempotent character identities are literal,
and `(ABC3)` gives exact shared conjugation of both lamp coordinates.

Nevertheless the block-mass coupling of `U_g` on this fixed marked PVM is

```text
C_g=nu tensor nu,                                      (ABC6)
```

because the source labels on `{p,q}` and the transported labels on `{r,s}`
are independent in the regular lamp packet.  The same holds for `g^(-1)=g`.
Sequential composition relative to `nu` therefore remains `nu tensor nu`,
whereas the identity coupling is `Diag(nu)`.  Consequently

```text
||C_g o_nu C_g-Diag(nu)||_TV
 =1-sum_omega nu(omega)^2
 =1-(a^2+(1-a)^2)^2
 =3815/5184.                                           (ABC7)
```

The defect in `(ABC7)` occurs at zero normalized-Hilbert--Schmidt
presentation defect in a finite matrix algebra carrying the canonical group
character.  Thus no dimension-free lemma can derive an equivariant
multiplicity table, or even inverse multiplicativity of the compressed
block-mass table, from a fixed two-site `A5` central-character identity plus
shared conjugation.

This does not refute `two-site-a5-center-classicalization` itself.  If the
state space retains the labels on all four sites, `g` is already a literal
permutation and the full PVM is invariant.  The countermodel proves exactly
what extra datum a positive proof must carry: actor-path/boundary memory, or
an independently extracted coherent finite actor table.  Repeating another
fixed central identity without enlarging the transported state cannot
supply that memory.

DERIVATION
two-site-a5-finite-boundary-countermodel-proof

