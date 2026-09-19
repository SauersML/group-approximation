---
rg: 2
id: tagged-shift-stabilizer-holonomy-proof
kind: route
title: Convert bounded pair-chart comparisons into finite endpoint holonomy sets
target: tagged-shift-stabilizer-normalization-has-unbounded-row-holonomy
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

For an ordered pair `(x,y)`, put

```text
h_0(x,y)=sigma_(0,x)^(-1)g_(x,y),
h_1(x,y)=sigma_(1,y)^(-1)g_(x,y).                        (TSHP1)
```

Equations `(TSH1)--(TSH2)` say that `h_ell(x,y)` centralizes `beta_ell`.
Concatenate the corresponding comparison in `(TSH3)` with the canonical
role-name comparison `(TSH1)`.  After conjugating by the role section, the
result is

```text
beta_ell (h_ell beta_ell h_ell^(-1))^(-1),              (TSHP2)
```

up to inversion and cyclic conjugation, neither of which changes area.
Thus `(TSH1)` and `(TSH3)` give the uniform bound
`Area_R([beta_ell,h_ell(x,y)])<=A+B`.

By `finite-mark-centralizer-commutator-area-is-proper`, for each `ell` the
elements `h_ell(x,y)` occupy only finitely many cosets modulo
`<beta_ell>`.  The latter subgroup is finite, so all the endpoint holonomies
range over fixed finite sets `K_0,K_1`.

Now fix `x`.  The two definitions in `(TSHP1)` give

```text
sigma_(1,y)
 =sigma_(0,x) h_0(x,y) h_1(x,y)^(-1).                  (TSHP3)
```

The right side has at most `|K_0||K_1|` possible group values.  By `(TSH1)`,
equal values of `sigma_(1,y)` give equal canonical row elements `c_y`.
Those elements are pairwise distinct, so every `x` has at most
`|K_0||K_1|` partners `y` with `(x,y) in P`.  This contradicts the assumed
unbounded out-degree.

If the proposed pair chart uses the canonical source section itself, then
`h_0=1`.  Formula `(TSHP3)` becomes even sharper: all target sections lie
in the one finite set `sigma_(0,x)K_1^(-1)`.  More generally, saying that a
further transporter fixes the source row only says that its source holonomy
centralizes `beta_0`; making that fix bounded-area or literal is precisely
the first estimate already covered above.  Hence source-row stabilization
cannot remove the target holonomy cost.
