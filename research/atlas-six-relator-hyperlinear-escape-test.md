---
rg: 2
id: atlas-six-relator-hyperlinear-escape-test
kind: claim
title: The exact six-relator matrix-ultraproduct escape is exactly a bridge-retaining hyperlinear quotient
distinct_from:
  atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test: that treats exact finite-dimensional zeros and reduces them to finite quotients; this treats the genuinely dimension-moving tracial matrix-ultraproduct zero set and reduces it to hyperlinear quotients.
  atlas-five-row-blowup-branch-is-impossible: that eliminates vanishing additive-energy blow-ups; this classifies the remaining positive-energy exact branch group-theoretically.
  atlas-six-relator-leavitt-tracial-countermodel: that gives an exact model in a possibly non-Connes-embeddable factor; this characterizes exactly when such a model exists in a tracial matrix ultraproduct.
  hyperlinear-quotient-permanence-equivalence: that concerns closure of the class of all hyperlinear groups under arbitrary quotients; this is a fixed relative quotient criterion with two injected A8 charts and a fixed finite bridge menu.
  atlas-six-relator-nontrivial-quotients-inject-charts: that proves algebraically that every nontrivial quotient injects the two charts; this adds the CE regularization and fixed-bridge energy needed to identify ultraproduct escapes.
---

**ESTABLISHED.**  Put

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>.
```

Let `t_1,...,t_4` be the four fixed standard transvections generating
`H=diag(GL_3(2),1)<A8`, and put

```text
b_ell=i_2(t_ell)i_1(t_ell)^(-1) in Gamma_6.          (HUQ1)
```

The following are equivalent.

1. There is an exact common-orbit model of the six displayed relators in a
   tracial matrix ultraproduct, with both `A8` restrictions equal to their
   regular character.
2. `Gamma_6` has a nontrivial hyperlinear quotient.
3. There is a hyperlinear quotient

   ```text
   q:Gamma_6 -> Lambda
   ```

   which is injective on both marked `A8` factors and for which
   `q(b_ell)!=1` for at least one `ell`.

Every model in item 1 automatically has strictly positive five-row additive
energy.  Indeed the exact `19243` relation prevents all four words `(HUQ1)`
from vanishing, and `regular-atlas-linearized-h-coercivity` makes any
surviving bridge pay positive five-row energy.  Thus item 1 is exactly the
macroscopic alternative left by `atlas-five-row-blowup-branch-is-impossible`.

There is also one intrinsic positive group-algebra witness for this energy.
Write each fixed integral derivative row as

```text
z_j=sum_r epsilon_(j,r) g_(j,r) in Z[A8]
```

and put

```text
Z_j=sum_r epsilon_(j,r)
          i_1(g_(j,r))i_2(g_(j,r))^(-1) in C[Gamma_6],
h_5=sum_(j in {0,11,30,44,55}) Z_j^* Z_j.             (HUQ4)
```

For every regular common frame `pi_U`, right multiplication by `U^*` gives

```text
pi_U(Z_j)=(rho(z_j)U)U^*,
tau(pi_U(h_5))=sum_j ||rho(z_j)U||_2^2.               (HUQ5)
```

Here `rho(z_j)U` uses the conjugation-module action, so `(HUQ5)` is an
identity, not a scalarization of the operator row.

Let `T_reg(Gamma_6)` be the tracial states whose restrictions to both marked
finite factors are their regular characters, and let `T_reg^CE(Gamma_6)` be
the subset whose GNS von Neumann algebras are Connes embeddable.  The theorem
can therefore be restated as

```text
T_reg^CE(Gamma_6) is nonempty
 iff Gamma_6 has a nontrivial hyperlinear quotient,
```

and every trace in that CE locus satisfies `tau(h_5)>0`.  The qualitative
five-row endpoint is exactly

```text
T_reg^CE(Gamma_6)=empty.                              (HUQ6)
```

In contrast, the pullback of the canonical Leavitt trace belongs to
`T_reg(Gamma_6)` and is positive on `h_5`.  Thus `(HUQ6)` is a genuine
CE-versus-all-traces separation.  It cannot be proved by making `h_5` vanish
in the full tracial quotient.

Equivalently, the qualitative endpoint of
`atlas-five-row-operator-phase-lift` says

```text
every hyperlinear quotient of Gamma_6 is trivial.             (HUQ2)
```

The bridge formulation is deliberately retained in item 3: it gives the
fixed group-word witness.  On the regular character face it is actually
automatic once both factors inject, because exact `c_19243` and simultaneous
vanishing of the four bridges are incompatible.  Thus the apparently
operator-valued positive-energy exclusion is exactly a relative hyperlinear-
residual statement for this one finitely presented group.  The implication
`2 => 3` also uses
`atlas-six-relator-nontrivial-quotients-inject-charts`: every nontrivial
quotient injects both marked factors before hyperlinearity is invoked.

## Direct nonhyperlinear endpoint

The quotient `Gamma_6 -> Q=L_(F_2)(1,2)^x` injects both marked `A8` factors.
The two chart images in `Q` intersect trivially, so every nonidentity standard
transvection gives a fixed surviving bridge word.  Consequently

```text
atlas-five-row-operator-phase-lift
             => Gamma_6 is nonhyperlinear.             (HUQ3)
```

This endpoint does not need the separate canonical-Leavitt separating
refinement.  If `Gamma_6` were hyperlinear, its identity quotient would be
the quotient in item 2, hence would itself supply the forbidden exact
matrix-ultraproduct escape.
