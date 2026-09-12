---
rg: 2
id: bcs-gap-compression-is-the-groupifier
kind: claim
title: Compressing the non-CE BCS gap into one active fiber is already the missing groupifier
distinct_from:
  corner-localized-non-ce-bcs-energy-gap: That supplies the lower bound for star-polynomial BCS residuals on any reducing corner; this identifies the additional comparison to ordinary group-word energy and proves that it is already terminal.
  payload-conditioned-btb-active-fiber-floor: That asks directly for an ordinary-relator floor on one BTB fiber; this audits the proposed way of deriving that floor by nesting or reusing the source BCS gap.
  wagon-wheel-stops-before-bcs-groupification: That states a whole-carrier pre-wagon decoder; this gives the corner-compressed version and shows why the later phase cycle becomes unnecessary once it is available.
---

**ESTABLISHED EQUIVALENCE/CIRCULARITY TEST.**  Let `B` be the fixed shared
non-CE BCS, let `R_B` be its involution, context-commutator, and forbidden
star-polynomial residuals, and let `F` be a matrix-decoded projection.  Put

```text
E_B(Z;F)=sum_x ||[F,Z_x]||_2^2
          +sum_(R in R_B)||R(Z)F||_2^2.                (BCF1)
```

The corner-localized BCS theorem gives

```text
E_B(Z;F)>=beta_B tr(F).                                (BCF2)
```

Suppose a finite ordinary presentation, after its fixed packet correction,
actually compresses this gap into its active multiplicity rows in the only
useful quantitative sense:

```text
E_B(Z;F)<=C E_pres+o(1),                               (BCF3)
tr(F)>=c ||rho(J)-1||_2^2-o(1),                        (BCF4)
```

with `C,c>0` independent of matrix dimension, while an exact finite-tracial
model keeps `J!=1` and has `F=0`.  Then the presentation is already a complete
nonhyperlinearity witness, without a phase cycle, self-copy, or proper-corner
backend.  Indeed `(BCF2)--(BCF4)` give

```text
E_pres>= (beta_B c/C)||rho(J)-1||_2^2-o(1).            (BCF5)
```

Thus canonical microstates cannot keep `J` separated, while the exact
tracial model proves `J` nontrivial.

Conversely, merely placing a fresh copy of the BCS variables on the active
multiplicity space gives only `(BCF2)`.  Unless their star-polynomial
residuals are bounded above by the defects of **ordinary group words** as in
`(BCF3)`, the inequality contains no term from the group presentation and
does not imply an active typed floor.  Independent finite packet/context
charts do not prove `(BCF3)` because they lose the shared-variable corner;
finite Reynolds selectors name the forbidden projections but turn their
mass into fixed-space mass, not word defect.

Hence reusing the source non-CE gap on a selected phase fiber has exactly two
outcomes:

```text
no ordinary-word comparison (BCF3)  => no information about E_act,
comparison (BCF3) proved            => the full groupification is complete. (BCF6)
```

In particular the non-CE gap cannot be treated as an independent black-box
proof of `(PAT7)`.  The missing theorem is precisely the compressed
shared-BCS-to-word estimate `(BCF3)`.  Steinberg/root wordization of formal
coefficient identities does not automatically provide it for arbitrary
unitary microstates: identifying the physical fiber with the intended root
spectral support is the same decoder in different syntax.

DERIVATION
bcs-gap-compression-terminal-proof
