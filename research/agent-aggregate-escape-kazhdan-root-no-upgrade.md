---
rg: 2
id: agent-aggregate-escape-kazhdan-root-no-upgrade
kind: claim
title: Kazhdan and relative-root rigidity do not robustify finite-dimensional root invisibility
distinct_from:
  agent-free-compressor-high-rank-stability-does-not-authenticate: That audits the normalized-versus-Frobenius norm mismatch and the complement gauge before the HNN row; this supplies a genuine normalized-HS asymptotic marked countermodel having property T, five-by-five root geometry, and exact local finite models.
  exact-fd-invisibility-has-no-general-hs-robustification: That uses a finitely presented sofic group without property T; this uses Thom's property-T five-by-five matrix group and isolates the remaining finite-presentation-plus-full-corner conjunction.
  agent-free-compressor-full-corner-root-is-fd-invisible: That proves exact finite-dimensional vanishing for the complete BCL presentation; this proves that its asymptotic upgrade cannot follow from property T, relative T, root torsion, or exact finite-window models alone.
---

There is a finitely generated property-`(T)` group `G`, realized from Thom's
five-by-five matrix group over `F_p[t,t^(-1)]`, and a central order-`p` root
element `j` such that

```text
rho(j)=1                         for every rho:G->U(d),       (KRR1)
```

but `G` has normalized-HS asymptotic representations `sigma_n` satisfying

```text
def_F(sigma_n)->0               on every fixed finite window F,
||sigma_n(j)-1||_(2,d_n)=sqrt(2).                           (KRR2)
```

Indeed `G` is LEF.  Choose an exhausting sequence of finite windows containing
`j` and exact partial embeddings into finite groups `H_n`, and compose with
the left regular representations of `H_n`.  Every fixed multiplication law
is eventually exact.  Since the partial embeddings keep `j` nonidentity, the
regular character gives

```text
tr(lambda_(H_n)(j))=0,
||lambda_(H_n)(j)-1||_2^2=2.                               (KRR3)
```

Thom's group has property `(T)`, hence it also has relative property `(T)`
with respect to every one of its root subgroups and has the robust
finite-dimensional spectral-gap property `(T;FD)_rob`.  Thus neither
ordinary Kazhdan gap nor its relative-root form can convert `(KRR1)` into a
dimension-normalized word-kill estimate.  The obstruction is not a
microscopic defect: the marked spectral projection has fixed positive trace
in `(KRR2)`.

This calibrates the complete BCL root theorem sharply.  For the finitely
presented rank-five group `G_BCL`, property `(T)` follows from the standard
Steinberg theorem for finitely generated coefficient rings.  It supplies a
uniform gap for almost-invariant vectors in the adjoint almost
representation, but it does **not** supply the missing operation

```text
root spectral support of x_12(P_f)
  -> physical projection carrying the named B_f action.      (KRR4)
```

Nor does the rank-five spare-index calculus do this: it makes the common
root kernel a two-sided coefficient ideal, an algebraic statement already
used by the exact proof.  It does not turn HS-small full-rank coordinate
errors into rank-small errors, and it does not make spectral supports of
orthogonal coefficient idempotents additive.

The two known counterexamples leave one conjunction genuinely open rather
than hiding it:

```text
Slofstra--Vidick: finite presentation + fd-invisible marked microstates,
                  but no property-T input;
Thom:             property T + five-by-five root geometry + exact LEF
                  windows + fd-invisible mark, but not finite presentation.
```

A finitely presented LEF example cannot fill the second line: every finitely
presented LEF group is residually finite, whereas `j` lies in the finite
residual.  Therefore the surviving BCL theorem must use the **simultaneous
finite full-corner relations**, not a general compactness upgrade of local
Kazhdan rigidity.

The minimal sufficient new statement is a direct local normalized-HS
stability estimate for the packet/HNN/corner subsystem as a whole:

```text
||rho(x_12(P_f))-1||_2^2
 <= C sum_(r in R_corner)||rho(r)-1||_2,                (KRR5)
```

or the equivalent authenticated-corner estimate of
`agent-free-compressor-authenticated-corner-pays-hs`.  Proving `(KRR5)` would
combine with `agent-free-compressor-full-corner-root-is-fd-invisible` and the
exact perfect tracial model to finish the nonhyperlinear endpoint.  Property
`(T)`, relative property `(T)`, and fixed root exponent alone do not prove it.

DERIVATION
agent-aggregate-escape-thom-countermodel-proof
