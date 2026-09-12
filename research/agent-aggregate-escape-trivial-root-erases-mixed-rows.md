---
rg: 2
id: agent-aggregate-escape-trivial-root-erases-mixed-rows
kind: claim
title: A boundedly trivial payload root eliminates every mixed coupling to a root-free quotient row
distinct_from:
  agent-free-compressor-padded-j-row-kills-payload-root: That gives a bounded derivation of the identity for the padded BCL root; this proves that adjoining mixed rows through that root cannot authenticate a physical payload and reduces them to root-free rows.
  root-scaling-covariance-does-not-detect-bcs-atom: That gives a trivial-root counterrepresentation for covariance rows; this treats arbitrary finite words containing a root already trivial in the presented group and gives a quantitative HS substitution theorem.
  forbidden-character-kernel-quotient-compiler: That gives a sufficient packet quotient when its perfect-model kernel separates all forbidden characters; this proves that any successful coupling through a boundedly trivial root is already such a root-free quotient mechanism.
---

Let

```text
G_0=<S | R>
```

be a finite presentation and let `w in F(S)` have a derivation of `w=1`
using at most `D` conjugates of defining relators.  Adjoin finitely many
generators `Y` and mixed relators

```text
r_j=r_j(S,Y,w),                    1<=j<=m.             (BTR1)
```

Let `bar r_j=r_j(S,Y,1)` be obtained by replacing every occurrence of
`w^(plus_or_minus 1)` by the empty word.  Then

```text
<S,Y | R,r_1,...,r_m>
  congruent <S,Y | R,bar r_1,...,bar r_m>.             (BTR2)
```

This is a Tietze equivalence fixing every generator in `S union Y`.  Hence a
mixed relation through a root which is already the identity cannot encode a
conditional payload.  It is exactly its root-free residue.

The equivalence is dimension-uniform in normalized Hilbert--Schmidt norm.
For a unitary tuple `rho`, let

```text
delta_R=max_(r in R) ||rho(r)-1||_2.
```

The bounded derivation gives

```text
||rho(w)-1||_2 <= D delta_R.                           (BTR3)
```

If `nu_j` is the number of occurrences of `w^(plus_or_minus 1)` in the
displayed word `(BTR1)`, telescoping unitary products gives

```text
||rho(r_j)-rho(bar r_j)||_2
 <=nu_j ||rho(w)-1||_2
 <=nu_j D delta_R.                                    (BTR4)
```

Consequently the two finite presentations in `(BTR2)` have Lipschitz-
equivalent normalized-HS defect functions, with constants depending only on
the fixed words and not on matrix dimension.

Apply this to the padded BCL root

```text
w=x_ij(P).
```

`agent-free-compressor-padded-j-row-kills-payload-root` supplies precisely
the bounded derivation required in `(BTR3)`.  Therefore every proposed finite
ordinary-group row intended to transfer physical forbidden mass to
nontrivial spectrum of `x_ij(P)` reduces to a row in which that root has been
deleted.

The same conclusion applies without the padding when all complete BCL corner
rows are imposed.  `agent-free-compressor-bcl-root-is-abstractly-zero` proves
that their selected coefficient idempotent is already zero in the presented
ring, so its root again has a fixed derivation of the identity.  Thus neither
version of the fully identified BCL root can be the nontrivial side of a
payload detector.

There is an exact dichotomy.

1. If the root-free residues `bar r_j` admit an exact finite-dimensional
   representation whose physical forbidden projection has positive trace,
   then the same representation, with `w=1`, is an exact countermodel to any
   estimate

   ```text
   tau(q_phys)<=C(E_pres+||rho(w)-1||_2^2).             (BTR5)
   ```

2. If the residues exclude every such representation while retaining the
   chosen perfect tracial representation, then the exclusion is caused
   entirely by the root-free quotient presentation.  The killed Steinberg
   root is dispensable.  On a finite context packet this is exactly the kind
   of perfect-kernel separation isolated by
   `forbidden-character-kernel-quotient-compiler`.

Thus the padded `J` row closes root killing but simultaneously makes the
payload-to-root formulation unavailable: an algebraically killed word cannot
acquire positive spectrum.  The remaining problem is not to couple physical
mass to that root.  It is to find a finite root-free quotient which preserves
the non-Connes-embeddable perfect trace and annihilates every forbidden local
character, or to use a payload word which is not already trivial in the
abstract group.

DERIVATION
agent-aggregate-escape-trivial-root-substitution-proof
