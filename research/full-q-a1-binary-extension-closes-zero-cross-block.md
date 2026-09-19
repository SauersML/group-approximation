---
rg: 2
id: full-q-a1-binary-extension-closes-zero-cross-block
kind: claim
title: The canonical binary A1 extension excludes the full-Q zero-cross block
artifacts:
  - research/full-q-a1-binary-extension-central-support-proof.md
  - experiments/full_q_a1_extension_compatible_cosets.cpp
  - experiments/full_q_outside_actor_order_audit.py
distinct_from:
  full-q-separate-actor-packet-retains-zero-cross-central-block: that constructs the exact zero block for P=<K,J1,J2,B2,B3>; this adjoins the first named source-normalizer root outside P and proves that the zero block cannot extend to its canonical binary action.
  row2-source-factor-detects-paid-pauli-sheet: that identifies A1 as a shortest signed-source-normalizer detector of the paid sheet but does not control its compression with the paid root; this uses the same one-root occurrence only to test central support of the native cross word in the finite full-Q chart.
  binary-leavitt-arbitrary-profile-native-cross-gram: that requires positivity in every finite-dimensional profile of the actual full group; this proves full central support only in one canonical finite binary extension and explicitly leaves other abstract extensions or profiles open.
---

**ESTABLISHED FINITE-EXTENSION EXCLUSION.**  In the exact binary
eight-summand chart, retain

```text
K=<L_0,r,l>,                 F=e_(K,chi),
g=J_1J_2,                    P=<K,J_1,J_2,B_2,B_3>.    (A1E1)
```

The zero-cross central block exists for `P`.  Adjoin the canonical binary
image of the already named common-source factor

```text
A_1=x_47(a_1),               a_1=s_1t_0,
bar(A_1)=x_(u1,q4)(1),
P_A=<P,bar(A_1)>.                                        (A1E2)
```

Then

```text
|P_A:P|=31,
|P_A|=20478689280.                                      (A1E3)
```

In particular `bar(A_1)` is genuinely outside `P`.  It is one ordinary
elementary root, hence has the minimum possible nonidentity ordinary-word
length among the named paid/source-factor candidates.

The exact `chi`-twisted double-coset audit for `P_A` gives

```text
[P_A:K]=624960,
K-double cosets=14528,
chi-compatible double cosets=176.                      (A1E4)
```

Thus `F C[P_A] F` has dimension `176`.  Exact signed-orbit multiplication,
reduced modulo the odd prime `1000003`, gives

```text
dim_<F_1000003>
  ((F C[P_A] F)(FgF)(F C[P_A] F))=176.                (A1E5)
```

Full rank modulo one prime implies full rank over the rationals: a
`176`-minor of the integral signed-orbit multiplication matrix is nonzero
modulo `1000003`, and therefore is a nonzero integer.  Hence `(A1E5)` proves
the exact complex identity

```text
F in (F C[P_A] F)(FgF)(F C[P_A] F).                   (A1E6)
```

Equivalently, `FgF` has full central support in the canonical finite
extension corner.  No simple `P`-block on which `F!=0` and `FgF=0` extends
to `P_A` with the displayed binary action of `A_1`.

This is a finite-extension fence, not the arbitrary-profile theorem.  A
representation of the actual Steinberg packet can attach a multiplicity
gauge to an occurrence of `A_1`; the present finite chart does not prove
that every such abstract extension factors through `P_A`, nor that its
twisted corner has the same `176`-dimensional algebra.  What it proves is
that the previously established zero block is not stable under the most
literal and shortest already-authenticated outside occurrence.  Any
remaining counterprofile must change the `A_1` extension data rather than
reuse the canonical binary chart unchanged.

No Property `(T)`, canonical trace, local computation, literature theorem,
or Lean compilation is used.  The finite audit was compiled and run once
through MSI.

DERIVATION
full-q-a1-binary-extension-central-support-proof
