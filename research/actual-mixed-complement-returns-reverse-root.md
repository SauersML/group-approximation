---
rg: 2
id: actual-mixed-complement-returns-reverse-root
kind: claim
title: The actual complementary mixed-braid occurrence returns a reverse constant root, not a support Whitehead
invalidates:
  - complementary-symmetric-whitehead-continues-mixed-braid-residual
artifacts:
  - experiments/mixed_braid_common_middle_return_audit.py
distinct_from:
  mixed-braid-gauge-cancellation-misses-signed-hecke-targets: that computes the correct residual matrix and its asymmetric three-root factorization; this compares it with the symmetric word used by the proposed complementary continuation and evaluates the actual complementary braid.
  complementary-mixed-braid-returns-support-but-retains-s3: that now scopes the symmetric support-cell identities and explicitly fences their use as the residual occurrence; this evaluates the true asymmetric complementary word and identifies its reverse-root output.
---

**ESTABLISHED OCCURRENCE CORRECTION.**  Retain the relative mixed-braid
word from `mixed-braid-gauge-cancellation-misses-signed-hecke-targets`:

```text
L=GK_0=x_89(r)P_1,
P_1=x_97(q_1)x_79(1)x_97(q_1)
   =[[q_0,1],[q_1,q_0]]_(7,9).                       (ACM1)
```

The word called `W_79(1,q_1)` in
`complementary-mixed-braid-returns-support-but-retains-s3` studies instead
the symmetric word

```text
S_1=x_97(1)x_79(q_1)x_97(1)
   =[[q_0,q_1],[q_1,q_0]]_(7,9).                     (ACM2)
```

Thus `P_1` and `S_1` differ in their `(7,9)` entry by the nonzero
idempotent `q_0`.  In particular neither `L=x_89(r)S_1` nor
`L=S_1x_89(r)` is true.  The support braid computed from `S_1` is an exact
identity for a different word, but it is not a continuation of the actual
mixed-braid occurrence.

The true complementary word is

```text
P_0=x_97(q_0)x_79(1)x_97(q_0)
   =[[q_1,1],[q_0,q_1]]_(7,9).                       (ACM3)
```

Faithful prefix-matrix multiplication gives

```text
P_1P_0P_1=P_0P_1P_0=x_97(1).                        (ACM4)
```

The output is the constant reverse root `7->9`.  It is not either support
Whitehead `W_79(q_i,q_i)`, and the exact ten-generator signed test shows

```text
x_97(1) notin Norm(L_0,lambda_0).                    (ACM5)
```

Consequently the advertised route from the exposed channel-nine word to
the support-return chart never occurs.  The `S_3` model in the independent
symmetric-cell claim is a model of the substituted symmetric table, not a
fence on the actual full-EL20 occurrence.  The real complementary braid
still misses the signed Hecke source at `(ACM5)` and supplies no route to
the native `J_1` target.  Thus this calculation closes one proposed
continuation of `el20-six-moving-coefficient-square-bridges`; it does not
establish any of `(ESB1)`--`(ESB3)` and does not retract that open claim.

The bare-root failure is not a failure of every longer continuation.
`reverse-mixed-root-has-two-positive-hecke-commutator-returns` uses the
literal `x_97(1)` occurrence in two positive-`L_0` commutators and obtains
the external signed normalizers `x_96(1)` and `x_27(1)`.  These are genuine
returns to the source carrier, but the native-orbit audit types both as
disjoint spectators, so neither supplies the missing native Gram or gauge
lock.

No Property `(T)`, Kazhdan input, trace hypothesis, literature theorem,
local computation, or Lean compilation is used.

DERIVATION
actual-mixed-complement-reverse-root-proof
