---
rg: 2
id: complementary-mixed-braid-returns-support-but-retains-s3
kind: claim
title: The complementary mixed-braid cell returns a support Whitehead but retains an S3 gauge
artifacts:
  - experiments/complementary_partial_whitehead_braid_audit.py
  - experiments/complementary_support_native_parity_audit.py
  - research/complementary-mixed-braid-support-return-proof.md
distinct_from:
  mixed-braid-gauge-cancellation-misses-signed-hecke-targets: that stops after the exposed partial Whitehead fails both signed Hecke targets; this adjoins its complementary idempotent cell and computes the resulting support returns.
  support-return-gives-gauged-native-loop: that uses the support Whitehead W_79(q_0,q_0) to return the native coefficient arms; this identifies that same literal word as the output of the complementary mixed braid and audits the remaining gauge.
---

**ESTABLISHED POSITIVE RETURN WITH AN S3 FENCE.**  Let

```text
A=W_79(1,q_1),                 B=W_79(1,q_0),
C=W_79(q_0,q_0),               D=W_79(q_1,q_1),
F=W_79(1,1),                   q_0+q_1=1.             (CMR1)
```

Here `A` is exactly the partial Whitehead left after the visible
`x_89(r)` factor is removed from the mixed-braid comparison word.  Direct
binary-Leavitt matrix multiplication gives

```text
ABA=C,                 BAB=D,                 CD=F.   (CMR2)
```

Thus the first complementary continuation really does return the exposed
channel-nine occurrence to a support-idempotent Whitehead.  In particular
`C` is the literal `W_1=W_79(e_0,e_0)` used by
`support-return-gives-gauged-native-loop`; this is an occurrence-level
connection, not an analytic replacement.

The connection does not authenticate the gauge of `A`.  The complete table
`(CMR2)`, the support-return identity

```text
J_1=C Khat_1 C,
```

and the factorization of `C,D,F` admit the exact reservoir assignment

```text
a=(1 2),             b=(2 3),
c=aba=(1 3),         d=bab=(1 3),             f=cd=1. (CMR3)
```

Every displayed relation is satisfied in `S_3`, while `a` and `b` remain
nontrivial and `ab` has order three.  The two occurrences of `C` in the
native support-return identity cancel its reservoir factor.  Hence the new
cell types the complementary factor and the support output, but it does not
force the original mixed-braid spectator `a` to be trivial or identify it
with the native Whitehead gauge on a signed Hecke carrier.

Exact full-signature tests give an additional carrier fence: none of
`A,B,AB,BA,C,D,F` preserves the signed Hecke projection `Q`.  Therefore
`(CMR2)` is not itself an `(ESB1)` bridge.  A successful continuation must
add a relation which returns this `S_3` packet to `Q` (or its native target)
with an incompatible gauge equation; repeating the complementary braid or
the existing support-return loop cannot do so.

This remains true after closing **all** exact relations with the native
Whitehead.  Faithful matrix closure gives

```text
H=<A,B,J_1>,                    |H|=12.                (CMR4)
```

The parity which is odd on `A` and even on `B,J_1` is a well-defined
character `H->C_2`; exhaustive equality testing finds no parity collision.
Moreover the only element of `H` which preserves the signed Hecke pair is
the identity, and the only element carrying `Q` to `J_1QJ_1^(-1)` is
`J_1` itself.  Both have even `A` parity.  Hence **no word at all** in the
complementary/native subgroup supplies the missing odd Hecke bridge.  The
next occurrence must leave `H`, rather than use a longer recombination of
the three available words.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
complementary-mixed-braid-support-return-proof
