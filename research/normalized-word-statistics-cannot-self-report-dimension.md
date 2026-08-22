---
rg: 2
id: normalized-word-statistics-cannot-self-report-dimension
kind: claim
title: Normalized word statistics cannot make a finite approximation report its dimension
distinct_from:
  dimension-kleene-threshold-needs-amplification-envelope: that analyzes whether tensor amplification crosses a dimension-dependent defect threshold; this proves exact invariance under direct-sum amplification for every finite normalized word-statistic transcript.
  same-model-supercritical-clifford-trigger: that asks for a dimension-aware packet forcing more anticommuting observables than a model can carry; this shows why the dimension cannot be read from normalized group-word data in the first place.
  depthwise-canonical-kleene-needs-no-uniform-runtime-gap: that gives a positive reverse-Kleene criterion once fixed-depth estimates exist; this is a no-go for obtaining those estimates by finite-model introspection alone.
---

**ESTABLISHED.**  Fix a finite tuple of unitaries `U=(U_s)_(s in S)` in
`M_d(C)`.  For `k>=1` let

```text
U^(oplus k)_s=U_s direct-sum ... direct-sum U_s
```

in `M_(kd)(C)`.  For every group word `v`, every pair of words `v,z`, and
every relator packet `R`, normalized trace and normalized Hilbert--Schmidt
statistics satisfy

```text
tr_(kd)(v(U^(oplus k)))=tr_d(v(U)),                     (NSD1)
||v(U^(oplus k))-z(U^(oplus k))||_(2,kd)
 =||v(U)-z(U)||_(2,d),                                  (NSD2)
def_R(U^(oplus k))=def_R(U).                            (NSD3)
```

Therefore no decision rule whose input is a finite transcript of normalized
group-word traces and HS defects can distinguish dimension `d` from any
multiple `kd`.  In particular it cannot force an approximation to
"recognize its own dimension" and activate a challenge strictly beyond that
dimension while remaining sound under amplification.

## Proof

Word evaluation commutes with direct sums:

```text
v(U^(oplus k))=v(U)^(oplus k).                          (NSD4)
```

Normalized trace averages the `k` identical blocks, giving `(NSD1)`.  For
any `A in M_d(C)`,

```text
||A^(oplus k)||_(2,kd)^2
 =(1/(kd)) k Tr_d(A^*A)=||A||_(2,d)^2,                 (NSD5)
```

which proves `(NSD2)` and hence every standard sum, maximum, or average
relator defect identity `(NSD3)`.

The obstruction is semantic, not computational.  A Turing machine can read
a matrix encoding in an external search procedure, but an ordinary group
presentation sees only its represented unitaries and their relations.
Normalized-HS semantics deliberately quotients out spectator multiplicity,
so the dimension is not an intrinsic observable of that semantics.

This does not rule out self-reference.  It identifies its viable form:

```text
finite-model introspection of d                 impossible by these data;
proof-theoretic introspection of the compiler   compatible with reverse Kleene.
```

The latter is exactly the orientation of
`depthwise-canonical-kleene-needs-no-uniform-runtime-gap`: the compiler may
react to proofs about its own marked word, but for every fixed proof depth
its soundness estimate must already hold uniformly over all dimensions and
all canonical profiles.  Self-reference removes the need to know a runtime
modulus; it does not manufacture the missing dimension-free analytic
estimate.

