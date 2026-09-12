---
rg: 2
id: one-kun-thom-compressor-is-relatively-embeddable
kind: claim
title: Every one-compressor Kun--Thom vertex inclusion is relatively embeddable
distinct_from:
  kt-q2-double-hyperlinear-iff-relative-embeddable: that is the equivalence for the full Kun--Thom vertex group G and leaves its relative embeddability open; this proves relative embeddability after restricting the vertex to any one positive monomial compressor subgroup
  kt-one-compressor-full-coset-action-is-sofic: that proves a permutation action is sofic; this uses that action to prove soficity of an amalgamated double and then relative embeddability of a von Neumann inclusion
  monomial-ascending-hnn-coset-action-sofic: that treats the distinguished ascending-HNN coset action abstractly; this identifies the double as a free generalized wreath product and obtains the operator-algebraic conclusion
---

Use the regular finite-field Kun--Thom data

```text
R_0=k[N^d],       R=k[Z^d],
Gamma=EL_r(R_0),  G=EL_r(R) rtimes SL_d(Z),
```

and let `A in SL_d(Z) intersect M_d(N)` be a proper monomial compressor.
Write `a=(1,A)` and `P_A=<Gamma,a><G`.  Thus

```text
a Gamma a^(-1) subsetneq Gamma
```

and `P_A` is the corresponding ascending HNN group.  Then:

1. The group double `P_A *_Gamma P_A` is sofic.
2. The tracial amalgamated free product

   ```text
   L(P_A) *_(L(Gamma)) L(P_A)
   = L(P_A *_Gamma P_A)
   ```

   is Connes embeddable.
3. The inclusion `L(Gamma) subset L(P_A)` is relatively embeddable over
   the scalars (`RE/C`) in the sense of Gao.

The algebraic mechanism is exact.  If `t_1,t_2` are the stable letters in
the two copies and `s=t_2^(-1)t_1`, then

```text
P_A *_Gamma P_A
  ~= <P_A,s | [s,Gamma]=1>
  ~= (*_(P_A/Gamma) Z) rtimes P_A.                         (OCR1)
```

The last group is the free generalized wreath product for the left coset
action `P_A action P_A/Gamma`.  That action is sofic, so the free-wreath
permanence theorem applies.

This is a sharp localization of the remaining obstruction.  Property (T),
strict one-sided compression, infinite index, and nonamenability of
`Gamma` do not prevent relative embeddability in any single compressor
direction.  Nothing here combines two distinct compressors: relative
embeddability is not known to survive the extra relations that make them
coherent inside the full vertex group `G`.  Thus this result does not settle
the full Kun--Thom double; it proves that any obstruction must use genuinely
multi-directional ambient data rather than only one ascending-HNN slice.

DERIVATION
free-lamp-double-and-sofic-action-proof
