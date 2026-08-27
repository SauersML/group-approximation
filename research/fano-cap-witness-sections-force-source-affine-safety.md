---
rg: 2
id: fano-cap-witness-sections-force-source-affine-safety
kind: claim
title: A cap-supported Culf--Mastel witness section forces affine safety of the actual source support
distinct_from:
  fano-cap-range-sections-cannot-encode-nonaffine-relations: that assumes one section over every satisfying source assignment and concludes the whole source relation is affine; this uses only the assignments of positive trace in the actual HALT witness and obtains the exact affine-sandwich obstruction.
  culf-mastel-rstar-reduction-is-support-blind: that observes that the published maps state no cap conclusion; this extracts the strongest necessary condition on their actual completeness section.
  three-label-affine-lowering-no-go: that constructs a separate oracular source whose affine lowering is classically satisfiable; this applies context by context to the support of the specific source trace used in Theorem 6.8.
---

**ESTABLISHED SOURCE-SUPPORT OBSTRUCTION.**  Let one context of the
Culf--Mastel source BCS have satisfying relation `C subseteq F_2^V`, and let
`tau` be the perfect source trace used on a HALT instance.  Write

```text
S={phi in C:tau(P_phi)>0}.                                (FWS1)
```

Let a finite pp-gadget over `R_*` implement this context as in Corollary 6.7,
and choose, for every `phi in S`, one satisfying target witness `sigma(phi)`
extending `phi`.  If the local tuples seen by **every** `R_*` occurrence as
`phi` ranges over `S` form Fano caps after ghost translation, then

```text
Aff_F2(S) subseteq C.                                    (FWS2)
```

More precisely, the cap choice produces an affine relation `A` with

```text
S subseteq A subseteq C.                                 (FWS3)
```

Thus `(FWS2)` is a necessary condition for a cap-supported completeness lift,
regardless of how the witnesses in Corollary 6.7 are selected.

The same conclusion holds if the lifted trace splits a positive source atom
among several target witnesses rather than choosing a deterministic section.
Select one positive target witness below each positive source atom.  Its local
tuples lie in the already cap-supported target support, and the deterministic
argument applies.

This gives a concrete finite obstruction.  If a source context is the
positive one-in-three relation

```text
C=S={100,010,001}                                        (FWS4)
```

and all three source atoms have positive trace, then

```text
111=100+010+001 in Aff(S)\C.                             (FWS5)
```

No choice of witnesses in any exact `R_*` pp-reduction of that context can
make every target occurrence cap-supported.  The same obstruction applies to
any actual context support containing an odd subset whose xor is a forbidden
source assignment.

For the actual Culf--Mastel construction, Corollary 6.4 and Theorem 6.8 give
only perfectness, oracularizability, and constant answer size.  Their source
contexts are the answer sets `C_i=O_i` and accepted-pair sets `C_ij` of the
oracularized protocol.  None of the cited results states `(FWS2)` for the
positive answer or accepted-pair supports of the perfect strategy.  Constant
answer size makes the possible supports and witness sections finite and
enumerable; it does not exclude `(FWS5)`.

Consequently the sole Fano completeness gate can be moved exactly one step
backward:

```text
find a HALT perfect source trace whose every context support is
affine-safe inside the corresponding C_i.                (FWS6)
```

The published completeness construction does not prove `(FWS6)`.  A positive
proof must use additional structure of the particular Dong--Fu--Natarajan--
Qin--Xu--Yao perfect strategy; changing witness sections after Corollary 6.7
cannot repair an affine-unsafe source support.

