# The certified atlas package has phase-preserving (A_8) quotients

Date: 2026-08-11

> **Status.** This noncentral quotient is retained as the exact precursor to
> `FALSE_ATLAS_DUAL_NUMBER_CENTRAL_QUOTIENT.md`, which kills the same 24
> certified classes while making `r_11` the unique nontrivial central
> involution.  The “next target” below is therefore historical.

## Result

Let

\[
P=A_8*A_8
\]

be the two-chart atlas group.  The complete radius-five boundary contains
234 Leavitt relations.  Perfect-overlap certificates prove that 178 of them
vanish in the relation module (R/[P,R]); under cyclic conjugacy and
inversion they reduce to 24 representatives.  Let (Z_5\triangleleft P) be
the normal closure of those 178 certified relations, equivalently of the 24
representatives.

**Theorem.** The survivor relation (r_{11}) is not in (Z_5).  In fact
there are homomorphisms

\[
\phi:P/Z_5\longrightarrow A_8
\]

such that (phi(r_{11})) is a nonidentity involution.

Among the complete set of relative automorphism alignments of the two
factors, exactly 26 kill all 24 representatives.  Eight of the 14 inner
alignments and all 12 outer alignments retain (r_{11}), for 20 explicit
phase-preserving quotients.

This is stronger than the local (S_4*S_4) certificate: all currently
proved-zero radius-five relations can be imposed simultaneously, both local
maps extend to the full ambient (A_8) charts, and the phase still survives.

## Exhaustion of homomorphisms to (A_8)

Because (A_8) is simple, the restriction of a homomorphism
(A_8*A_8\to A_8) to either factor is trivial or an automorphism.  If both
restrictions are nontrivial, postcomposition lets us fix the first one as the
identity.  The second restriction then ranges over all of

\[
\operatorname{Aut}(A_8).
\]

In the atlas coordinates (A_8\cong\operatorname{GL}_4(mathbb F _2)), every
automorphism is either inner or inner after

\[
\theta(g)=(g^{-1})^{\mathsf T}.                     \tag{1}
\]

Thus it suffices to enumerate the 20,160 maps

\[
g_1\mapsto g,\qquad g_2\mapsto hgh^{-1}
\]

and the 20,160 maps

\[
g_1\mapsto g,\qquad g_2\mapsto h\theta(g)h^{-1},   \tag{2}
\]

with (h\in\operatorname{GL}_4(mathbb F _2)).  Exact (mathbb F _2)
evaluation gives:

| relative alignment | kills all 24 classes | also preserves (r_{11}\neq1) |
|---|---:|---:|
| inner | 14 | 8 |
| outer | 12 | 12 |
| total | 26 | 20 |

Neither one-factor map kills all 24 representatives, and the map trivial on
both factors kills the phase.  The enumeration therefore also exhausts all
homomorphisms (P\to A_8), up to postcomposition, relevant to the claim.

## One explicit certificate

Take the outer alignment `(2)` with

```text
h = 00000100010000000001000000000001
```

in row-major (mathbb F _2) matrix encoding.  Direct multiplication sends
each representative with boundary index

```text
0, 2, 10, 13, 16, 17, 35, 50, 65, 68, 70, 72,
80, 86, 90, 91, 114, 125, 126, 127, 218, 221, 224, 227
```

to the identity, while

```text
r_11 -> 01000100000101000000010000000001,
```

an element of order two.  Every one of the 178 certified relations is a
cyclic conjugate or inverse of one of the 24 representatives, so it is also
killed.  If (r_{11}\in Z_5), every homomorphism killing the normal
generators of (Z_5) would kill (r_{11}), contradicting this certificate.

## Exact scope

The theorem proves that the entire current perfect-overlap package does not
normally generate class `11`.  It does **not** yet prove that class `11` is
nonzero in (R/[P,R]).  In the displayed (A_8) quotient its image is not
central—(A_8) has trivial center—whereas passage from (R) to (R/[P,R])
imposes commutation with every element of (P).  Additional Leavitt
relations outside the radius-five certified package may force the class to
vanish after centralization.

The result nevertheless closes two tempting no-go strategies:

1. the four numerically stubborn relations do not kill the phase even in
   their local (S_4*S_4);
2. adding all other currently certified-zero classes and requiring full
   (A_8)-chart extensions still does not kill it.

The next finite target must therefore incorporate centrality of the phase
alongside the 24 zero classes, or discover new certified-zero relations
outside this boundary which eliminate all 20 finite witnesses.

## Reproduction

```text
python3 experiments/atlas_certified_a8_alignment.py
```

The script reconstructs the complete collision boundary, tests the two
one-factor cases, enumerates all 40,320 automorphisms using exact
(mathbb F _2) arithmetic, and prints every solution and phase image.
