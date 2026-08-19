---
rg: 2
id: strong-atiyah-torsion-free
kind: claim
title: The Strong Atiyah Conjecture for torsion-free groups
root: true
distinct_from:
  whitehead-vanishing-torsion-free: that is vanishing of a K_1 quotient of the integral group ring; this is integrality of von Neumann ranks of matrices over K[G]. Both are open conjectures about all torsion-free groups and both were attacked against this repository on 2026-08-17, but neither is known to imply the other.
  torsion-free-countable-non-mf: that asks for a torsion-free group failing an operator-algebraic approximation property; this asserts an exact arithmetic property of kernels of finite matrices. Section 7 of the audit records why no implication runs between them.
  linnell-skew-field-can-be-centrally-infinite: that is an established no-go about the structure of one Linnell skew field; this is the global conjecture. That claim constrains proofs of this one without deciding it.
  finite-torsion-free-pattern-realizable-finitely-presented: that realizes finite equation-and-inequation patterns inside finitely presented torsion-free groups, a combinatorial transplantation tool; this is an L^2-arithmetic conjecture about von Neumann ranks, and the audit records why transplanting a matrix does not transport a rank.
  hnn-torsion-theorem: that is torsion-freeness permanence for HNN extensions; this takes torsion-freeness as its hypothesis and conjectures integrality of von Neumann ranks. Neither mentions the other's subject.
  torsion-free-higman-embedding: that embeds recursively presented torsion-free groups in finitely presented ones and says nothing analytic; this is a conjecture about kernels of finite matrices over K[G]. The audit's Section 6 records that no presentation-level embedding preserves von Neumann kernel dimension, so that theorem cannot serve this one.
  whitehead-vanishing-finitely-presented-torsion-free: that is Whitehead vanishing restricted to finitely presented torsion-free groups; this is Atiyah integrality over all torsion-free groups. Both were attacked against this repository the same day and they share no invariant.
artifacts:
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

Let `G` be a countable torsion-free group, `N(G)` its group von Neumann
algebra and `U(G)` the affiliated operators.  For a subfield `K` of `C`, the
Strong Atiyah Conjecture over `K` says every finite matrix `A` over `K[G]`
has

    rk_{N(G)}(A) in Z,     equivalently   dim_{N(G)} ker A in Z.

By **Linnell's theorem** this is equivalent to the division closure
`D_K(G)` of `K[G]` in `U(G)` being a **division ring**.  A positive answer
for torsion-free `G` implies Kaplansky's zero-divisor conjecture in
characteristic zero: `K[G]` is a domain.

Open in general.  Verbatim from Fisher--Ng (arXiv:2606.19606, Section 1.1,
read from source 2026-08-17): the question "has been reformulated into the
following open problem known as the Strong Atiyah Conjecture", and it is
"known for many classes of groups, including all locally indicable groups,
braid groups, elementary amenable groups, virtually compact special groups,
and 3-manifold groups".

## Why it is a root of *this* graph

Same reason as `whitehead-vanishing-torsion-free`, and on the same day: an
external resolution attempt was run against this repository's
compression--centralizer machinery.  It produced no proof and no
counterexample, but it produced something that outlasts most attempts -- a
**refuted bridge**, plus the exact extension of the repository's own theorem.
The durable results are `compression-defect-dies-in-weakly-locally-finite-division-rings`
and `linnell-skew-field-can-be-centrally-infinite`.

The word "Atiyah" did not occur anywhere in this tree before that audit.

## What a certificate must contain

*Positive.*  For every torsion-free `G`, that `D_K(G)` is a division ring;
equivalently that every nonzero element of the division closure has zero von
Neumann kernel.

*Negative.*  Explicit torsion-free `G` and `A in M_{m,n}(K[G])` with a proof
that `dim_{N(G)} ker A` is not an integer; or explicit nonzero `a, b` in
`K[G]` with `ab = 0`, which would also refute Kaplansky.

This repository produces group words invisible to selected classes of finite
models.  It does not convert one into a matrix over `K[G]` with a computed
non-integer kernel dimension, and the audit explains at each route why not.

## Attempts

Six, all against this repository's machinery, all with an identified stopping
point.  The audit artifact traces each.

1. **Extend the finite-dimensional sterility theorem to division rings.**
   Got as far as weakly locally finite division rings
   (`compression-defect-dies-in-weakly-locally-finite-division-rings`) and
   then *died at a refutation, not a gap*:
   `linnell-skew-field-can-be-centrally-infinite` exhibits a torsion-free
   elementary amenable group with nontrivial defect that satisfies Strong
   Atiyah, whose Linnell skew field is not weakly locally finite.  The bridge
   is false, not merely unproved.
2. **Treat a skew field as one-dimensional over itself.**  *Dies* on scalars:
   the commutant of a subset of `D` is not a `D`-subspace, only a vector space
   over a central subfield, and finite dimension over the center is exactly
   the hypothesis attempt 1 shows cannot be assumed.
3. **Use the property-`(TT)` Leavitt machinery.**  *Dies* twice over. The
   repository's `HasSingleSandwichDivision` says every nonzero `a` has
   `xay = 1`, which holds in division rings *and* in properly infinite simple
   rings, so it is not skew-field control; and by
   `division-ring-hosts-no-binary-leavitt-family` a division ring hosts no
   Leavitt family at all.
4. **Property `(T)`, nonsoficity, non-MF as the missing bridge.**  *Dies* as
   a matter of label versus content.  Torsion-free finite-index subgroups of
   `Out(F_n)` have property `(T)` and satisfy Strong Atiyah (Fisher--Ng), so
   `(T)` alone cannot force failure; and approximation properties output no
   matrix, no kernel projection and no trace.
5. **Reconstruct a finite factor, or use the faithful reduced trace.**  *Dies*
   by circularity and by weakness respectively: every countable `G` embeds in
   `U(N(G))` with `N(G)` finite, so no theorem can reconstruct a properly
   infinite Leavitt ring from an arbitrary homomorphism into a finite von
   Neumann algebra; and faithfulness of the canonical trace forbids proper
   isometries without making kernel dimensions integers.  For infinite `P` the
   Kazhdan projection maps to zero in the left regular representation, so the
   repository's proper-projection compression never reaches `N(G)`.  The
   circularity is already recorded in `notes/NOTEPAD.md`.
6. **Import an exotic `L^2`-Betti value.**  *Dies* at torsion and finiteness:
   the known irrational-value constructions have torsion subgroups of
   unbounded order, Fournier-Facio--Sauer's groups are torsion-free only for
   integer values, and a group `L^2`-Betti number without `FP`-finiteness is
   not the kernel dimension of one finite matrix.  A transfer would need an
   explicit identity `dim ker Atilde = dim ker A` across a torsion-free
   replacement, which no presentation-level embedding theorem supplies.
