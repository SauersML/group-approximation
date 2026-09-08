---
rg: 2
id: ck-envelope-has-a-finitely-normally-generated-maximal-kernel
kind: claim
title: The finitely presented normal-generator envelope has a maximal proper normal subgroup that is finitely normally generated
distinct_from:
  finite-infranormal-subgroup-is-normal: that is the elementary fact that a FINITE infranormal subgroup is normal, about conjugation preserving cardinality; this asks for a finite NORMAL GENERATING SET of a maximal normal subgroup, which is a condition on generating data rather than on the subgroup's size -- the kernel here is expected to be infinite.
  fp-quotient-iff-kernel-finitely-normally-generated: that is the general equivalence between finite presentability of a quotient and finite normal generation of its kernel, true for every finitely presented group; this asserts that one particular class of envelopes actually HAS such a kernel at a maximal element, which is the open existence statement the equivalence turns the conjecture into.
  boone-normal-closure-of-t-finitely-generated: that concerns the Boone HNN tower and finite generation of a normal closure AS A SUBGROUP; this concerns finite NORMAL generation of a maximal normal subgroup of an elementary matrix group, a different group, a different construction and a strictly weaker finiteness condition.
  every-nontrivial-core-element-normally-generates-the-envelope: that records how rigid the envelope is -- perfect, no finite quotients, every core element a normal generator; this asks for a compactness property of its normal lattice, and the audit found no implication from the rigidity clauses to this one.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `S` be a finitely generated computably presented infinite simple group,
`1 != s in S`, and let `Gamma` be a finitely presented group containing `S`
with `Gamma = <<s>>_Gamma`, as supplied by
`chatterji-kassabov-normal-generator-embedding`.  Then `Gamma` has at least
one maximal proper normal subgroup `M` that is finitely normally generated in
`Gamma`.

Open.  This is the entire remaining content of
`boone-higman-via-ck-maximal-kernel`, and by
`fp-quotient-iff-kernel-finitely-normally-generated`
it is equivalent to: **some** maximal proper normal quotient of `Gamma` is
finitely presented.

## Why this and not the conjecture

By `proper-normal-subgroups-miss-the-normally-generating-core` every maximal
proper normal quotient of `Gamma` is simple and contains `S`, hence contains
the original group.  So there is no work left in the *embedding* — only in
the *presentation*.  The quantifier is existential over maximal normal
subgroups and over the freedom in the construction, which is why this is not
a restatement of the conjecture: it is a question about the normal lattice of
a specific, explicitly presented matrix group.

The coefficient ring can be the explicit finitely presented ring

    U = Z[G~]<p,q>/(p(1-g)q - 1).

**September 8 correction:** this does not establish finite presentation
of `EL_4(U)`. The verified finite-presentation theorem applies to
`St_4(U)`. By [[ck-steinberg-marked-cover]], one can use a finitely
presented marked quotient `Gamma` of `St_4(U)` mapping onto `EL_4(U)`.
The covering kernel remains uncontrolled. This open claim concerns the
finitely presented cover; its normal subgroups must not be identified
with the normal subgroups of the elementary image without an additional
argument.

## Attempts

1. **Zorn restricted to the finitely normally generated proper normals.**
   *Dies on chains.*  The union of an ascending chain of finitely normally
   generated normal subgroups need not be finitely normally generated, so the
   restricted poset has no upper bounds and Zorn does not apply.  Finite
   generation of `Gamma` gives properness of the union (that is the argument
   in `proper-normal-subgroups-miss-the-normally-generating-core-proof`) and
   nothing more.  A Max-n condition on the normal lattice would rescue it;
   none is known for these groups.
2. **Derive it from property (T).**  *Dies as a general normal-Noetherianity
   principle.*  `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels` gives
   one torsion-free finitely presented word-hyperbolic property-`(T)` group
   with continuum many maximal normal subgroups that are not finitely normally
   generated.  Thus property `(T)` does not imply `Max-n`, even with those
   additional hypotheses.  This does not refute the existential claim for
   the special elementary-matrix envelope: a successful proof must use that
   envelope's matrix/ring structure or select one special quotient.
3. **Derive it from the rigidity already proved.**  *No implication found.*
   `every-nontrivial-core-element-normally-generates-the-envelope` makes the
   envelope perfect with every proper quotient infinite and no nontrivial
   finite quotient.  All of that is non-existence of *small* quotients; this
   claim is compactness of *some* maximal kernel.  A group with no small
   quotients can still have every maximal normal subgroup infinitely normally
   generated, and nothing found here excludes it.
4. **Weaken to an effective maximal kernel** — ask only that `M` be
   recursively enumerable as a normal subgroup.  *Unsolved and strictly
   easier*; it would give a finitely generated computably presented simple
   quotient with decidable word problem, not a finitely presented one.  The
   effective-Zorn construction needs to decide `<<M, x>> ∩ S = 1`, and the
   clean criterion "proper iff misses `S`" is not effective in the direction
   required.  Recorded here rather than as a node because it is a different
   target, not a route into this one.
5. **Transfer every maximal kernel to the matrix image.** The exact
   alternative is [[ck-cover-quotient-kernel-dichotomy]]. A maximal kernel
   either contains the covering kernel and descends to a proper matrix
   kernel, or maps onto the whole matrix group while the covering kernel
   surjects onto the simple quotient. The second case cannot be excluded
   by assuming stable K_2 properties for the unstable kernel. Neither
   branch currently supplies finite normal generators for the maximal
   kernel upstairs.
