---
rg: 2
id: mf-safe-asymmetric-hnn-replacement
kind: claim
title: Replace an effective asymmetric HNN identification by MF-safe finite-presentation moves
root: true
artifacts:
  - research/artifacts/fp-mf-pi2-compiler-audit-2026-08-25.md
  - research/coordinate-swap-rope-does-not-compress-kernel.md
distinct_from:
  symmetric-double-weak-mf: that handles two identical copies and one common subalgebra; this must simulate two different embeddings used by effective Higman compilation.
  hnn-extension-finite-presentation-permanence: that preserves finite presentability, not the MF property.
---

**ESTABLISHED in the special form required by the Higman rope.**  The
Mikhailova compiler gives a regular-MF pre-rope benign witness, the finite-CEP
graph factor gives exact finite edge conjugacies, and tensor synchronization
makes the final asymmetric graph HNN regularly operator-MF.  This is not a
generic permanence theorem for arbitrary asymmetric HNN extensions.

## Attempts

Replacing the HNN step by a symmetric double works only when the two embeddings
agree up to the available symmetry; the general effective identification does
not have that form.

The full Higman compiler does not in fact require arbitrary HNN permanence.
After the countable-to-finitely-generated bridge, the last rope edge has the
special form

```text
< Gamma times Q, u |
  u (s,1) u^-1 = (s,tau(s)),  s in S >,              (GH1)
```

where `S = F *_N F` is the symmetric double occurring inside the benign
witness, `Q=F/N`, and `tau:S->Q` is the quotient map on the first copy and is
trivial on the second.  Thus both edge embeddings retain the same faithful
`Gamma` coordinate; only a graph-valued `Q` coordinate changes.  Proving MF
permanence for `(GH1)` in the rope situation is sufficient and is strictly
narrower than the claim's original generic formulation.

- **Shulman's symmetric double does not apply.**  In arXiv:2603.13564v2 the
  notation `A *_C A` explicitly means that the two copies use the identical
  inclusion of `C`.  Theorem 10 therefore does not cover the two embeddings in
  `(GH1)`.  The general criterion (body Theorem 16 in v2) asks for compatible
  matrix-corona embeddings; it does not manufacture them from MF of the two
  vertex algebras.
- **The trivial-quotient specialization is central but unavailable.**  If
  `Q=1`, then `(GH1)` is a central HNN and Shulman's Theorem 25 applies.  The
  recursive FIN switch is countably generated, however.  Every effective
  countable-to-finitely-generated bridge leaves a nontrivial finitely generated
  scaffold on the branch where the switch group itself collapses.  In the
  explicit HNN bridge this scaffold is the central HNN of `F_2` over
  `<x^-i y x^i : i>=0>`, so `Q` is MF but not trivial.
- **Finite-generation compactness rules out killing the scaffold by a
  monotone relator stream.**  In a finitely generated group, if an increasing
  union of normal closures contains every member of one finite generating
  set, one finite stage already contains them all.  Hence an indefinitely
  delayed `INF` collapse cannot have literal triviality as its positive branch
  after finite generation.
- **A common retraction is not enough.**  If the two edge embeddings
  `theta_0,theta_1:C->A` have a common retraction, representations factoring
  through the retraction balance the two restrictions but lose the kernel of
  the retraction.  Adding one faithful corona embedding creates an unmatched
  operator-norm summand.  Multiplicity dilution repairs normalized traces, not
  operator norm, so it does not satisfy Theorem 16's exact corona
  compatibility.
- **Boone packing does not remove the edge.**  Simpson's fixed finite
  presentation packs all input configurations, and its last stable letter is
  central over the lifted halting subgroup.  Before that central step it uses
  finitely many asymmetric HNN identifications between scaled copies of
  `Z * Z^2`.  Totality of the machine does not delete those vertex groups or
  stable letters, so central-HNN permanence alone does not prove the total
  branch MF.
- **Lamp and graph-wreath packing leaves a finite-presentation obstruction.**
  A commuting lamp base over the configuration cosets needs finitely many
  diagonal orbits.  A graph-product base needs only finitely many edge orbits,
  but a finite orbit of lamp generators cannot distinguish infinitely many
  obligations without conjugating their normal closures together.  No finite
  presentation gadget avoiding this collapse was found.
- **Opposite quotient coordinates solve compatibility but destroy
  compression.**  Putting the quotient maps in opposite coordinates makes
  the two graph edges conjugate by coordinate swap, so block-swap
  symmetrization gives exact matrix-corona compatibility.  But the lifted
  finite relations merely make the stable letter swap `(n,1)` and `(1,n)`
  for `n in N`; they do not force `n=1`.  The exact calculation is
  [[coordinate-swap-rope-does-not-compress-kernel]].

There is nevertheless a new positive input before the final rope edge:
[[higman-half-row-has-regular-mf-benign-witness]] proves that Higman's
two-letter positive half-row witness has a regularly operator-MF ambient
group.  This enlarges the MF-safe benign library but does not by itself prove
`(R2)`.

The exact open analytic/group-theoretic subproblem is therefore `(GH1)` for
the rope data, not generic MF preservation under arbitrary HNN extensions.

The tensor-synchronization theorem now resolves the analytic part without
requiring finite quotients to separate `Gamma`.  A regular representation of
`Gamma` in an MF algebra is tensored in an algebra-valued reduced product with
finite graph models whose edge restrictions are
exactly conjugate; the former supplies faithfulness and the latter supplies
compatibility.  The product benign witness in
`graph-witness-product-supplies-tensor-sync` supplies those finite graph
models uniformly from the finite-CEP embedding
`B3(1)<=F_2 times F_2`, while leaving the recursive kernel unchanged.  The
previously missing regular-MF ordinary factor is supplied uniformly by
`mikhailova-fiber-product-gives-regular-mf-benign-compiler`.
