# Boone--Higman meets the MF radical, 2026-09-11

The Boone--Higman conjecture remains open here. This record does two things:
it grades the live holes against every obstruction on file, and it proves a
new consequence of the conjecture stated entirely in this repository's own
vocabulary.

## 1. Which hole is closest, and what blocks each

Eleven routes target `boone-higman-conjecture`; four are dead. Of the live
ones the open inputs fall into three families. Grading them against the
recorded obstructions:

**Shell / shift envelopes** (`decidable-inputs-have-fp-shell-envelopes`,
`perfect-decidable-inputs-have-fp-shell-envelopes`,
`infinite-shift-higman-compiler`, and the stabilizer and overgroup variants).
These carry the most machinery and the most obstructions. Blocked by, at
least: `free-shift-shell-envelopes-are-not-finitely-presented` (a successful
enumeration must impose a mixed near relation, and the generic computable
enumeration does not), `finite-ray-shift-envelopes-require-virtually-cyclic-input`,
`shell-prefix-core-detects-finite-ray-enumerations` (the normal-core repair
works exactly for virtually cyclic inputs), `shell-finite-prefix-cannot-certify-presentation`
(finite point samples certify nothing), and
`decidable-fp-groups-need-not-embed-in-rational-group` for the finite-state
variants. This family is the most developed and the most fenced. Not closest.

**Ring / projective host** (`decidable-group-ring-has-fp-projective-simple-host`,
`finite-fullness-simulation-theorem-for-rings`). Blocked by
`ring-simple-envelope-characteristic-obstruction`,
`rank-four-elementary-center-obstructs-simplicity`,
`projective-elementary-simplicity-forces-simple-ring` and
`fg-central-extension-of-fp-group-is-fp`. The September 8 correction also
moved finite presentation from `EL_4(U)` to `St_4(U)`. Not closest.

**Normal-lattice** (`ck-envelope-has-a-finitely-normally-generated-maximal-kernel`,
`ck-envelope-simple-core-has-finite-bi-index`). The bi-index half is now
heavily fenced: `ck-quotient-corner-has-infinite-bi-index` kills the canonical
corner and all its nontrivial quotients, `ck-cover-quotient-kernel-dichotomy`
confines any repair to the covering kernel, and
`terminated-digit-host-has-infinite-shell-biindex` kills the explicit host.
The maximal-kernel half is fenced only once, by
`kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`, and that obstruction
is explicitly about the general principle "property (T) implies Max-n", not
about any particular envelope. Its own node says so.

**Verdict.** The maximal-kernel hole carries the fewest obstructions, and its
single obstruction is a statement about a method rather than about the object.
That is the hole this record works on. The finding below is that it is *not*
specific to the Chatterji--Kassabov envelope: the identical question about a
group this repository built has a payoff that has nothing to do with
Boone--Higman, which gives the same hole two independent reasons to be worth
closing.

## 2. Boone--Higman forces a finitely presented simple group with full MF radical

The four ingredients are all already established here.

* `rank-twelve-leavitt-simple-non-mf`: `H = EL_12(L_(F_2)(1,2))` is
  nontrivial, finitely generated, simple, Kazhdan, and `Rad_MF(H) = H`.
* `rank-twelve-leavitt-elementary-wp-decidable` (new): `H` is infinite and has
  decidable word problem, hence is recursively presented. The proof multiplies
  `12 x 12` matrices in the Diamond-lemma normal form of the Leavitt algebra
  and compares entries; infiniteness is read off the full radical, since a
  finite group is MF.
* `mf-radical-functoriality`: `f(Rad_MF(G)) <= Rad_MF(H)` for every
  homomorphism.
* `Rad_MF` is an intersection of kernels, hence normal.

So `H` is an admissible Boone--Higman input. If the conjecture holds, it sits
in a finitely presented simple `K`; functoriality along the inclusion puts the
whole of `H` inside `Rad_MF(K)`; that is a nontrivial normal subgroup of a
simple group; therefore `Rad_MF(K) = K`.

```text
Boone-Higman  ==>  there is a finitely presented simple group K
                   with Rad_MF(K) = K.
```

Recorded as the root `fp-simple-full-mf-radical-group` with the route
`fp-simple-full-mf-radical-from-boone-higman`.

**Why it is worth recording.** The target is the missing corner of a square
this repository has filled on three sides: finitely presented with full
radical but not simple (`defect-saturation-full-mf-radical`); simple with
total radical but not finitely presented (`simple-sofic-total-mf-radical`);
finitely generated and simple with full radical but no finite presentation
(`rank-twelve-leavitt-simple-non-mf`). No finitely presented simple group in
the literature has been shown to have the property.

**The usable direction is the contrapositive.** A proof that no finitely
presented simple group has full MF radical refutes Boone--Higman. That is a
negative attack on a fifty-year-old conjecture which passes through no
decidability argument and no embedding argument, only through the
approximation machinery this repository owns. It is stated in prose in the
node rather than wired, because rg:2 records refutations as established
negation claims and no such claim exists.

**One thing it is not.** It is not a soficity statement. Soficity does not
imply MF-ness here: `simple-sofic-total-mf-radical` is a sofic group with
total MF radical. So nothing above licenses "Boone--Higman implies a nonsofic
finitely presented simple group", and the nodes say so explicitly.

## 3. The same hole, reached without Boone--Higman

`defect-saturation-full-mf-radical` gives a two-generated finitely presented
torsion-free Kazhdan acylindrically hyperbolic `G` with `Rad_MF(G) = G`, and
records that every nontrivial quotient again has full MF residual. So a
maximal proper normal quotient of `G` is simple with full MF radical, and by
`fp-quotient-iff-kernel-finitely-normally-generated` it is finitely presented
exactly when that maximal kernel is finitely normally generated.

That is `defect-saturation-has-fng-maximal-kernel`, and the deduction is
`fp-simple-full-mf-radical-from-fng-maximal-kernel`. It is the same shape as
the Chatterji--Kassabov hole, for a different group, with a payoff that does
not mention Boone--Higman.

The obstruction check for this new hole is the one that matters, and it
passes: `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels` is sharp
against the *general principle* (its witness is finitely presented,
torsion-free, hyperbolic and Kazhdan, and `G` has the same adjectives), but it
is an existence statement about one group's bad kernels and leaves open
whether a different, specified group has one good kernel. Zorn's lemma is
useless here for the reason it is useless in the CK lane: ascending chains of
finitely normally generated normal subgroups need not have finitely normally
generated unions.

The concrete next step named in the node: `G` is built by a Hull--Osin routing
quotient chosen to make the compression defect normally generate, not to be
maximal. Determine whether that routing can be iterated to a maximal quotient
with every stage finitely normally generated.

## 4. Verification boundary

Everything above is written mathematics plus four established imports. No Lean
certificate is claimed for the new nodes, no numerical computation was run,
and no MSI job was submitted for this step: the content is a four-line
functoriality argument and a normal-form algorithm, and neither gives signal
from a computer. Section 1's grading is a reading of nodes on `origin/main` at
the time of writing, not a proof that no other obstruction applies.
