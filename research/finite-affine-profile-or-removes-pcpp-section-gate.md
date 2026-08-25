---
rg: 2
id: finite-affine-profile-or-removes-pcpp-section-gate
kind: claim
title: Finite affine-profile enumeration removes the coherent PCPP-section gate
distinct_from:
  dfnqxy-mie-pcpp-has-no-global-affine-replacement: that forbids one ambient-affine PCPP for every source verifier; this first narrows each fixed question-pair predicate to one affine subspace and uses a separate linear PCPP in each finite profile branch.
  affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain: that assumes both affine-safe source supports and coherent affine perfect-proof sections; this derives the latter after a finite OR and therefore leaves only source affine safety.
  finite-lcs-product-sign-is-exact-or: that supplies the final marked OR once a finite menu of LCS branches is given; this constructs the finite menu without knowing the HALT strategy's support.
---

**ESTABLISHED PROFILE COMPILER.**  Let `V` be one finite two-prover
verifier with binary answer strings.  Refine the verifier's private coins
into its question-pair label, so every sampled pair `q=(x_0,x_1)` has one
deterministic accepting relation

```text
C_q subseteq F_2^(k_0+k_1).                              (FAP1)
```

Suppose a perfect real commuting symmetric EPR strategy for `V` has
positive joint-answer support `S_q` at every sampled `q`, and suppose

```text
Aff(S_q) subseteq C_q.                                  (FAP2)
```

There is an effective finite menu of constant-answer verifier branches,
depending only on `V` and not on the strategy, with these properties:

1. one branch has a perfect strategy whose every positive local support is
   affine-safe;
2. a perfect matrix-ultraproduct model of any branch yields one for `V`;
3. after the established cap-safe `R_*` compilation and the exact finite
   LCS OR, the menu becomes one finite LCS with the same completeness and
   matrix-ultraproduct soundness.

Consequently the coherent affine PCPP-section hypothesis `(APS2)` in
`affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain` is
unnecessary.  The first remaining hypothesis in that chain is precisely
the pre-PCPP support condition `(FAP2)` for the selected HALT strategy.

## Enumerate the hidden affine hull without knowing the strategy

For each sampled `q`, enumerate all nonempty affine subspaces

```text
A_q subseteq C_q.                                       (FAP3)
```

This is finite and effective: enumerate affine systems `B y=c` over
`F_2`, evaluate their solution sets, and test containment in the finite
truth table of `C_q`.  Duplicates do no harm.  A **global affine profile**
is one choice `P=(A_q)_q`.  There are finitely many profiles.  Define the
narrowed verifier `V_P` by retaining the question distribution and replacing
`C_q` by `A_q`.

For every strategy, acceptance by `V_P` implies acceptance by `V`
pointwise.  Hence

```text
val_t(V_P) <= val_t(V)                                  (FAP4)
```

in every tensor, commuting, or matrix-ultraproduct model `t`.  On the
other hand, under `(FAP2)` the profile

```text
A_q=Aff(S_q)                                             (FAP5)
```

occurs in the enumeration, and the original perfect strategy also wins
`V_P` perfectly.  No measurement, marginal, or overlap is changed.

## A question-pairwise linear PCPP is sufficient

Fix one profile `P`.  For each `q`, the language tested in the Hadamard
answer reduction is

```text
L_q={ (Had(y_0),Had(y_1)) : (y_0,y_1) in A_q }.         (FAP6)
```

It is an affine subset of the two Hadamard-word spaces and has an
`O(K)`-size presentation by affine equations, where `K` is their combined
word length: impose the linear equations defining the two Hadamard codes
and the affine equations defining `A_q`.  The linear PCPP special case
extracted from Ben-Sasson--Goldreich--Harsha--Sudan--Vadhan therefore gives
a constant-query PCPP for `L_q` whose honest proof bits are affine functions
of the encoded assignment and whose local checks are affine equations.

Take the finite disjoint union of these PCPPs, dispatching on `q`.  Pad all
proofs and random seeds to the largest length.  Padding coordinates are
fixed to zero, so this does not spoil affineness.  The proximity and
soundness constants can be replaced by their finite worst cases.  This
is exactly compatible with the DFNQXY interface: in `Verify`, proof
cross-check, and proof-code questions, a prover receives the full pair
`(x_0,x_1)`, whereas a prover receiving only `x_c` is queried only about
the answer code.  Thus the proof map is allowed to depend on `q`; no
question-local consistency condition identifies proofs belonging to
different pairs.

The published answer-reduction soundness proof is conditional on a fixed
`q` before invoking PCPP proximity soundness.  It therefore applies
unchanged to this finite dispatched family.  In particular, a sequence of
strategies for the answer-reduced `V_P` with values tending to one decodes
to strategies for `V_P` whose values exceed the fixed source soundness
threshold.  By `(FAP4)` these are also strategies for `V`.

For completeness, use the affine honest proof map for `L_q`.  Hadamard
encoding, proof encoding, and restriction to a sampled view are affine.
Each positive `Verify` support is therefore contained in an affine image
of `A_q`, and every point of that image is accepted by the affine local
check.  Hence its affine hull is accepted.  The consistency, cross-check,
and code-test relations are already affine.  The perfect strategy remains
in the same Connes-embeddable algebra because all added answer and proof
bits are classical affine functions of joint outcomes of commuting source
measurements.

This localization does not contradict
`dfnqxy-mie-pcpp-has-no-global-affine-replacement`.  The full language
obtained by allowing arbitrary `q` and arbitrary nonlinear `C_q` need not
be affine.  Here each branch first replaces every `C_q` by one affine
`A_q`, and the PCPP proof map is required to be affine only with `q` fixed.

## Cap compilation, finite OR, and effectivity

Every positive context support after answer reduction is now affine-safe.
Apply the truth-table gadget of
`boolean-relations-have-affine-complete-rstar-pp-gadgets` to obtain a
cap-valued perfect lift.  Its visible projection is the entire source
predicate, so restricting a target model gives a model of the
answer-reduced branch.  Enumerate the seven Fano-cap choices in every
bounded target context and turn each cap profile into an LCS branch.

Do this for every global affine profile `P`, and apply
`finite-lcs-product-sign-is-exact-or` once to the resulting finite menu.
The branch selected by `(FAP5)` supplies HALT completeness.  On a NONHALT
input, a negative marked matrix-ultraproduct model of the OR decodes on a
nonzero selector corner to one cap branch, then to one answer-reduced
`V_P`, then by answer-reduction soundness and `(FAP4)` to a forbidden source
strategy.  Thus all soundness implications are valid for quantum and
ultraproduct strategies; no classical choice of the unknown support is
made inside a quantum model.

The construction is computable although enormous.  For a fixed machine
index the source verifier has finitely many random strings, questions, and
answers.  Exhaustive enumeration of question pairs, truth tables, affine
subspaces, global profiles, linear PCPP descriptions, and cap profiles all
terminate.  Efficiency is irrelevant to the recursive fixed-point
argument, which only requires a finite presentation to be output in finite
time.

## Recursive scope and the still unaudited transformations

The same observation can be reused at any **finite** compiler stage whose
incoming perfect support is affine-safe.  A deterministic support is a
singleton and is therefore an admissible starting profile.  Parallel
repetition preserves the property because the affine hull of a correlated
support is contained in the product of the affine hulls of its coordinate
projections.  Oracularization, fixed type labels, coordinate copying, and
detyping use affine embeddings or projections and likewise preserve it.

For the nonuniform finite-presentation objective, one can apply the present
Hadamard/linear-PCPP reduction directly to an affine-profile narrowing of a
finite verifier with arbitrarily long answers.  The two preliminary
low-degree answer reductions in DFNQXY Theorem 6.10 are needed for
polynomial-time parameters, not for mere finite effectivity, and may be
skipped.  Thus those two layers introduce no additional gate **after**
`(FAP2)` has been proved for the final finite source verifier.

This does not yet propagate a deterministic base strategy through the
self-referential JNVWY compression theorem.  In the published compression
pipeline, the low-degree PCP of JNVWY Theorem 10.25 has `POINT_6`
game-check predicates containing circuit-proof data.  As
`jnvwy-low-degree-pcp-reflects-affine-unsafety` records, that layer reflects
any incoming odd-xor violation and its generic completeness proof does not
provide an affine witness section.  To use profile enumeration recursively,
one must replace the game-check proof layer by a profile-dispatched linear
proof construction at every recursive occurrence and then audit the
introspection, low-degree consistency, and recursive-game tests for affine
support preservation.  No claim presently in Cairn proves that replacement
is compatible with the JNVWY compression soundness theorem.  Therefore
"the base HALT proof is deterministic" alone does not yet establish
`(FAP2)` for the final MIP*=RE verifier.

Primary-source interfaces used above:

- Dong--Fu--Natarajan--Qin--Xu--Yao, arXiv:2312.04360v3,
  Definition 6.8, Figure 5, and Theorem 6.9.  Figure 5 gives the full pair
  to every proof-query player, and Theorem 6.9 derives source soundness
  from a near-perfect answer-reduced strategy.
- Natarajan--Vidick, arXiv:1801.03821v2, Theorem 6.1 and its proof,
  especially the BSGH+05 linear-PCPP special case for an AND of affine
  equations.
