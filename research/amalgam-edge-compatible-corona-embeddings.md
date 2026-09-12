---
rg: 2
id: amalgam-edge-compatible-corona-embeddings
kind: claim
title: Edge-compatible corona embeddings for the literal marked amalgam
refuted_by: literal-mark-quotient-not-mf
distinct_from:
  literal-mark-quotient-mf: That claim is group MF of the amalgam; this is the C*-level datum Shulman's criterion asks for, which is strictly stronger and which requires both vertex algebras to be MF.
  shulman-amalgam-mf-criterion: That is the imported general theorem; this is the instance it demands for this particular amalgam.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
  - research/artifacts/bekka-math-0609102-verified.md
  - research/artifacts/shulman-2603-13564-verified.md
---

Writing `E/<w> = V *_{B_1} ((Z/2)^8 semidirect B_1)`
(`literal-lamp-kernel-clifford-block-amalgam`), the datum required by
`shulman-amalgam-mf-criterion` is: embeddings

```text
phi_V : C*(V) -> prod M_n / (+) M_n,
phi_K : C*( (Z/2)^8 semidirect B_1 ) -> prod M_n / (+) M_n
```

into one norm matrix corona whose restrictions to `C*(B_1)` coincide.

## Ideas

**It is the same fork.**  Compatibility forces the eight lamps of a block to
become distinct commuting symmetries in `C = phi_V(B)' cap Q` that are
permuted transitively by `phi_V(B_1)`, where `B` is the site stabilizer of
index eight in `B_1`.  A symmetry in `C` that is *not* in
`phi_V(B_1)' cap Q` is exactly operator-norm commutant growth at the
compressor, so this claim implies the negation of
`corona-commutant-no-growth` — the same hinge reached from a different
direction, and independently of the Kazhdan transport argument
(`marked-quotient-mf-forces-commutant-growth`).

**The algebra-versus-group gap bites at the INPUT, not only the output.**
Residual finiteness of `V` gives *group* MF for free, and gives nothing at
the algebra level: `C*(V)` MF is not implied by `V` being residually finite,
linear, or residually finite dimensional-free in any other sense.  Both
hypotheses of Theorem 20 are therefore genuinely open inputs here, including
the one about a group whose group-level MF was trivial.  Do not read
"`V` is linear hence MF" as "`C*(V)` is MF".

**What is known about those inputs.**  Both vertex algebras contain
`C*(Z^3 sd SL_3(Z))`.  Bekka (arXiv:math/0609102, abstract verified in
`research/artifacts/bekka-math-0609102-verified.md`) proves the full
C*-algebra of `SL_n(Z)`, `n >= 3`, has no faithful tracial state; a separating
family of finite-dimensional representations would produce one, so these
algebras are not residually finite dimensional.  That does **not** refute MF —
a unital MF algebra carries a limit trace, which need not be faithful — but it
closes the exact finite-dimensional side, so whatever supplies MF here must be
genuinely asymptotic.  Shulman's own introduction says the status directly:
outside the amenable and RFD classes "it is not clear when full group
C*-algebras are MF or at least stably finite".

**A structural asymmetry worth exploiting** (cairn-literal): the edge group
`B_1` has *finite* index `256` in the right-hand vertex group, and infinite
index in `V`.  So the compatibility datum is not symmetric — one side extends
an embedding of `C*(B_1)` across a finite-index overgroup.  Induction does not
obviously help, since it returns a representation whose restriction is the
induced one rather than the original, but the asymmetry should be checked
before the two sides are treated alike.

**What it is good for anyway.**  It converts "is the quotient MF" into a
question about two *residually finite* groups and one matching condition on a
shared (T) subgroup, with no lamp combinatorics left.  Any negative answer for
`C*(V)` would also be interesting on its own.
