# Rank one: the headline as the unit group

2026-09-07.  Audit of a fifth forwarded dossier, proposing that the headline
group be written as `H = L_(F_2)(1,2)^x` rather than as an elementary group of
an optimized rank, together with a set of editorial recommendations.

## Verdict

The identification is correct and is **already established in this
repository, internally and machine-checked**, and it is already printed in the
manuscript as a footnote to the headline theorem
(`GL_n(R) = EL_n(R) = R^x` for `n >= 2`, from Khanh--Thanh).  The node is
`leavitt-gl-equals-el-and-perfect-unit-group`, whose route is explicit that no
external `K`-theory is used: `KOne/AllRanksElementary.lean` proves
`glAll_eq_elementary` for every rank `n >= 2` over every field by prefix-code
self-similarity and block flattening, and `binaryLeavittUnits_perfect` proves
perfection through the three-leaf prefix code and the Steinberg relation.
`binary-leavitt-all-ranks-full-mf-radical` then already carries the full
conclusion at every rank including one.

So the recommendation is editorial: promote the footnote to the statement.
Nothing in the graph blocks it and nothing new is needed to license it.

## The dossier's own route, checked

The proposed chain is a valid alternative, and its citations check out.

- **Ara--Goodearl--Pardo, arXiv:math/0111066, Theorem 2.4**, quoted:
  "If `R` is a purely infinite simple ring then `K_1(R) = U(R)^ab`."  No von
  Neumann regularity is assumed, despite the paper's title; the proof records
  that a purely infinite simple ring is a GE-ring.  Their Theorem 4.2 supplies
  that `V_(1,n)`, the Leavitt algebra of type `(1,n)`, is purely infinite
  simple.
- **Ara--Brustenga--Cortinas, arXiv:0903.0056**, `K`-theory of Leavitt path
  algebras.  Corollary 7.7 could not be read from the abstract page.  The
  conclusion is independently immediate for the binary algebra over `F_2`:
  the relevant map is multiplication by `1 - 2 = -1`, an isomorphism of `Z`,
  so it has zero kernel and cokernel, and `K_1(F_2) = 0`, so
  `K_1(L_(F_2)(1,2)) = 0`.

The remaining step is general and is authored here as
`ge-ring-with-perfect-units-has-gl-equals-el`.

**Which route to prefer in this repository.**  The internal one.  Trading a
Lean-checked internal argument for a two-citation external chain is a
downgrade here, whatever its merits in a paper written from scratch.  The
external chain is recorded as a second route so that the general ring-theoretic
statement is available to other lanes.

## The module reframing

`R^x = Aut_R(R_R)` because `End_R(R_R) = R`, and the Leavitt relations say
exactly that `R_R = R_R (+) R_R`, with `s_i` and `t_i` the insertion and
extraction maps.  Iterating gives `R_R = R_R^(n)` for every `n >= 1`, so

```text
GL_n(R) = Aut_R(R_R^(n)) = Aut_R(R_R) = R^x.
```

That is the conceptual reason external matrix rank stops being informative for
this example: the module already absorbs finite matrix coordinates.  Authored
as `unit-group-is-automorphisms-of-a-self-doubling-module`.  Note this is the
`R = M_n(R)` mechanism again, so it is available only where the copies exhaust
the unit; the general rank-two theorem of
`full-defect-ring-non-mf-at-rank-two` needs no such exhaustion.

## Editorial recommendations, recorded not enacted

The prose of the manuscript is not this session's to edit.  Recorded for the
manuscript lane:

1. Make the headline `H = L_(F_2)(1,2)^x`, with a short identification lemma
   beside it, and keep the rank descent as a separate algebraic proposition.
2. Lead the exposition through the module: a module containing copies of
   itself, its automorphisms, the subgroup on selected summands, an
   automorphism compressing that subgroup, a centralizing element whose
   conjugate stops centralizing, and the commutator that matrix
   approximations must kill.
3. State the general ring hypothesis as the four splitting relations
   `w_iv_j = delta_(ij)` with the single fullness certificate `w_1ev_1 = 1`,
   proving the equivalence once.  This is already
   `full-idempotent-ring-has-properly-infinite-unit`.  For the binary example
   the splitting elements are the defining generators, so no preliminary
   construction is needed.
4. Give the finite linear certificate one proposition, one proof, and one
   consequence paragraph covering its three uses, rather than a subsection
   per corollary.
5. **Keep the Hilbert--Schmidt dimension bound out of the paper.**  The
   dossier is right that it adds a formula without resolving the
   approximation problem, since microstate dimensions are unconstrained.  The
   node `hyperlinear-models-need-quadratic-dimension` stays in the graph as a
   research record and now says so in its own body.

## Not asserted

No novelty for the identification.  Nothing here is formalized beyond what
`KOne/AllRanksElementary.lean` already carries, and the two new nodes are
paper-level.
