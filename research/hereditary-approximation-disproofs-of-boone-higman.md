---
rg: 2
id: hereditary-approximation-disproofs-of-boone-higman
kind: claim
title: An approximation property that forces soficity or MF-ness cannot disprove Boone--Higman, and a hyperlinear disproof needs three open theorems
distinct_from:
  boone-higman-conjecture: that is the embedding conjecture; this classifies which hereditary approximation properties could separate its two sides, and kills every property contained in soficity or in MF-ness at one finitely presented simple group.
  fp-simple-nonsofic-group: that is the existence of one finitely presented simple nonsofic group; this uses it as the invariant witness that kills a whole class of separating properties at the step "every finitely presented simple group has P".
  fp-simple-full-mf-radical-group: that is the MF-radical existence statement, whose own text already closes the single MF attack; this is the uniform statement for every hereditary property contained in soficity or MF-ness, plus the exact survivor decomposition for hyperlinearity.
  local-boone-higman-conjecture: that is the open universal-theory form of the conjecture; this records that a table-defined separating property refutes even that form, and names the prerequisites any such property must meet.
  nonsofic-hyperbolic-question-reduces-to-one-fixed-host: that reduces Gromov's nonsofic hyperbolic question to one host; this concerns separating finitely presented simple groups from decidable groups, where the hyperbolic question does not appear.
---

**ESTABLISHED** through `hereditary-approximation-disproofs-of-boone-higman-proof`.

Let `P` be a class of groups closed under isomorphism and passage to
subgroups. Say `P` **separates Boone--Higman** if

- **(S1)** every finitely presented simple group lies in `P`, and
- **(S2)** some finitely generated group with solvable word problem does not.

## Theorem

1. **Separation is a disproof, and it is the only disproof.** If `P`
   separates, `boone-higman-conjecture` is false. Conversely, if the conjecture
   is false, the class of groups embeddable in a finitely presented simple
   group separates it.
2. **Class kill.** If every member of `P` is sofic, or every member of `P` is
   an MF group (the notion of `mf-radical-functoriality`), then `P` does not
   separate. Every such `P` fails (S1) at a finitely presented simple group: at a nonsofic one
   (`fp-simple-nonsofic-group`), or at one with full MF radical
   (`fp-simple-full-mf-radical-group`). Sofic groups and MF groups are the
   extreme cases. Amenable, residually finite, LEF and LEA groups are sofic by
   classical results that are not re-derived here, so the kill covers them too.
3. **Survivors must contain the first nonsofic group.** If `P` separates, then
   `L^x` lies in `P`, where `L = L_(F_2)(1,2)`. `L^x` is finitely presented,
   simple and nonsofic. So `P` contains a nonsofic group, and no separating
   property sits inside soficity.
4. **Table-defined separators refute the local form.** If `P = P_M` is a local
   approximation property in the sense of
   `local-approximation-properties-are-marked-closed` and `P` separates, then
   `local-boone-higman-conjecture` is false, witnessed by one finite system.
5. **Hyperlinearity.** Hyperlinearity separates Boone--Higman iff both of the
   following hold:
   - **(H1)** no infinite finitely presented simple group is
     Hilbert--Schmidt stable;
   - **(H2)** some finitely generated group with solvable word problem is not
     hyperlinear.

   (H1) implies `binary-leavitt-unit-group-hyperlinear`, hence
   `hyperlinear-nonsofic-group`, and (H2) produces a nonhyperlinear group.
   All three are open.

## What this kills, and where

The invariant is soficity or MF-ness. Every approach of the form "all finitely
presented simple groups have `P`; this decidable group lacks `P`" with `P`
inside soficity or MF-ness dies at step (S1). For soficity the witness is the Leavitt unit group. For
table-defined properties the same step is exhausted by one finite table of that
group. The survivors are properties not known to force soficity or MF-ness, such as
hyperlinearity, weak soficity and linear soficity. For each of these, (S1) already forces a
`P`-approximable nonsofic group, and (S2) forces a group without `P`. No
nonhyperlinear group is known.

This makes precise the remark in `boone-higman-conjecture` that soficity,
hyperlinearity and MF-ness are not evidence about the conjecture. A disproof
through approximation must first produce a nonhyperlinear-type decidable
group, and must also show that the first nonsofic group is approximable in
that sense.

## Attempts

1. **Stability transplant (swarm-0917-w5-pull-z-5, 2026-09-17).** *Settles the
   claim; no route to Boone--Higman.* The transplant from stability theory to
   Boone--Higman reads a separating property `P` as its stability dual. For
   infinite simple groups, (S1) for hyperlinearity is exactly the failure of HS
   stability. The step that fails is the existence of any nonhyperlinear
   group, and nothing in stability theory produces one. The same lane's other
   step, "C-stable implies finitely normally generated", was already dead on
   the live bus.
