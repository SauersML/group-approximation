---
rg: 2
id: openai-leavitt-unit-nonsofic
kind: claim
title: The binary Leavitt unit group is nonsofic - the first nonsofic group
distinct_from:
  kun-thom-nonsofic-wreath: That is a later theorem, about generalized wreath products over infranormal Kazhdan pairs, whose own abstract says it builds on this result and analyses its mechanism; this is the first nonsofic group, about the unit group of the binary Leavitt algebra.
  universal-leavitt-el4-nonsofic: That is this repository's own kernel-checked endpoint, which reaches the same unit group through a rank-four configuration and a two-relator corner witness; this is the chapter's theorem, reached through a nine-leaf configuration and Thompson's `V`, and it came first.
  leavitt-steinberg-hs-stability-fork: That is this repository's dichotomy for the Steinberg cover `St_5(L_(F_2)(1,2))`, about normalized-Hilbert-Schmidt stability; this is a soficity statement about the unit group of the same algebra.
  openai-nine-leaf-leavitt-configuration: That asserts only that one explicit subgroup triple satisfies the criterion's hypotheses, with no approximation property in it; this is the nonsoficity conclusion drawn from it.
root: true
artifacts:
  - c1168433:official/counterexample.tex
  - c1168433:official/reasoning.tex
  - 22863aed:official/README.md
---

ESTABLISHED.

> **Theorem 1.1.** The unit group `L_(F_2)(1,2)^x` is not sofic.

for the binary Leavitt algebra
`R = L_(F_2)(1,2) = F_2<s_0,s_1,t_0,t_1 | t_i s_j = delta_ij, s_0t_0+s_1t_1=1>`.
What the proof produces is a finitely generated nonsofic subgroup
`G = EL_D(R) = Theta_D(EL_9(R)) <= R^x` for an explicit nine-word complete
prefix code `D`; soficity passes to subgroups.  Announced by OpenAI on
2026-08-01, this is **the first nonsofic group** -- the first negative answer
to Weiss's question (Pes08, Open Question 3.8), open since 2000.

Root-marked as the record of the question this program is named after.  The
two routes into it are the chapter's own derivation
([[openai-expander-matching-criterion]] applied to
[[openai-nine-leaf-leavitt-configuration]], with [[thompson-v-not-lef]] as the
witness) and this repository's independent kernel-checked proof of the same
statement.

## Priority, stated once so the graph stops getting it backwards

The first nonsofic group is this one.  Kun--Thom, arXiv:2608.06222, open their
abstract with "This work builds on the breakthrough of OpenAI in finding the
first nonsofic group.  We analyze the underlying proof mechanism and find
further applications"; their Theorem A is not an independent existence proof
and must never be cited as one.  Fournier-Facio, arXiv:2608.02025, likewise
builds on the criterion for the torsion-free example.  In their own v3
introduction (arXiv:1901.03963v3, 2026-08-04) Kun and Thom write: "On August 1,
2026, we learned about the breakthrough result of OpenAI.  The proof of their
key Proposition 2.3 in [20] is a creative and effective application of the
results and techniques of this paper and the ones in [18]."  That is the
attribution to keep in both directions -- the criterion is theirs to be
applied, and applying it was the step nobody had taken.

`notes/CREDIT_AND_PRIORITY_AUDIT.md` already carries this as a manuscript
directive; the two things `official/README.md` says never to inherit from the
copy (the "[Kun19] ... 2019" dating of arXiv:1606.04471, which is June 2016,
and the "soficity conjecture" framing of an open question) still stand.

## Version trap

The chapter exists in two versions with the **same proposition numbers and
different hypotheses**.  Always state which one is meant.

| | original | current |
|---|---|---|
| URL | `cdn.openai.com/pdf/ten-proofs-oai-original.pdf` | `cdn.openai.com/pdf/ten-proofs-oai.pdf` |
| Ch. 3 title | "A Counterexample to the Soficity Conjecture" | "Nonsofic groups exist" |
| pages | 77--93 | 78--95 |
| dated | announced 2026-08-01 | "Updated August 6, 2026" |

**Proposition 2.3, original:** `Gamma <= G` infinite **finitely generated
groups with property (T)**; `G=<Gamma,t_1,...,t_m>`, `t_i Gamma t_i^(-1)<=Gamma`;
`J<=G` finitely generated with `[Gamma,J]=1`, `Gamma cap J={1}`,
`t_1 J t_1^(-1)<=Gamma`; then **soficity of `G`** implies `J` is LEF.

**Proposition 2.3, current:** (T) is required **only of `Gamma`**, and the
conclusion is conditioned on an explicit hypothesis rather than on bare
soficity -- `G` must admit a sofic approximation whose generator graphs
differ in `o(|Y_n|)` edges from uniformly bounded-degree graphs with a
uniform positive expansion constant.  The current text adds: "Property (T)
is required only of `Gamma`.  In our application, property (T) for `G` serves
only to obtain the expanding approximation assumed in the proposition."

The revision moved the passage from soficity to a *single* expanding
approximation out of Proposition 2.3 and into the consequences of Theorem 2.1.
Read that as the repair of the delicate step, and cite the current version.
Neither version changes the Leavitt application; `official/counterexample.tex`
in this repository is the current one.

## The sentence this program cares about

Verbatim, and **identical in both versions**:

> "Thus every sofic group is hyperlinear [Pes08, Theorem 3.3], but Theorem
> 1.1 does not determine whether `L_(F_2)(1,2)^x` is hyperlinear."

So this theorem does not touch [[hyperlinear-nonsofic-group]] by itself: a
nonsofic group is a candidate for Q3.4 only once it is known to be
hyperlinear, and nothing here decides that.  The same passage records that
Kervaire--Laudenbach holds for every hyperlinear group (Nitsche--Thom,
J. Group Theory 25 (2022) 1--10, arXiv:1811.07737, Theorem 1.3), so a
one-variable equation over `R^x` with nonzero total exponent and no solution
in any overgroup would refute hyperlinearity of `R^x` -- a cheap falsification
test, tracked at [[kl-violating-equation-over-leavitt-unit-group]].

## Why this is established here and was not before

The node used to read "ANNOUNCED, not established at this repository's
standard", on the ground that the source is an unrefereed corporate
announcement.  That reasoning does not survive contact with what this
repository actually holds:

* the exact statement `L_(F_2)(1,2)^x` is not sofic is a **kernel-checked
  theorem here** -- `Endpoint/MainResults.universalLeavittUnits_not_isSofic`,
  where `UniversalLeavitt.BinaryLeavittAlgebra` is the free `ZMod 2`-algebra
  on `s_0,s_1,t_0,t_1` modulo exactly `t_i s_j = delta_ij` and
  `s_0 t_0 + s_1 t_1 = 1`, which is the chapter's equation (1) verbatim;
* the bridge their Proposition 2.3 supplies is formalized here as
  [[one-sided-compression-nonsofic-criterion]], and both of its external
  inputs are proved here rather than quoted;
* the chapter's own argument is checkable, and it is checked in the four
  nodes this one now decomposes into.

The quarantine also had a cost the graph could measure: it left
[[kun-thom-nonsofic-wreath]] imported as established while the result it
builds on was parked, which is how "nonsofic groups exist unconditionally
(kun-thom-nonsofic-wreath)" came to be written down.
