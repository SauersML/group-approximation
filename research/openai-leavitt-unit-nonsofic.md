---
rg: 2
id: openai-leavitt-unit-nonsofic
kind: claim
title: The binary Leavitt unit group is nonsofic (ANNOUNCED, unrefereed)
distinct_from:
  kun-thom-nonsofic-wreath: that is a refereeable arXiv preprint by named authors about wreath products, imported as established; this is an unrefereed corporate announcement about the Leavitt unit group and is deliberately not established here
  leavitt-steinberg-hs-stability-fork: that is this repository's own dichotomy for the Steinberg cover St_5(L_(F_2)(1,2)); this is an external nonsoficity claim about the unit group of the same algebra
root: true
---

*Marked `root` only so that the graph does not report it as unreachable. It
is a recorded external fact, not a program target: no route should be built
toward it and nothing should depend on it. See the status note below.*

**Status: ANNOUNCED, not established at this repository's standard.**
`OPEN` here does not mean "believed false" or "worth attacking" — it means
the source is unrefereed and carries a visible trust surface, per repository
doctrine on conditional and unattested inputs.  Nothing in this graph should
depend on it.

The claim, as announced by OpenAI on 2026-08-01:

> **Theorem 1.1.** The unit group `L_(F_2)(1,2)^x` is not sofic.

for the binary Leavitt algebra
`R = L_(F_2)(1,2) = F_2<s_0,s_1,t_0,t_1 | t_i s_j = delta_ij, s_0t_0+s_1t_1=1>`.
What is actually proved is that the finitely generated subgroup
`G = EL_D(R) = Theta_D(EL_9(R)) <= R^x` is nonsofic, for an explicit
nine-word complete prefix code `D`; property (T) comes from
Ershov--Jaikin-Zapirain (arXiv:0809.4095) and the non-LEF witness is
Thompson's group `V`.  Soficity passes to subgroups.

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
soficity — `G` must admit a sofic approximation whose generator graphs
differ in `o(|Y_n|)` edges from uniformly bounded-degree graphs with a
uniform positive expansion constant.  The current text adds: "Property (T)
is required only of `Gamma`.  In our application, property (T) for `G` serves
only to obtain the expanding approximation assumed in the proposition."

The revision therefore moved the passage from soficity to a *single*
expanding approximation out of Proposition 2.3 and into the consequences of
Theorem 2.1.  Read that as the repair of the delicate step, and cite the
current version.

## Independent expert engagement

Kun--Thom, arXiv:1901.03963v3 (2026-08-04), write in their added
introduction: "On August 1, 2026, we learned about the breakthrough result of
OpenAI.  The proof of their key Proposition 2.3 in [20] is a creative and
effective application of the results and techniques of this paper and the
ones in [18]."  Fournier-Facio (arXiv:2608.02025) and Kun--Thom
(arXiv:2608.06222) both build on the criterion.  This is meaningful
corroboration by the people whose theorems are being applied; it is not
refereeing, and it does not move the status above.

## The sentence this program cares about

Verbatim, and **identical in both versions**:

> "Thus every sofic group is hyperlinear [Pes08, Theorem 3.3], but Theorem
> 1.1 does not determine whether `L_(F_2)(1,2)^x` is hyperlinear."

The same passage records that Kervaire--Laudenbach holds for every
hyperlinear group (Nitsche--Thom, J. Group Theory 25 (2022) 1--10,
arXiv:1811.07737, Theorem 1.3), so a one-variable equation over `R^x` with
nonzero total exponent and no solution in any overgroup would refute
hyperlinearity of `R^x` — a cheap falsification test.
