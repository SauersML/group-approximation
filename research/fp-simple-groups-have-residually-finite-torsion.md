---
rg: 2
id: fp-simple-groups-have-residually-finite-torsion
kind: claim
title: (RT) In every finitely presented simple group, every finitely generated torsion subgroup is residually finite; this uniform torsion separator refutes Boone–Higman if true, and holds on every finitely presented simple family where it has been checked
distinct_from:
  some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup: that is the bounded-exponent separator P_n for a single exponent n; (RT) implies P_n for every n at once (Zelmanov), and it also covers unbounded-exponent torsion. So (RT) is the stronger, uniform statement, and it is the one the host-class proofs on main actually establish.
  brin-thompson-2v-is-torsion-locally-finite: that is the question for the single host 2V, in its strongest (locally finite) form; this is the claim for all finitely presented simple groups, in the residually finite form that the Röver–Nekrashevych hosts force.
  bh-separators-must-omit-nested-decidable-hosts: that classifies decision-problem separators and shows which die; (RT) is a hereditary group-theoretic separator, not a decision problem, so it is outside those tables.
refuted_by: [golden-mean-periodic-group-lies-in-a-contracting-rsg]
artifacts:
  - research/artifacts/gq-bh-bh-lit-survey.md
---

**OPEN**, stated in the refutation direction. Define

> **(RT)** Every finitely generated torsion subgroup of `S` is residually finite.

The claim is that (RT) holds for every finitely presented simple group `S`.

## Why it is a separator for Boone–Higman

- **Subgroup-closed.** (RT) passes to subgroups.
- **Fails on a decidable input.** `B(2,665)` is infinite, finitely generated, of exponent 665 and has solvable word
  problem (Novikov–Adian, as recorded in `free-burnside-groups-satisfy-boone-higman`). By Zelmanov
  (`restricted-burnside-finiteness`) it is not residually finite. So `B(2,665)` violates (RT).
- **Consequence.** If this claim holds, `boone-higman-conjecture` is false. Conversely, Boone–Higman forces some
  finitely presented simple group to contain a non-residually-finite finitely generated torsion group.
- **Relation to the bounded-exponent separator.** (RT) implies, for every `n`, that f.g. subgroups of exponent `n`
  are finite, i.e. the separator `P_n` of `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup`. So this
  claim implies the negation of that node for every `n`. It is stronger, but it is the natural uniform form.
- **Where it sits in the separator picture.** By `hereditary-approximation-disproofs-of-boone-higman` and
  `bh-separators-must-omit-nested-decidable-hosts`, a separator must use finite presentation and simplicity together.
  (RT) does: finitely presented non-simple groups can violate it. Examples:
  - Clapham's finitely presented overgroups of `B(2,n)`;
  - Ol'shanskii–Sapir's finitely presented torsion-by-cyclic groups, as noted in the bounded-exponent node.

## Families where (RT) is proved (all on main)

| finitely presented simple family | form proved | node |
|---|---|---|
| `V`, all `V_{d,r}` | f.g. torsion is finite | `almost-automorphism-torsion-subgroups-are-rf` item 2 (Röver for `V`) |
| every Röver–Nekrashevych `V_d(G)`, any self-similar `G` (finitely presented simple commutator subgroups for many `G`); Matui's one-sided SFT full groups and Exel–Pardo 1-graph groups, with all their subgroups | f.g. torsion is residually finite (virtually in `G^k`) | `almost-automorphism-torsion-subgroups-are-rf` items 1, 2, 6 |
| `T`, `T_{n,r}`, finitely presented simple circle groups | f.g. torsion is finite | `circle-and-tree-product-periodic-subgroups-are-finite` (a) |
| Burger–Mozes, Wise and other lattices in products of trees | f.g. torsion is finite | `circle-and-tree-product-periodic-subgroups-are-finite` (b) |
| Caprace–Rémy Kac–Moody lattices with 2-dimensional buildings, e.g. `Λ_(2,4,6)(q)` | torsion locally finite | `two-dim-cat0-product-groups-are-torsion-locally-finite` |
| Caprace–Rémy Kac–Moody lattices with word-hyperbolic Weyl group | torsion locally finite | `hyperbolic-kac-moody-lattices-are-torsion-locally-finite` |

Every row is proved by the same **equicontinuity principle**. A finitely generated torsion group is forced to have
a bounded orbit, or bounded depth change, on the host's natural space:
- pumping for synchronous tree dynamics;
- Serre, Norin–Osajda–Przytycki or Haettel–Osajda fixed-point theorems for trees, 2-complexes and hyperbolic
  buildings.

The group then lies in a profinite or finite stabilizer.

## Where (RT) is open

These are exactly the finitely presented simple families where the principle breaks:
1. **Brin–Thompson `nV`, `n >= 2`.** The depth cocycle becomes a vector. Owned elsewhere:
   `brin-thompson-2v-is-torsion-locally-finite` and `brin-thompson-groups-contain-infinite-periodic-groups`. The
   full-shift part of `2V` satisfies (RT) (`full-shift-topological-full-groups-are-torsion-locally-finite`).
2. **Contracting-RSG hosts of hyperbolic groups (BBMZ).** Their local maps change length:
   `contracting-rsg-torsion-subgroups-are-residually-finite`.
3. **Twisted Brin–Thompson groups `SV_Γ`.** Here (RT) for `SV_Γ` is at least as hard as (RT) for `Γ` together with
   `nV`.
4. **Kac–Moody lattices with `Z^2 ≤ W` and a spherical triple of generators.** This would follow from
   Haettel–Osajda's conjecture (locally elliptic actions of f.g. groups on finite-dimensional nonpositively curved
   complexes are elliptic) for Davis buildings.
5. **Derived full groups of minimal free `Z^N`-SFTs, if any is finitely presented** (Labbé's `Ω_U`). They sit
   inside the sofic, and for `N = 1` LEF, world, and LEF torsion need not be residually finite: Nekrashevych's simple
   periodic groups are LEF. So (RT) there is a genuinely new question.

**Where the general Boone–Higman routes put their torsion.** Every general route on main must violate (RT) on some
Burnside input, and each does so through a specific mechanism:
6. **Shell route (finite germ extensions of `V`, `boone-higman-via-shell-germ-stabilizers`).** The envelope
   `E_ν` contains the input `P`, so for `P ⊇ B(2,665)` it violates (RT) by construction. Away from the singular
   orbit its elements are prefix replacements, where the pumping of `almost-automorphism-torsion-subgroups-are-rf`
   applies. So non-residually-finite torsion can live only in the **singular germs**. The Burnside test gives the
   shell route no obstruction beyond its finite-presentation gate, but it says where the gate must carry torsion.
   Made precise by `torsion-subgroups-of-almost-v-groups-localize-at-singular-germs`: a finitely generated torsion
   subgroup either has infinite orbits on its singular support, or is locally-finite-by-(germs at finitely many
   fixed points).
7. **Type (A) and shift-compiler routes (twisted Brin–Thompson `SV_G` over a finitely presented strongly
   shift-similar or type (A) actor `G ⊇ P`).** The actor `G` itself contains `P`. So these routes need finitely
   presented actors with non-residually-finite torsion, for instance a finitely presented strongly shift-similar
   group containing `B(2,665)`. (RT) for finitely presented type (A) actors would block both routes for Burnside
   inputs.

## Lesson for general BH

The Burnside test turns Boone–Higman into a statement about **host dynamics**: a universal host must make some
finitely generated torsion group act non-equicontinuously, with no bounded orbit on any structure that has profinite
stabilizers. Every host family built from synchronous tree dynamics or low-dimensional nonpositive curvature fails
this. The live host mechanisms are:
- vector-valued depth (nV, higher-rank graphs);
- length-changing (asynchronous) local maps;
- higher-rank buildings;
- aperiodic-SFT full groups.

A proof of (RT) for any one of these families removes it as a possible universal host. Conversely, an infinite
non-residually-finite torsion subgroup in any finitely presented simple group would be the first evidence that
Boone–Higman survives its Burnside test.

## Attempts

1. **bh-free-12, 2026-09-18.** Stated the claim and collected the census above from the landed host theorems. No new
   family decided.
2. **REFUTED: the golden-mean group (swarm-0917 w21 belief breaker, 2026-09-20).** (RT) is false.
   - **Counterexample.** `golden-mean-periodic-group-lies-in-a-contracting-rsg` (landed by w12, marked unreviewed)
     puts `P = [F,F]` inside a finitely presented simple group `Q = SV_G`. Here `F` is Nekrashevych's golden-mean
     fragmentation group (arXiv:1601.01033, §7). `P` is infinite, finitely generated, simple and periodic. An
     infinite simple group is not residually finite. So `Q` violates (RT).
   - **Independent review of the chain.** Done for this attempt.
     - *Nekrashevych side.* I re-read the arXiv TeX (`burnside.tex`, l.1405–1439). The defining equations of
       `a_0, b_0, c_0, d_0` and `x_1, x_2` match the proof node's quotations verbatim. So does Theorem `th:F`:
       "periodic and of intermediate growth. Its derived subgroup $[F, F]$ is simple and has finite index in $F$".
       The typo `g_0` at l.1420 is harmless, because the proof covers every reading in `{a_0,b_0,c_0,d_0}`.
     - *RSG side.* I rechecked every case of Lemmas 3–6 of the proof node by hand: the phase lemma (both cases,
       dangling `1` absorbed after one block) and closure under products and inverses. Every local action of a
       K-map lies in the 7-element `N_0`. No gap was found.
     - *Import.* The BBMZ side is the established `contracting-rsgs-embed-in-fp-simple-groups`. Its item 1 makes
       `<V_2, F>` an RSG, and items 3 and 5 embed the full group `G_N` in `SV_G`.
     - *Computation.* `check_golden_mean_rsg.py` reruns clean: 2000 deep local actions, none outside `N_0`.
   - **What survives.** `P` has unbounded exponent (`bounded-exponent-groups-omit-alt-of-unbounded-orbits`), so the
     bounded-exponent separator `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup` (P_n) is untouched.
     The Burnside test of Boone–Higman now runs only through bounded exponent.
   - **Class of separators killed.** A separator of the form "every finitely generated subgroup of a finitely
     presented simple group with property Π is residually finite" is false whenever `P` has Π. Such Π include:
     - periodic;
     - amenable;
     - subexponential growth;
     - simple and periodic.

     So a hereditary torsion separator that could still refute BH must use bounded exponent. By Zelmanov
     (`restricted-burnside-finiteness`), it is then exactly ¬P_n.
   - **Host mechanisms.** In the Lesson list above, item 2, length-changing (asynchronous) local maps, is now
     realized: the generators `b_i, c_i, d_i` are asynchronous. Every census row stays true as stated, since those
     rows are specific host families.
   - **Collateral.** The main clause of `contracting-rsg-torsion-subgroups-are-residually-finite` fails for the same
     `G`. That node is not edited here; the finding goes to the bus as a spark.
