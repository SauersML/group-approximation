---
rg: 2
id: deligne-triple-cover-nonsurjunctive
kind: claim
title: Deligne's triple cover of Sp4(Z) carries an injective non-surjective cellular automaton
refuted_by:
  - deligne-triple-cover-surjunctive
artifacts:
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

**OPEN.** Some finite alphabet `A` carries an injective non-surjective cellular automaton on `A^(E_3)`,
where `E_3` is Deligne's connected triple cover of `Sp_4(Z)`.

**Payoff.**
- **Gottschalk.** It refutes Gottschalk's surjunctivity conjecture.
- **Finite normal subgroups.** It refutes `finite-normal-subgroups-do-not-affect-surjunctivity`, since
  `Sp_4(Z)` is residually finite and so surjunctive.
- **Soficity.** It proves `E_3` nonsofic.

## Attempts

No witness has been constructed. Every witness must meet these constraints (artifact Section 4.4):
- **Characteristic three: linear witnesses are dead.** It is not linear and not formalizable over `F_3^n`,
  and over `F_q^m` with `q` a power of `3` its degree product is at least `q`
  (`deligne-triple-cover-ternary-group-algebras-are-stably-finite`).
- **Memory group.** Its memory group `H` contains the central `z`, has `z in Res_fin(H)`, and is nonsofic;
  `H/<z>` is neither virtually free nor amenable
  (`strict-automata-memory-keeps-finite-normal-kernel-residual`).
- **Missed configurations.** It is bijective on `z`-invariant configurations
  (`surjectivity-descends-to-centralized-coset-quotients`), so it misses only configurations with trivial
  `C_3`-stabilizer.
- **Linear route in other characteristics: open.** The only linear route left is a one-sided inverse pair
  in one of the two twisted group algebras of `Sp_4(Z)` in a characteristic `p != 3` (artifact Lemma 4.1).
  Their multiplier class is not inflated from any finite quotient, and no construction or obstruction is
  known.
- **Linear route for p != 3, wired** (lane w4-deligne-twisted, `deligne-twisted-group-algebras-2026-09-12.md`).
  - **Route:** a one-sided pair in a twisted algebra is `deligne-twisted-group-algebra-is-not-stably-finite`,
    and it reaches this claim through `deligne-cover-nonsurjunctive-from-twisted-algebra-failure`.
  - **Cost:** by `deligne-cover-linear-soficity-is-rank-projective-approximation`, such a pair also proves
    `E_3` not `F_p`-linear sofic, so it is at least as hard as a rank-metric sector gap for the Deligne
    multiplier.
  - **Filter:** its support must keep `z` in the finite residual of its preimage (artifact Lemma 4.1).
  - **Positive side:** rank-approximate projective representations kill the whole linear route in every
    characteristic (`deligne-cover-stable-finiteness-from-rank-projective-models`).
- **Table-level filter** (idea from lane w4-clifford-nonlinear, argued here; not a claim). A strict pair
  reads finitely many products of a finite window of `E_3`, hence finitely many values `a(g,h)` of a
  section cocycle.
  - Suppose some finite quotient `Q` of `Sp_4(Z)`, injective on the images of those products, carries a
    cocycle `b in Z^2(Q; Z/3)` agreeing with `a` on the read pairs, after changing the section on the
    window.
  - Then the window embeds with the same coordinates into the finite group `Q x_b Z/3`. Forward
    coincidences survive, and no reverse coincidence is created, because images are distinct in `Q` and
    `Z/3`-coordinates are computed from the same values.
  - By `strict-pairs-transfer-to-table-realizations` that finite group would carry a strict pair, which is
    impossible.
  - So a witness's read partial cocycle is the restriction of no finite-quotient cocycle. Such partial
    cocycles exist because `E_3` is finitely presented and not LEF, and every witness table must contain
    one. No witness has been found.
- **Where it stops.** No mechanism is known that uses a non-inflated multiplier to produce a one-sided
  inverse pair. The known strict-pair designs on main (invariant output, table groups, Leavitt corners) all
  live on hosts built from compression, and `E_3` has none.
