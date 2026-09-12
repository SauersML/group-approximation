---
rg: 2
id: linear-sofic-groups-are-surjunctive
kind: claim
title: A group that is linear sofic over some prime field is surjunctive
distinct_from:
  sofic-groups-are-surjunctive: that is Gromov and Weiss from soficity; this would derive surjunctivity from linear soficity over one prime field, a weaker hypothesis, conditional on stable formalizability and alphabet ascent.
  stable-finiteness-forces-prime-power-surjunctivity: that concludes surjunctivity over p-power alphabets from stable finiteness of F_p[G]; this concludes surjunctivity over every alphabet from linear soficity over F_p.
  linear-sofic-nonsofic-group: that asks for a linear sofic group outside the sofic class; this records what such a group would buy for Gottschalk's conjecture.
refuted_by:
  - some-linear-sofic-group-is-not-surjunctive
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
---

**OPEN.** If a group `G` is `F_p`-linear sofic for some prime `p`, then `G` is surjunctive over every finite
alphabet.

**Why it would extend Gromov–Weiss.** Sofic groups are linear sofic over every field. So the statement
contains `sofic-groups-are-surjunctive`, and it exceeds it on any linear sofic nonsofic group.

## Attempts

- **Route.** `linear-sofic-surjunctivity-via-formalizability-and-ascent`:
  1. linear soficity gives stable finiteness of `F_p[G]`;
  2. stable formalizability gives surjunctivity over `p^n` symbols;
  3. ascent gives every alphabet.
- **Without ascent.** The same argument gives surjunctivity over prime-power alphabets, for each prime at
  which `G` is linear sofic.
- **Census of recorded nonsofic hosts** (artifact, Section 8).
  - *Kun–Thom wreath.* Linear soficity is open (`kun-thom-wreath-linear-sofic`), but its group algebras are
    stably finite (`kun-thom-wreath-stably-finite`), consistent with its known surjunctivity.
  - *`R^x`, `L_(F_3)(1,2)^x`, `PG`.* Linear soficity is open (`binary-leavitt-unit-group-is-f2-linear-sofic`,
    `projective-ternary-group-is-f3-linear-sofic`). The natural rank models are dead
    (`leavitt-algebra-has-no-unital-rank-model`, `block-unipotent-rank-models-of-leavitt-el3-are-trivial`,
    `monomial-rank-models-are-hamming-models`).
  - *Thompson's `V` and the Fournier–Facio group.* Not recorded.
- **Where it stops.**
  - Stable formalizability and ascent are both open.
  - No nonsofic group is known to be linear sofic (Arzhantseva–Paunescu Question 8.5), so the statement
    currently exceeds Gromov–Weiss only conditionally.
  - Read contrapositively: a strict automaton on a group, together with the two open prerequisites,
    makes that group not linear sofic over any prime field.
- **Matrix form, datum by datum** (w4-linsofic-surj, artifact `linear-sofic-rung-rank-implication-2026-09-12.md`).
  - *Exact form.* Over `F_p` the claim holds iff every strict datum has a reverse word whose rank is forced
    below `eps n` whenever all forward relators have rank at most `delta n`, in every invertible matrix tuple
    (`linear-sofic-surjunctivity-is-a-rank-implication-per-datum`). The rules enter only through strictness.
  - *Gromov–Weiss is the monomial case.* That implication holds on monomial tuples for every strict datum, and on
    tuples near monomial ones (`gromov-weiss-is-the-monomial-case-of-the-rank-implication`). The content of the
    claim is tuples far from monomial.
  - *Counting does not extend.* The coordinatewise product through which nonlinear rules are evaluated vanishes
    in defect only at permutation matrices, and a rank-one perturbation gives it full rank
    (`site-pullbacks-are-discontinuous-in-the-rank-metric`). So Gromov–Weiss counting has no rank-metric version.
    A proof must linearize on the group side first, as the recorded route does, or find a rank-visible invariant of
    the rule pair.
  - *Negation.* `some-linear-sofic-group-is-not-surjunctive` (open). A strict datum whose reverse words avoid the
    linear sofic kernel makes `F(D)/N_lin(F_p)(D)` linear sofic, not surjunctive and not sofic.
  - *Where it stops.* No proof for nonlinear automata, and no separating datum. Whether the rank implication
    implies linear control, `rk(rho(w) - 1) <= C max_r rk(rho(r) - 1)`, is open. The weakly sofic rung implies it.
