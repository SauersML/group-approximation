---
rg: 2
id: left-invertible-lift-of-s0-in-leavitt-group-algebra
kind: claim
title: A left-invertible lift of s_0 to the Leavitt group algebra
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that asks only that some one-sided inverse pair exist somewhere in the group algebra; this asks for one whose right factor evaluates to `s_0`, which is strictly stronger and is exactly the condition for the explicit four-site rule to extend to the full shift
  leavitt-corner-one-sided-lift-exists: that states the lifting problem inside the corner `eAe`, where the identity is `e` and the augmentation no-go is switched off; this stays in the whole algebra with identity `1`, which is a different equation and is what the support-thirteen bound constrains
  leavitt-rank-three-lift-inverse-support-thirteen: that fixes the explicit support-three lift of `t_0` and bounds the support of any completing factor; this quantifies over all lifts of `s_0` and asserts existence, so that bound restricts one instance of it rather than deciding it
  leavitt-rank-three-unit-lift: that constructs support-three lifts of the generators, which exist and are explicit; this asks for a lift with a one-sided inverse, which is the thing no construction supplies
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Exhibit `a` in `A = F_2[G]`, `G = L_(F_2)(1,2)^x`, with

    pi(a) = s_0        and     b a = 1 for some b in A,

where `pi : A ->> R = L_(F_2)(1,2)` is the evaluation map of
`leavitt-unit-group-algebra-surjects-onto-leavitt`.

## Why this is the sharp form of the surjunctivity gap

For any `a` in `A`, the dual of right multiplication `R_a : s |-> s a` is a
linear cellular automaton `T_a` on the full shift `F_2^G`, and

    T_a injective  <=>  R_a surjective  <=>  a left-invertible in A.

So this claim says precisely that the explicit four-site rule of
`leavitt-kernel-annihilator-strict-self-embedding` — injective on the proper
subshift `X`, and useless there — extends to an **injective** automaton of the
full shift.  Non-surjectivity is then automatic, since `pi(a b) = s_0 t_0 != 1`
(see `leavitt-direct-finiteness-failure-from-left-invertible-lift`).  It is
therefore the one statement that would convert the repository's dynamical
material into a disproof of Gottschalk's conjecture, and it simultaneously
refutes Kaplansky direct finiteness.

## Necessary conditions already known

*Augmentation.*  `eps(a) = 1`, since `eps(b) eps(a) = 1`.  This alone kills
the natural four-unit lift `a = [uv] + [u] + [v] + [w]` of `s_0`, which has
four terms.  It is **not** an obstruction to the claim: by
`leavitt-evaluation-kernel-hits-augmentation-one` the kernel contains an
element of augmentation `1`, so parity is always repairable.

*Support.*  The corresponding question for the explicit support-three lift of
`t_0` carried a proved floor: any completing factor has support at least
thirteen (`leavitt-rank-three-lift-inverse-support-thirteen`).  That bound was
about `t~`, not about lifts of `s_0`, and it excluded small witnesses rather
than all of them.

*Location, which is stronger and does reach `s_0` (2026-08-18).*  The explicit
support-three lift `s~ = [v_1]+[v_2]+[v_3]` of `s_0` is now **excluded
outright** as the `a` of this claim: `<v_1,v_2,v_3> = (C_2 x C_2) * C_3`
(`leavitt-rank-three-support-group-is-virtually-free`), so by
`subgroup-supported-one-sided-inverse-rigidity` a left inverse would make
`s_0` a unit of `R` — see
`leavitt-rank-three-lift-has-no-one-sided-inverse` item 2.  The claim itself is
untouched, since it quantifies over all lifts of `s_0`; what changed is that
the obvious one is gone along with the four-unit lift the augmentation already
killed, and the necessary condition to carry forward is now: **the support of
`a` must generate a subgroup whose group algebra is not directly finite.**
For a lift of `s_0` that is a condition on the lift, not on its partner, so it
can be checked before any search for `b` begins.

Equivalently, in element form: correct chosen lifts `a, b` of `s_0, t_0` by
kernel elements `alpha, beta` so that `(b + beta)(a + alpha) = 1`, that is

    (b a - 1) + b alpha + beta a + beta alpha = 0,   alpha, beta in ker(pi).

## Attempts

**2026-09-12, normal form and unit reformulation (lane `gk-kdf-structure`).**

* **Exhaustiveness.** By `leavitt-inverse-defects-are-visible-or-invisible`, every
  Kaplansky pair in `F_2[R^x]` whose defect survives evaluation is a translate, by
  one group element, of a witness to this claim. The partner can then be taken
  over `t_0`. If `pi(b) = t_0 + gamma t_1`, the involution `1 + s_0 gamma t_1` fixes
  `s_0` on the left and turns `pi(b)` into `t_0` on the right. The only other kind
  of pair is `leavitt-evaluation-kernel-unitization-not-directly-finite`.
* **Unit reformulation.** This claim holds exactly when some lifts `a` of `s_0` and
  `b` of `t_0` have `b a` a unit of `F_2[R^x]`. Then `b' = (b a)^(-1) b` satisfies
  `b' a = 1` and still lies over `t_0`, since `pi(b a) = 1`. In particular
  `b a - 1` nilpotent is sufficient. Trivial units over `1` are only `[1]`, so a
  nontrivial correction needs a nontrivial unit of the group algebra in `1 + ker(pi)`.
* **Completion is impossible.** A witness never extends to lifts of `(s_1, t_1)` that
  complete a Leavitt family, because the augmentation forbids a unital binary Leavitt
  family in any group algebra over a field. So the defect `1 - a b` lifts `s_1 t_1`
  but is not equivalent to `1` (Proposition 6 of
  `research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md`).
* **Gate.** If `R^x` is linear sofic over `F_2`
  (`binary-leavitt-unit-group-is-f2-linear-sofic`), this claim is false.

**2026-09-12, SAT on bounded supports (lane `kdf-sat`).** The encoder
`experiments/nonsofic-certificates/kaplansky-df/sat/dfsat.py`, in target mode,
imposes two conditions:
- `pi(a) = s_0`, as linear XOR rows over the normal-form monomial coordinates of `R`;
- `b a = 1`, as bilinear XORs over shared AND variables.

Strictness is then automatic, since `s_0` is not a unit of `R`. Results so far:

* **Thompson `V`**, generators `A, B, C, P`, at every radius. By
  `s0-lifts-cannot-be-supported-in-the-all-ones-stabilizer`, no lift of `s_0` is
  supported in `V`. The exact span computations on `pi(B_r(V))` for `r <= 6` are
  instances of it.
* **Nine-leaf `EL_D` generators** of `openai-nine-leaf-leavitt-configuration`.
  `s_0` is not in the span of `pi(B_3)`, by Gaussian elimination. These generators
  generate all of `R^x`, so this is only an effect of the radius.
* **The two `GL(4,2)` atlas charts**, which generate all of `R^x`. `s_0` lies in the
  span of `pi(B_3)`, but the solver finds no pair
  - with `supp a` and `supp b` both in `B_3` (85,849 AND variables). This is UNSAT
    in 82 s with the valid prune clauses of 7e8a94ac9, and UNKNOWN at 600 s without them;
  - with `supp a` in `B_3` and `supp b` in `B_2` or `B_1`;
  - with `supp a` in `B_5` and `supp b` in `B_1`.

  Without prune clauses, pairs with `supp a` in `B_4` and `supp b` in `B_3`, or
  `supp a` in `B_5` and `supp b` in `B_2`, were UNKNOWN at 2,400 s (about 470,000 AND
  variables). With the prunes and the all-ones clause they are still UNKNOWN at about
  2,430 s.
* **Exact span bound on the atlas charts**, by Gaussian elimination. Neither `s_0` nor
  `t_0` lies in the span of `pi(B_2)`, and `s_0` lies in the span of `pi(B_3)`. So
  every lift of `s_0` over these generators has support radius at least 3, and 3 is
  attained.
* **Two-sided mode on the atlas charts.** Also impose `pi(b) = t_0`.
  - Every witness can be corrected to this form, by the Exhaustiveness item above.
    The correction changes supports, so these runs restrict the search rather than
    decide the one-sided instances.
  - With prunes, the solver finds no pair with `(supp a, supp b)` in `(B_3, B_3)`
    (0.19 s, 85,849 AND variables), `(B_4, B_3)` (981 s) or `(B_3, B_4)` (490 s), the
    last two with 469,679 AND variables each.

Where it dies: every support tried so far is too small. The UNSAT verdicts are
CryptoMiniSat outputs without proof logs, so they record where nothing was found and
certify nothing. Details: `research/artifacts/kaplansky-df-sat-search-2026-09-12.md`.
