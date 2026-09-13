---
rg: 2
id: zaremsky-3-02-braid-groups-embed-in-glnz
kind: claim
title: "Zaremsky Problem 3.2 resolved: do braid groups embed in GL_n(Z)?"
root: true
distinct_from:
  spherical-artin-groups-are-linear-over-q-x-y: that places every spherical Artin group, braid groups included, inside GL_N(Q(x,y)), a field of transcendence degree 2; this asks for an embedding into GL_m(Z), whose finitely generated subgroups are discrete in GL_m(R).
artifacts:
  - research/artifacts/zp-braid-glnz-landscape-2026-09-13.md
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3 ("Matrix groups,
braid groups, etc"), Problem 2, verbatim: "Do braid groups embed in
GL_n(Z)?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-02-by-yes` requires `every-braid-group-embeds-in-some-glnz`.
- **No**: `zaremsky-3-02-by-no` requires `some-braid-group-embeds-in-no-glnz`.

Never write a `requires: []` route into this claim.

**Reading.** `B_n` is Artin's braid group on `n` strands. Call a group
*Z-linear* if it has an injective homomorphism into `GL_m(Z)` for some `m`.
The question asks whether every `B_n` is Z-linear. The standard inclusions
`B_n <= B_(n+1)` make the answer monotone: if `B_N` is not Z-linear then no
`B_n` with `n >= N` is. So the answer is a threshold `N* in {4, 5, ..., oo}`,
where `N* = oo` means yes.

- `B_1`, `B_2` and `B_3` are Z-linear
  (`braid-groups-on-at-most-three-strands-embed-in-glnz`), so the first open
  case is `B_4`.
- For every `n`, Z-linearity of `B_n` is equivalent to Z-linearity of
  `P_n / <Delta^2>` (`braid-group-z-linear-iff-pure-braid-mod-center-z-linear`).
  For `n = 4` that group is a free-by-free group `F_3 ⋊ F_2`.
- Every `B_n` embeds in `GL_(n(n-1))(Z[t, t^{-1}])`
  (`braid-groups-embed-in-gl-over-integer-laurent-polynomials`), by specializing
  one Cohen–Wales parameter to the unit `(3 - sqrt 5)/2`. The problem is to
  get rid of the last formal parameter.

**Known before the list.** Braid groups are linear over fields of
characteristic 0 through the Lawrence–Krammer representation (Bigelow,
arXiv:math/0005038, Theorem 1.1; Krammer, Ann. of Math. 155 (2002)), and so are
all spherical Artin groups (Cohen–Wales, arXiv:math/0010204; Digne). In the
graph: `spherical-artin-groups-are-linear-over-q-x-y`. The list (July 12, 2026)
records the integral question as open. z-status-b's sweep
(`research/artifacts/zp-open-status-sections-2-4-2026-09-13-part2.md`) found
nothing that decides it.

**Links.** A yes gives `every-braid-group-is-linear-over-a-number-field`, which
gives the non-cocompact CAT(0) reading of Problem 3.6
(`number-field-linear-groups-act-properly-on-cat0-spaces`). Conversely, a
braid group with no proper action on a proper CAT(0) space would give a no
(`braid-not-z-linear-from-no-proper-cat0-action`).

## Attempts

- 2026-09-13 (z3-02-braid-glnz): the reductions and links above are landed
  (landscape in the artifact). The affirmative side is stuck on a unit
  specialization of the one remaining parameter. The one faithfulness proof
  checked (Cohen–Wales §4, following Krammer) works modulo `t` with a positive
  cone, and cannot reach a unit value
  (`lawrence-krammer-has-a-faithful-algebraic-unit-specialization`, attempt 3).
  No obstruction is known. All standard necessary conditions for subgroups of
  `GL_m(Z)` hold for braid groups (`some-braid-group-embeds-in-no-glnz`).
