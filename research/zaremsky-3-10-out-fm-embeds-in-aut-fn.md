---
rg: 2
id: zaremsky-3-10-out-fm-embeds-in-aut-fn
kind: claim
title: "Zaremsky Problem 3.10 resolved: does every Out(F_m) embed in some Aut(F_n), and every closed-surface MCG(S_g) in some Out(F_n) or Aut(F_n)?"
root: true
distinct_from:
  out-free-groups-satisfy-boone-higman: that is the Boone--Higman statement for Out(F_n); this is the question whether Out(F_m) embeds in any Aut(F_n) at all, which is one sufficient route to that statement.
  closed-surface-mapping-class-groups-satisfy-boone-higman: that is the Boone--Higman statement for closed-surface mapping class groups; this asks whether those groups embed in automorphism or outer automorphism groups of free groups.
artifacts:
  - research/artifacts/zp-out-aut-mcg-embeddings-2026-09-13.md
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3, Problem 10, verbatim:
"(Added 3/20/25) Does every Out(Fm) embed in some Aut(Fn)? Does every MCG(Sg)
embed in some Out(Fn) and/or some Aut(Fn)?"

This claim is the question. It is established only through the route
`zaremsky-3-10-by-parts`, which requires the three part questions:

- (a) `zaremsky-3-10a-out-fm-in-some-aut-fn-resolved`: does every `Out(F_m)`
  embed in some `Aut(F_n)`?
- (b) `zaremsky-3-10b-closed-mcg-in-some-out-fn-resolved`: does every
  `MCG(S_g)` embed in some `Out(F_n)`?
- (c) `zaremsky-3-10c-closed-mcg-in-some-aut-fn-resolved`: does every
  `MCG(S_g)` embed in some `Aut(F_n)`?

Never write a `requires: []` route into this claim or into the part questions.

## Reading

- `S_g` is the closed orientable surface of genus `g`. For a finite-type
  surface with a puncture or boundary component the answer is already yes
  (`punctured-surface-mcgs-virtually-embed-in-aut-free-groups` together with
  `aut-free-embeddability-passes-to-finite-index-overgroups`), so the closed
  case is the question.
- `MCG` is the orientation-preserving mapping class group. For (a) and (c) the
  extended group gives the same question, since both depend only on
  finite-index subgroups.
- "Embed" means an injective homomorphism. `m` and `g` range over all
  nonnegative integers.
- Context: the problem was added in the same month as Belk--Fournier-Facio--
  Hyde--Zaremsky, arXiv:2503.21882 (March 2025). Their Section 4 leaves the
  Boone--Higman conjecture open exactly for `Out(F_n)`, `n ≥ 3`, and for
  closed-surface mapping class groups of genus `≥ 3`. An embedding into some
  `Aut(F_n)` settles those cases through their Theorem A
  (`out-fn-bh-via-virtual-embedding-in-aut-fn`, `closed-mcg-bh-via-aut-free-host`).

## What is known

- **Small cases, yes.** `m ≤ 2` (`low-rank-out-free-groups-embed-in-aut-free-groups`)
  and `g ≤ 2` (`low-genus-closed-mcgs-embed-in-aut-free-groups`).
- **Hosts need large rank.** `n ≥ m` for `Out(F_m)` and `n ≥ 2g − 1` for
  `MCG(S_g)`, `g ≥ 2` (`rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`).
- **Finite index suffices.** Parts (a) and (c) depend only on finite-index
  subgroups, and (c) implies (b)
  (`aut-free-embeddability-passes-to-finite-index-overgroups`). So (a) at rank
  `m ≥ 3` is equivalent to the Boone--Higman lane's premise
  `out-free-groups-virtually-embed-in-aut-free-groups`.
- **Natural constructions die or reduce.** Covering-lift constructions are
  virtual sections (`outer-covering-lifts-are-virtual-sections`). The Birman
  sequence has none in genus `≥ 4` (Chen--Salter,
  `birman-exact-sequence-does-not-virtually-split`) or genus 3
  (`birman-sequence-genus-three-does-not-virtually-split`, unreviewed).
  Splitting-compatible homomorphisms into a larger `Aut(F_n)` are virtual
  sections of `Aut(F_m) → Out(F_m)` for `m ≥ 4`
  (`free-splitting-compatible-aut-lifts-are-virtual-sections`), and whether
  those exist is undecided.
- **Literature (bounded, 2026-09-13).** The status table
  `research/artifacts/zp-open-status-sections-2-4-2026-09-13-part2.md` found
  nothing deciding either question. Its search summary lists Out-to-Out
  embeddings `Out(F_m) → Out(F_N)` for `N = r^m(m − 1) + 1`, `r` coprime to
  `m − 1` (Bogopolski--Puga; Bridson--Vogtmann), not re-read here; they do not
  land in `Aut`.

## Attempts

- 2026-09-13, lane z3-10-out-aut-embed: the structure above. Nothing is
  decided for `m ≥ 3` or `g ≥ 3`.
  - **Sharpest positive crux:** an injective homomorphism from some
    finite-index subgroup of `Out(F_m)` (resp. `MCG(S_g)`) into any `Aut(F_k)`.
    It need not lift the outer action and need not preserve any free factor.
  - **Sharpest negative crux:** an obstruction that survives passing to
    finite-index subgroups and separates `Out(F_m)` or `MCG(S_g)` from all
    subgroups of automorphism groups of free groups. Torsion alone cannot do it
    for (a) and (c).
