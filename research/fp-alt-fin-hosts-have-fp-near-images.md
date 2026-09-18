---
rg: 2
id: fp-alt-fin-hosts-have-fp-near-images
kind: claim
title: A finitely presented permutation group containing the finitary alternating group has a finitely presented near image, and every subgroup embeds there modulo a locally finite normal subgroup
distinct_from:
  fp-finitary-alternating-overgroups-have-type-a-actions: that shows the action of such a group on its set is of type (A); this passes to the quotient by the finitary part, shows that quotient is finitely presented, and tracks where a subgroup goes.
  permutational-host-forms-agree-for-countable-inputs: that proves the finitary-alternating host form equivalent to membership in B_A; this is a structural lemma about any such host, used to bound what the finitary part can contribute.
  finitary-symmetric-extensions-of-oligomorphic-actions-are-fp: that gives sufficient conditions for FSym(S) x| G to be finitely presented; this gives a necessary condition, finite presentation of the near image, for any finitary-alternating host.
  lampshuffler-groups-are-not-fp2-over-q: that shows one family of candidate hosts is not FP_2; this shows that f.p. hosts always come with an f.p. quotient carrying the whole of any subgroup without locally finite normal subgroups.
---

**ESTABLISHED** through `fp-alt-fin-hosts-have-fp-near-images-proof`.
Elementary hand proof, lane-proved, not independently reviewed. No novelty is
claimed for items 1–3; the point is the consequence for `GL_n(Q)` (item 4).

## Setting

Let `X` be an infinite set, `FSym(X)` the finitary symmetric group and
`Alt_fin(X)` its finitary alternating subgroup. Let `Γ <= Sym(X)` with
`Alt_fin(X) <= Γ`. Put `Γ_fin = Γ ∩ FSym(X)` and call
`Γ* = Γ/Γ_fin`, the image of `Γ` in `Sym(X)/FSym(X)`, the **near image** of `Γ`.
It carries the faithful near action of `Γ` on `X`.

## Statement

1. `Γ_fin` is `Alt_fin(X)` or `FSym(X)`. In either case it is the normal
   closure in `Γ` of one element: a 3-cycle, respectively a transposition.
2. If `Γ` is finitely presented, then `Γ*` is finitely presented. If `Γ` is
   finitely generated, so is `Γ*`.
3. For every subgroup `H <= Γ`, `H ∩ FSym(X)` is a locally finite normal
   subgroup of `H`, and `H/(H ∩ FSym(X))` embeds in `Γ*`. So every subgroup of
   `Γ` without nontrivial locally finite normal subgroups embeds in `Γ*`.
4. **The rational groups.** The largest locally finite normal subgroup is
   - trivial for `(Q,+)`, for `Aff(Q) = Q x| Q^x`, for `U_n(Q)`, for
     `PGL_n(Q)` (`n >= 2`) and for `SL_n(Q)` with `n` odd;
   - contained in `{±I}` for `GL_n(Q)` and `SL_n(Q)`, `n >= 2`.

   Hence if `Γ` is finitely presented and contains `GL_n(Q)` (`n >= 2`), then
   `Γ*` is a finitely presented group, with a faithful near action on `X`,
   that contains `GL_n(Q)/K` for some `K <= {±I}`. It therefore contains
   `GL_(n-1)(Q)` (via `A -> diag(A,1)`), `SL_n(Q)` for `n` odd, `Aff(Q)`,
   `U_n(Q)` and `(Q,+)`. If `Γ` contains `PGL_n(Q)`, so does `Γ*`.

## Consequences

- **Form (a) of `gl-n-q-in-permutational-boone-higman-class` needs a
  finitely presented overgroup of `GL_n(Q)` first.** By item 4 and
  `gl-n-q-targets-are-cofinal-in-n`, a finitary-alternating host for all
  `GL_n(Q)` yields, for every `n`, a finitely presented group containing
  `GL_n(Q)` that acts faithfully by near permutations of `X`. So this route
  is never easier than the non-natural form of Problem 2.7
  (`gl-n-q-explicit-natural-fp-overgroup`), and an explicit host gives an
  explicit answer to that form.
- **The finitary part supplies no divisibility.** Divisible torsion-free
  subgroups, and every copy of `Aff(Q)`, `U_n(Q)` or `PGL_n(Q)`, meet
  `FSym(X)` trivially. This is the calibration test T1 of
  `research/artifacts/gq-gq-calibration-worlds.md` in its general form; the
  Houghton case is `rf-near-image-permutation-groups-omit-rationals`.
- **Only non-realizable near actions add anything.** If the near action of
  `Γ*` is induced by a genuine action of `Γ*` on `X` with finitely many orbits
  of 2-subsets and finitely generated point stabilizers, then `Γ*` is already
  a type (A) actor and the passage to `Γ` gains nothing. Houghton's groups
  `H_n`, `n >= 3`, show that finite presentation of `Γ` can come from a near
  action whose image (`Z^(n-1)`) has no faithful action with finitely many
  orbits of 2-subsets. Such a mechanism would have to be found for a
  finitely presented overgroup of `GL_n(Q)`.
