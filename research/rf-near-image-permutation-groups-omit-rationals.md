---
rg: 2
id: rf-near-image-permutation-groups-omit-rationals
kind: claim
title: A permutation group whose near image is residually finite, such as a Houghton group, contains no (Q,+) and so none of Aff(Q), U_3(Q), SL_n(Q), GL_n(Q)
distinct_from:
  fp-alt-fin-hosts-have-fp-near-images: that is the general lemma placing a subgroup in the near image modulo its locally finite radical; this is its application to Houghton-type hosts, where the near image is residually finite.
  lifts-add-no-unipotent-divisibility: that excludes central and covering lifts of groups without (Q,+); this excludes finitary extensions of residually finite near actions.
  germ-extensions-omit-standard-gl-n-q: that bounds the globally projective elements of piecewise-projective groups and their germ extensions; this concerns permutation groups of a discrete set modulo finitary permutations, and excludes every copy of (Q,+), standard or not.
  houghton-h2-is-not-fp2-over-q: that is a finiteness property of the Houghton group H_2; this is a subgroup obstruction for every Houghton group.
---

**ESTABLISHED** through `rf-near-image-permutation-groups-omit-rationals-proof`.
Elementary, lane-proved, not independently reviewed. This is test T1 of
`research/artifacts/gq-gq-calibration-worlds.md`, stated for this host class;
no priority is claimed.

## Statement

Let `X` be a set and `Γ <= Sym(X)`. Suppose the near image
`Γ* = Γ/(Γ ∩ FSym(X))` contains no subgroup isomorphic to `(Q,+)`; for
example, `Γ*` residually finite. Then `Γ` contains no subgroup isomorphic to
`(Q,+)`. Hence `Γ` contains none of `Aff(Q)`, `B_2(Q)`, `U_n(Q)` (`n >= 2`),
`SL_n(Q)`, `GL_n(Q)`, `PGL_n(Q)` (`n >= 2`), all of which contain `(Q,+)`.

## Houghton-type hosts covered

The hypothesis holds whenever `Γ` has a homomorphism to a residually finite
group with kernel exactly `Γ ∩ FSym(X)`. In particular:

1. **Houghton groups** `H_n`, `n >= 1`. Here `X = {1..n} x N` and `H_n`
   consists of the permutations that are eventually translations
   `(i, m) -> (i, m + t_i)` on each ray. The map `g -> (t_1, ..., t_n)` is a
   homomorphism to `Z^n` whose kernel is the set of finitary elements, and its
   image is `{t : Σ t_i = 0} ≅ Z^(n-1)`. The same applies to every subgroup of
   `H_n`.
2. **Eventually in a residually finite permutation group.** Let `L <= Sym(X)`
   be residually finite with `L ∩ FSym(X) = 1`, and let every `g ∈ Γ` agree
   with some `l(g) ∈ L` outside a finite set. Then `l(g)` is unique, `g -> l(g)`
   is a homomorphism with kernel `Γ ∩ FSym(X)`, and the hypothesis holds.
   Examples of `L`:
   - `Aff(Z^k) = Z^k x| GL_k(Z)` or `Isom(Z^k)` on `X = Z^k`, `k >= 1`: a
     nontrivial affine map of `Z^k` moves infinitely many points, and `L` is
     finitely generated linear, hence residually finite (Mal'cev);
   - `Aut(T)` on the vertices of a locally finite rooted tree `T` in which
     every vertex has a child: a nontrivial automorphism moves a vertex and
     hence the infinite subtree below it, and `Aut(T)` is residually finite,
     since it acts faithfully on the union of the finite balls around the root;
   - any finitely generated linear group acting on `X` with no nontrivial
     finitary element.

## What survives

A finitary-alternating host for any of the groups listed needs a near image
that already contains `(Q,+)` (see `fp-alt-fin-hosts-have-fp-near-images`).
Known finitely presented groups containing `(Q,+)`, such as Ghys--Sergiescu's
`T-bar` acting on the dyadic rationals of `R`, or `VA` acting on clopen sets,
give near images `T-bar` and `VA`. `T-bar` contains no `Aff(Q)`, `U_3(Q)` or
`GL_n(Q)` (`lifts-add-no-unipotent-divisibility`), and `VA` contains no
`SL_3(Z)` (survey Remark 4.12), so no `GL_n(Q)` for `n >= 3`. Whether `VA`
contains `Aff(Q)` or `GL_2(Q)` is not settled here.
