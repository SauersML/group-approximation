---
rg: 2
id: pgl-n-q-acts-on-rational-polyhedral-cantor-set
kind: claim
title: PGL_n(Q) acts faithfully on the Cantor set of rational polyhedral regions of RP^(n-1); for n = 2 it is the blow-up at P^1(Q) carrying standard V, and non-integral elements are singular everywhere there
distinct_from:
  gl-n-q-targets-are-cofinal-in-n: that reduces the root to PGL_n(Q) for infinitely many n; this gives PGL_n(Q) a canonical Cantor-set action, the setting of the Cantor host criteria.
  fp-cantor-groups-containing-v-type-a-iff-clopen-stabilizer-fg: that is the host criterion for finitely presented Cantor groups containing standard V; this supplies a Cantor action of PGL_n(Q) to which it can be applied when n = 2, and records why the germ-extension criteria cannot be.
artifacts:
  - research/artifacts/gq-gq-pp-simple-exits.md
---

**ESTABLISHED** by `pgl-n-q-acts-on-rational-polyhedral-cantor-set-proof` (elementary;
not independently reviewed; no novelty claimed). Item 3 uses the standard identification
of Thompson's `T` with the piecewise-`PSL_2(Z)` homeomorphisms of `RP^1`, cited, not
re-derived.

## Statement

Let `n >= 2`. Call a subset of `RP^(n-1)` a **rational region** if it is the interior of
the closure of a union of chambers (connected components of the complement) of a finite
arrangement of projective hyperplanes defined over `Q`. Let `𝔅_n` be the set of rational
regions.

1. `𝔅_n` is a countable atomless Boolean algebra, a subalgebra of the regular open
   algebra of `RP^(n-1)`. So its Stone space `S_n` is a Cantor set.
2. `PGL_n(Q)` permutes rational hyperplanes, so it acts on `𝔅_n` by Boolean
   automorphisms, and hence on `S_n` by homeomorphisms. This action is faithful. By
   `gl-n-q-targets-are-cofinal-in-n`, every `GL_k(Q)` embeds in some `PGL_n(Q)`, so
   every `GL_k(Q)` acts faithfully on a Cantor set this way.
3. **n = 2.** `S_2` is `RP^1` with each point of `P^1(Q)` replaced by a left and a right
   copy. Under the standard homeomorphism of `RP^1` onto `R/Z` carrying `P^1(Q)` onto the
   dyadic points, which conjugates the piecewise-`PSL_2(Z)` homeomorphisms with rational
   breakpoints onto Thompson's `T` (survey arXiv:2306.16356v3, Remark 5.5, citing
   Greenberg and Cannon–Floyd–Parry §7), `S_2` becomes `{0,1}^N` and `T <= V` act in their
   standard form. So `Γ_2 = <V, PGL_2(Q)>` is a group of homeomorphisms of the standard
   Cantor set containing standard `V`, and every finitely presented `Γ` with
   `V <= Γ <= Homeo(S_2)` falls under
   `fp-cantor-groups-containing-v-type-a-iff-clopen-stabilizer-fg`.
4. **Singular everywhere (n = 2).** Every piece of an element of `V` is an element of
   `PSL_2(Z)` in these coordinates. Two Möbius maps that agree on an open arc are equal. So
   an element `g ∈ PGL_2(Q)` outside `PGL_2(Z)` agrees with no element of `V` on any open
   arc. It is a non-`V` germ at every point, and `<V, g>` is not a finite germ extension
   of `V`. Its orbits can also be strictly larger than those of `V`: `x ↦ 2x` maps `√2`
   to `2√2`, which is not in `PSL_2(Z)·√2`. So neither Belk–Hyde–Matucci Theorem 1.3
   (same orbits) nor their finite-presentation theorems (finite singular sets) apply to
   hosts built on this model. Only the exits that need no germ structure apply: the
   clopen-stabilizer type (A) criterion, and the finite-index monolith of
   `sl-m-q-passes-to-finite-index-and-commutator-cores`.

## Attempts

Proved; see the proof route. Open follow-ups (not claimed):
- a finitely presented `Γ` between `V` and `Homeo(S_2)` containing `PSL_2(Q)`;
- a higher-dimensional analogue of `V` on `S_n` (piecewise-`PGL_n(Z)` rational scissors)
  that contains standard `V`.
