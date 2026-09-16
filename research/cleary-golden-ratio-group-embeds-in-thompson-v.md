---
rg: 2
id: cleary-golden-ratio-group-embeds-in-thompson-v
kind: claim
title: Cleary's golden-ratio Thompson group F_τ embeds in Thompson's group V
distinct_from:
  stein-group-f23-does-not-embed-in-thompson-v: that excludes the Stein group F_{2,3}, whose endpoint germ group Z^2 is not cyclic, from V; this asks whether F_τ, whose germ group <τ> is cyclic, embeds in V
  wreath-z-by-z2-embeds-in-thompson-v: that asks about the metabelian wreath product and is refuted by Corwin's thesis; this asks about the irrational-slope Thompson group
  cleary-golden-ratio-group-does-not-embed-in-thompson-f: that excludes F_τ from the smaller group F (Hyde–Moore) and does not decide embeddings into V; this asks whether F_τ embeds in V
---

Let `F_τ = F([0,1]; Z[τ], ⟨τ⟩)` with `τ = (√5 − 1)/2`. This is Cleary's irrational-slope
Thompson group, as in `cleary-golden-ratio-group-does-not-embed-in-thompson-f`. The claim
is that `F_τ` is isomorphic to a subgroup of Thompson's group `V`.

With `cleary-golden-ratio-group-does-not-embed-in-thompson-f`, this would answer the
reposed Zaremsky Problem 2.15 negatively (route
`biorderable-v-subgroup-not-in-f-via-golden-ratio-group`).

**Status (checked 2026-09-16).** Open. Hyde–Skipper–Zaremsky (arXiv:2605.20564v2, closing
remark, TeX source) write:

> "Since $\langle \tau\rangle$ is cyclic, we cannot rule out $F_\tau$ embedding in $V$
> using our methods, but $F_\tau$ does not embed in $F$ [Corollary 1 of Hyde–Moore], and
> we expect it should also not embed in $V$."

So the experts expect this claim to be false. It is named because it is the sharpest
known test case for the negative answer.

## Attempts

- 2026-09-16 (swarm lane, zaremsky-2-15b). Every obstruction to embedding in `V` known to
  this lane was checked; none applies.
  - *Dead: distorted cyclic subgroups.* Burillo–Cleary–Röver (arXiv:1402.3860v2, TeX
    checked) prove that cyclic subgroups of `V` are undistorted, so a group with a
    distorted cyclic subgroup is not in `V`. But every cyclic subgroup of a finitely
    generated `G ≤ PL_+([0,1])` is undistorted. *Proof.* For `w` in `G` put
    `σ(w) = max_x |log w'(x+)|`. The chain rule `(uv)'(x+) = u'(v(x)+)·v'(x+)` gives
    `σ(uv) ≤ σ(u) + σ(v)`, so `σ(w) ≤ c·|w|_S` for a finite generating set `S`. If
    `g ≠ 1`, then at the left endpoint `p` of a bump of `g`, `λ = g'(p+) ≠ 1` and
    `(g^n)'(p+) = λ^n`. So `|g^n|_S ≥ n·|log λ|/c`. `F_τ` is finitely generated
    (`irrational-slope-f-tau-is-of-type-f-infinity`), so this obstruction is empty for it.
    The same holds for `F_{3/2}`.
  - *Dead: Corwin and Bleak–Salazar-Díaz.* `Z ≀ Z^2` is not a subgroup of `F_τ`. Theorem
    N4 of `research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part2.md`
    covers subgroups of `PL_+(I)` with slopes at fixed points in a cyclic group, and `F_τ`
    has slopes in `⟨τ⟩`. `Z * Z^2` is not a subgroup of `F_τ` either, since `F_τ` has no
    free subgroups (Brin–Squier).
  - *Dead: germ obstructions at hyperbolic periodic points.* These exclude `BS(1,n)` and
    non-abelian torsion-free nilpotent groups from `V` (part 3; the input V0 has a direct
    proof in `research/artifacts/infinite-order-v-elements-hyperbolic-points-2026-09-16.md`).
    Neither kind of group is a subgroup of `PL_+(I)` (`bs-1-n-does-not-embed-in-pl-plus-interval`
    and `nilpotent-subgroups-of-pl-plus-interval-are-abelian`).
  - *Dead: Hyde–Skipper–Zaremsky semiconjugacy rigidity.* It needs a non-cyclic germ
    group at infinity. The authors say so in the remark quoted above.
  - *Open: co-context-freeness.* `V` is co-context-free (Lehnert–Schweitzer, Bull. LMS
    2007, not re-read this session), so finitely generated subgroups of `V` are
    co-context-free. Showing that the co-word problem of `F_τ` is not context-free would
    refute this claim. Not attempted.
  - *Open: context-free actions.* By Bodart–D'Angeli–Perego–Rodaro (arXiv:2608.02111,
    abstract only), this claim is equivalent to `F_τ` having a faithful context-free
    action. Not attempted.
  - *Heuristic only: the golden-base Cantor model.* `F_τ` acts on the space of infinite
    paths of its two-caret subdivision tree. Changing to a fixed binary coding, such as
    always splitting in the ratio `τ : τ^2`, seems to need golden-base normalisation with
    carries. That looks like an asynchronous transducer with memory rather than a finite
    prefix replacement. This is not checked, and it does not exclude other embeddings.
  - *Sibling candidate.* `F_{3/2}` (slopes in `⟨3/2⟩`, breakpoints in `Z[1/6]`) is not a
    subgroup of `F` (Belk–Hyde–Moore, arXiv:2211.05825, abstract). HSZ "do not know
    whether $F_{\frac{3}{2}}$ embeds in $V$". The same four obstructions fail for it for
    the same reasons.
