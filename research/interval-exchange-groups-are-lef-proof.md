---
rg: 2
id: interval-exchange-groups-are-lef-proof
kind: route
title: Proof that finitely generated interval exchange groups are LEF, by rational specialisation
target: interval-exchange-groups-are-lef
requires: []
---

Let `G = <g_1, ..., g_k>` be a group of interval exchanges of `T = R/Z`, with the
generating set closed under inverses. Normalise every breakpoint and translation of
every generator into `[0, 1)`, and list all of them as a parameter vector `P ∈ R^N`.

**1. Candidate points and elementary arcs.** Fix `m`. For a word `w` of length at most
`m` and a point `x`, the itinerary of `x` (which piece of which generator is used at
each step) determines `w(x) = x + s` modulo 1, where `s` is a sum of at most `m`
generator translations. So every breakpoint of `w` is a point `a - s` modulo 1, with `a`
a breakpoint of some generator and `s` a sum of at most `m` translations. Call these the
*candidate points of level m*. As real numbers they are values `⟨c, P⟩` of linear forms
with `c ∈ Z^N` and `|c|_1 <= m + 1`.

**2. A finite sign vector decides the combinatorics.**
- Every quantity compared along an itinerary is a candidate point, a candidate point
  moved by a sum of at most `m` translations, a generator breakpoint, or a difference of
  two sums of at most `m` translations. Each comparison modulo 1 is the sign of an affine
  form `⟨c, P⟩ + k` with `c ∈ Z^N`, `|c|_1 <= 2m + 2`, and, since the entries of `P` lie
  in `[0, 1)`, an integer `|k| <= 2m + 3`.
- Let `Φ_m` be the finite set of all affine forms `⟨c, P⟩ + k` with `c ∈ Z^N`,
  `|c|_1 <= 2m + 2` and `k ∈ Z`, `|k| <= 2m + 3`. Its signs at `P` decide the cyclic
  order on `T` of all candidate points of level `m`, including coincidences, and every
  comparison below.
- Once the signs of `Φ_m` are fixed, the elementary arcs between consecutive candidate
  points are fixed combinatorially, and which of them are degenerate is fixed. Every
  prefix of every word of length at most `m` maps each elementary arc into a single piece
  of the next generator, because the preimages of generator breakpoints under prefixes
  are candidate points. So the translation of each word on each elementary arc is a
  determined sum `d` of generator translations.
- Pieces are half-open on the right, so a word is determined by its translations on the
  nondegenerate elementary arcs. Hence two words `u, v` of length at most `m` are equal
  in `G` iff, on every nondegenerate elementary arc, their translation sums `d_u, d_v`
  satisfy `⟨d_u - d_v, P⟩ + k = 0` for some `|k| <= 2m + 3`. That is a condition on the
  sign vector of `Φ_m`.

**3. Bijectivity is a sign condition too.** Let `Ψ` be the affine forms deciding the
cyclic order of the breakpoints `a_j` of each generator and of the image endpoints
`a_j + t_j`. A choice of parameters with the same signs on `Ψ` as `P` defines, for each
generator, a piecewise translation whose piece images tile `T` in the same pattern, hence
a bijection.

**4. Rational specialisation.** Fix `n` and put `Σ = Φ_(2n) ∪ Ψ`. The set of `Q ∈ R^N`
with `sign φ(Q) = sign φ(P)` for all `φ ∈ Σ` is the intersection of the affine subspace
cut out by the forms that vanish at `P` with the open set where the remaining forms keep
their strict signs. The subspace is defined by equations with integer coefficients, so
its rational points are dense in it, and the open condition holds near `P`. Choose a
rational `P'` in this set.

**5. The finite group.** Let `g_i'` be the interval exchange with parameters `P'`, which
is a bijection by step 3. Let `q` be a common denominator of the entries of `P'`. Each
`g_i'` has breakpoints and translations in `(1/q)Z`, so it permutes the arcs
`[j/q, (j + 1)/q)`. So `G' = <g_1', ..., g_k'>` embeds in `Sym(q)` and is finite.

**6. The local embedding.** Let `B_n` be the ball of radius `n` in `G`. Define
`φ(g) = w(g_1', ..., g_k')` for any word `w` of length at most `n` representing `g`.
- By step 2 at level `2n` and the choice of `P'`, two words of length at most `2n` are
  equal in `G` iff they are equal in `G'`. So `φ` is well defined and injective on `B_n`.
- If `g, h, gh ∈ B_n` are represented by words `u, v, w` of length at most `n`, then the
  word `uv` of length at most `2n` equals `w` in `G`, hence in `G'`. So
  `φ(g) φ(h) = φ(gh)`.

So for every `n` the ball `B_n` embeds partially multiplicatively in a finite group, and
`G` is LEF. ∎
