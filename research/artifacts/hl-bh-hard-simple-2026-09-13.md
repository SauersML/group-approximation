# Arbitrarily complex finitely presented simple groups: lane hl-bh-hard-simple, 2026-09-13

Target: `fp-simple-groups-with-arbitrarily-complex-word-problem`, together with
`fp-simple-dehn-functions-have-no-recursive-upper-bound` and
`type-a-actors-with-arbitrarily-hard-word-problem`.

Verdict: not solved. One obstruction landed:
`orbit-preserving-germ-corollary-extensions-of-v-are-rational`.

## 1. Provenance pins

**Birget, *Circuits, coNP-completeness, and the groups of Richard Thompson*,
arXiv:math/0310335.** Source file `Thconp.tex`, fetched from the arXiv e-print
on MSI 2026-09-13, lines 221–250:

> Another motivation for this paper is a conjecture attributed to Higman
> about a stronger form of the Boone-Higman theorem. The conjecture is that
> a finitely generated group $G$ has decidable word problem iff $G$ is
> embeddable into a finitely presented simple group.

> A consequence of this conjecture would be that the word problem of finitely
> presented simple groups can have arbitrarily large time complexity. This
> means that for every function $T$ which is the time complexity of a
> deterministic Turing machine, there is a finitely presented simple group
> whose word problem cannot be decided in time $\leq T$.

> On the other hand, all known finitely presented simple groups have word
> problems with rather low complexity (in the cases where the complexity has
> been analyzed in detail it always turned out to be in the complexity class
> P).

> So, one might ask the opposite question:
> {\it Is there some cap on the computational complexity of
> the word problem of finitely presented simple groups? }
> At the moment, neither Higman's conjecture nor the opposite question have
> much evidence in their favor (and, a priori, they could both be wrong).

Lines 63–66 of the same file: "Madlener and Otto \cite{MO} gave a version of the
Higman embedding theorem that preserves the Grzegorczyk hierarchy from level 3
upward."

So the root is Birget's reading of a consequence of the stronger Boone–Higman
conjecture he attributes to Higman. As of that paper the opposite "cap" question
was also open.

**Zaremsky, *Finitely presented simple groups with at least exponential Dehn
function*, arXiv:2305.15176 (v2, 11 July 2024).** Abstract, from the arXiv page:
"We construct examples of finitely presented simple groups whose Dehn functions
are at least exponential. To the best of our knowledge, these are the first such
examples known. Our examples arise from Röver-Nekrashevych groups, using
carefully calibrated self-similar representations of Baumslag-Solitar groups."

This matches the "quasi-retract examples stop at exponential" line of
`fp-simple-dehn-functions-have-no-recursive-upper-bound`.

**No later answer found.** A web search on 2026-09-13 found no construction of
finitely presented simple groups beyond a fixed recursive complexity bound. It
did find Llosa Isenrich–Schesler–Wu, arXiv:2510.01952, which separates
homological finiteness properties and says nothing about complexity. This was
one search session, not a systematic survey.

## 2. Belk–Hyde–Matucci definitions used

From `2407.03149.txt` on MSI (`/scratch.global/sauer354/bh-reviewer/`), lines
45–56. Ligatures were lost in extraction and are restored here.

> If h ∈ Homeo(X), the singular points of h are the set
> sing(h) = { p ∈ X : h does not agree with any element of B on any neighborhood of p }.
> A group G ≤ Homeo(X) will be called a finite germ extension of B if it satisfies
> the following conditions:
> (1) Every element of G has only finitely many singular points.
> (2) G contains B, and indeed B is precisely the subgroup of G consisting of all
> elements that have no singular points.
> (3) For every g ∈ G and p ∈ sing(g), there exists an h ∈ G with sing(h) = {p}
> such that h agrees with g on some neighborhood of p.

Corollary 2.10 hypotheses (2) and (3), as quoted in
`research/artifacts/shell-envelope-local-tests-2026-09-13.md`:
- (2) "Fix_B(M) has type F_n for each M ⊆ sing(G) with 0 ≤ |M| ≤ n";
- (3) "Either |(G)_p : (B)_p| < ∞ for each p ∈ sing(G), or (B)_p ⊴ (G)_p for each
  p ∈ sing(G) and (G)_p/(B)_p has type F_n".

## 3. The obstruction

`orbit-preserving-germ-corollary-extensions-of-v-are-rational`, route
`orbit-preserving-germ-corollary-rationality-proof`, elementary.

With `B = V` on `{0,1}^N`:
- hypothesis (2) for singletons forces every singular point to be eventually
  periodic;
- the either-or of (3) makes every germ fixing a singular point commute with a
  power of the periodic shift, hence rational;
- if singular transports stay inside `V`-orbits, every element is rational.

So these groups lie in `F(2^n)`, and so do all their subgroups.

**What it rules out.** The cheap Corollary 2.10 branch of the finite-germ hosts,
in the orbit-preserving case, can't produce a witness for the root. This covers
the virtually cyclic positive controls of the shell route.

**What it leaves.**
- Theorem 2.1 hosts whose germ groups normalize no finite-index subgroup of the
  `V`-germs. Shell envelopes of non-virtually-cyclic inputs are of this kind
  (`shell-isotropy-germs-fail-bhm-germ-hypothesis`).
- Singular transports between different `V`-orbits. Here `g τ_q^N = σ g` makes
  only `σ` rational, and `g` near `q` may apply the `k`-th iterate of an annulus
  map at depth `k`.

## 4. Routes examined and set aside (no node)

1. **Iterated twisted Brin–Thompson towers.** Already dead on main (one exponential
   per round).
2. **Hard stabilizers inside Thompson-like actors.**
   - A fixing germ at an aperiodic point is trivial, so point stabilizers of
     aperiodic points in `V` are not finitely generated (Step 1 of the route).
   - Rational-point stabilizers have easy membership (compute the germ exponent).
   - So hard stabilizer membership needs a non-rational actor.
3. **Distortion amplification.** Suppose an element simulating a Turing machine
   in `2V` is conjugated to its square inside some host. Then short words encode
   runs of exponential length. Tower distortion (Baumslag–Gersten-type) only
   gives elementary lower bounds. Beating an arbitrary recursive `T` needs
   distortion at least `T` in the host, which is itself a computational-
   universality requirement. Proper-power conjugates are also obstructed in many
   hosts (`graph-path-almost-automorphism-proper-power-is-equicontinuous`,
   `rsg-proper-power-conjugate-germs-torsion-at-finite-orbits`).
4. **Unique hard configurations on the scale tree** (Attempt 6 of
   `hard-half-finite-permutations-have-fp-shift-envelopes`).
   - Forcing that propagates only toward larger scales gives values computable by
     dynamic programming in polynomial time.
   - A hard witness therefore needs non-causal global forcing: constraints from
     scales about `log T(x)` above `x`.
   - Nothing on main certifies finite presentation for any such rule.

## 5. Exact gap

For every recursive `T`, one of the following:
- a finitely presented group with a faithful type (A) action outside `F(T)`;
- a finitely presented self-similar group outside `F(T)`;
- a finitely presented finite germ extension of `V` that uses Theorem 2.1 with
  non-normalizing germ groups or cross-orbit transports.

Every known host family lies in `F(2^(2^n))` or below.
