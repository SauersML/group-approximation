# Zaremsky Problem 2.20 (faithful 2-transitive action of F): swarm notes, 2026-09-16

## Setup

Target: `zaremsky-2-20-f-faithful-2-transitive-action`. The two answer claims
are `thompson-f-admits-a-faithful-2-transitive-action` and
`thompson-f-has-no-faithful-2-transitive-action`. The "no" claim was locked by
another agent, so I did not edit it. I worked on a new sub-hole of the "no"
direction: necessary conditions that any 2-transitive action must satisfy,
stated as checkable tests on a candidate point stabilizer `H`.

Lock held: `thompson-f-two-transitive-hull-endpoints-are-rational` (created by
me, then locked; `bin/cairn lock` refuses unknown ids, so the claim file had to
exist first).

Standing facts used (all landed in the graph and "established" per check.sh):
`thompson-f-two-transitive-actions-are-faithful`,
`thompson-f-two-transitive-actions-satisfy-grid-condition` (from Le
Boudec–Matte Bon Prop. 5.1, case (2)).

Notation: `F_x^-`, `F_x^+` rigid stabilizers of `[0,x]`, `[x,1]`;
`I^-(ω,ω') = {x : ω' ∈ F_x^- ω}` (up-set), `I^+` (down-set);
`η = inf I^-`, `ξ = sup I^+` (hull endpoints).

## What was proven

### Lemma A: `thompson-f-two-transitive-hull-endpoints-are-rational`

Route `thompson-f-two-transitive-hull-endpoints-rational-proof` (requires
faithfulness and the grid claim). Content:

1. `I^±` nonempty and proper, symmetric, `F`-equivariant; so `0 < ξ ≤ η < 1`.
   Nonempty: `N_1 = ∪_{x<1} F_x^-` is a nontrivial normal subgroup of a
   primitive faithful action, hence transitive. Proper: if some `F_x^-` were
   transitive, the grid would make `F_x^+` act trivially.
2. Every swap `s` of `{ω,ω'}` fixes `η, ξ` and is the identity on no open
   interval around them. Key trick: if `s = id` on `[y,x]` around `η`, cut
   `s = s_- s_+` there. Grid injectivity at `x` (with `a ∈ F_x^-`, `aω = ω'`)
   forces `s_- ω = ω'`, so `y ∈ I^-`. Contradiction.
3. Hence `η, ξ` are rational (a swap is affine near a non-dyadic fixed point
   with slope `2^k`, `k ≠ 0`).
4. All `η` lie in one `F`-orbit `Θ^-`, all `ξ` in one orbit `Θ^+`, by invariant
   symmetric relations.
5. Germ statement: `ρ(s) ∉ L = ρ(F_ω ∩ F_ω')`, `ρ(s)^2 ∈ L`, in `Γ_p`.

Test: `η(ω,gω) = g(inf Z)`, `Z = {z : g agrees on [z,1] with some h ∈ H}`. A
candidate `H` dies if this is irrational for some `g`, or if two pairs give
endpoints in different orbits.

### Lemma B: `thompson-f-two-transitive-dyadic-branching-is-binary`

Route `thompson-f-two-transitive-dyadic-branching-binary-proof` (requires the
grid claim and Lemma A). With `M_p = ∪_{y<p} F_y^-` and `λ_p` the log left slope
at dyadic `p`:

- `F_p^- ω` is one or two `M_p`-orbits, and `λ_p(H ∩ F_p^-)` is `Z` or `2Z`.
  Proof idea: `H_p = Stab_H(p)` fixes every branch, because conjugation by `h`
  preserves left slopes at `p`. It is also transitive on
  `T_p = {ω' : η(ω,ω') = p}`, and every non-trivial branch lies in `T_p`.
- Dichotomy: two branches somewhere iff `Θ^-` is the dyadic orbit and every
  pair attains its endpoint (`ω' ∈ F^-_η ω`). Then the two-branch points for `ω`
  are exactly the `H`-orbit `P_ω` of endpoints.
- Parity: in that case every `h ∈ H` fixing `p ∈ P_ω` has even log left slope
  at `p` (via the grid splitting at `p`). Every swap can be replaced by a swap
  in `F_p^-` of odd slope.

So a stabilizer is of "kind I" (full slopes at every dyadic point, no dyadic
endpoint attained) or "kind II" (Jones-type parity on the dense orbit `P_ω`).

check.sh on the four research files: exit 0.

## Approaches and where each dies

1. **Endpoint germs at 0 and 1.** Idea: an invariant of `g ∈ F` near `1`
   that `H` must respect. Dies right away: `N_1` is transitive, so
   `F = H N_1` and `H` surjects onto the germs at `1`. There is no constraint
   at the endpoints of `[0,1]`. Constraints must come from interior points,
   which is why I turned to hull endpoints.

2. **Hull endpoints (Lemma A).** Works, and gives rationality and a single
   orbit. It does not decide whether `Θ^-` is dyadic or non-dyadic rational.
   In the non-dyadic case, `Γ_p ≅ Z`, `L` has even index, and swaps have slope
   `2^k`, `k ≠ 0`, at `p`. I found no contradiction there.

3. **Branching at dyadic points (Lemma B).** Works, and gives the kind I /
   kind II dichotomy. It dies at the next step: neither kind is contradictory
   with what I could prove.
   - Kind I: `λ_p(H ∩ F_p^-) = Z` for every dyadic `p` says `H` has elements
     of every left slope supported left of `p`. That does not force `H` to
     contain a rigid stabilizer, so it does not contradict
     `thompson-f-two-transitive-rigid-stabilizers-fix-no-point`. I tried to
     show that a non-attained dyadic endpoint (`ω' ∈ F_x^- ω` for all `x > p`
     but not at `p`) leads to a contradiction, using swaps and the grid at
     `x ↓ p`. The cut pieces `s_-` at `x > p` are not swaps, since `s` is not
     the identity near `p`. So the argument of Lemma A step 3 does not go
     through.
   - Kind II: the parity rule on `P_ω` is exactly the slope rule of Jones'
     subgroup `\vec F`: at a dyadic `t` fixed by `g`, `t ∈ J(g)` iff the log
     left slope is odd (`jones-subgroup-cosets-form-a-parity-lamplighter`).
     So kind II is modeled by lamplighter-type cocycles, and the local
     conditions are consistent. `\vec F` is not a candidate: `χ_1(\vec F) ⊆ 2Z`,
     so `\vec F F' ≠ F` and `F/\vec F` is imprimitive. The obstruction would
     have to be global: maximality plus 2-transitivity.

4. **Set-translate candidates (LBMB's partition stabilizers).** For an action
   on `F`-translates of a subset `S` of a dyadic orbit, the swap argument
   gives: `sup(S_1 Δ S_2)` must be rational for all translates `S_1 ≠ S_2`,
   and no swap is the identity near it. Sets defined by a condition on the
   dyadic tail (suffix-defined sets) have translates with finite symmetric
   differences near the endpoints. Test T1 of
   `thompson-f-admits-a-faithful-2-transitive-action` rules these out. I did
   not find a partition-stabilizer candidate that passes Lemma A and Lemma B.
   I also found no proof that none exists.

5. **Analogues.** I looked for a group acting on the line, with the LBMB
   hypotheses (no global fixed point, `G^0 ≠ 1`), that has a faithful
   2-transitive action, to see which of kind I or kind II occurs. I checked
   free-product-like, lamplighter-like and affine (`Z[1/2] ⋊ Z`) examples
   informally. None satisfies the hypotheses with a 2-transitive action I
   could verify, so nothing was learned.

## Status and next steps

- The problem remains open. No candidate was constructed and no impossibility
  was proven.
- Most promising kill: combine kind II on the left with the mirror statement on
  the right. For a pair `(ω,ω')`, `ξ ≤ η`, and a swap `s` has odd left slope at
  `η` after cutting. It would be worth asking whether the right-side parity at
  `ξ` is compatible with the same swap. I did not finish this.
- A computational test: run the formula `η(ω,gω) = g(inf Z)` on closed maximal
  subgroups from Golan's transducer description, looking for irrational values.
  I wrote no script this session.

## Literature consulted (2026-09-16)

- M. Zaremsky, open problems document containing Problem 2.20 (PDF dated
  July 12, 2026, fetched 2026-09-16). Text was extracted crudely with zlib and a
  regex, since the PDF tools in the sandbox were broken. I relied on the root
  claim's recording of the problem. No solution is reported there.
- A. Le Boudec, N. Matte Bon, *Triple transitivity and non-free actions in
  dimension one*, arXiv:1906.05744v3 (June 16, 2021). I fetched the PDF but
  could not extract its text. For Prop. 5.1, Prop. 5.2, Cor. 5.3 and the
  partition-stabilizer question on p. 23, I relied on the verbatim quotes in
  `thompson-f-transitivity-degree-at-most-two-citation` (read by another agent
  on 2026-09-13). I did not re-verify them this session.
- arXiv:2607.04038 (dated July 4, 2026): abstract level, transducer
  description of maximal closed subgroups of F. I found no 2-transitivity
  statement. Authorship (Golan) is as I recorded it earlier this session and
  was not re-checked while writing these notes.
- arXiv:2606.00863 (dated May 30, 2026): abstract level. I found no statement
  on 2-transitive actions of F. Authorship was not re-checked while writing
  these notes.
- arXiv:2209.03244 (Golan) and arXiv:1501.00724, arXiv:1508.00493
  (Golan–Sapir): seen only through their existing repo nodes (closedness,
  Jones' subgroup `\vec F`). Not re-fetched.
- arXiv:2503.21882: checked, and not relevant to this problem.
- Groups Geom. Dyn. 19 (2025), 617–636: text not extractable. Content
  unverified; it is not used in any node.

The 2024–2026 sources above are what my literature search turned up. None of
them reports a resolution of Problem 2.20.

## Referee (2026-09-16)

Checked:

- Read all four research files and these notes in full, plus the landed nodes
  they rest on: the grid claim and its route (which quotes Le Boudec–Matte Bon
  Prop. 5.1 case (2) for every `x ∈ R`, so the grid facts hold at irrational
  and non-dyadic rational `x` too), the faithfulness claim,
  `thompson-f-two-transitive-stabilizers-minimal-not-confined` and
  `jones-subgroup-cosets-form-a-parity-lamplighter`. `git status` shows no
  unlisted solver files.
- Hull-endpoint route, line by line. Nonempty and proper `I^±`; disjointness
  `I^- ∩ I^+ = ∅` via (G2); swaps fix `η, ξ` by equivariance and symmetry.
  Step 3 is correct: cutting `s` on `[y,x]` gives `s_- ∈ F_y^- ≤ F_x^-` and
  `s_+ ∈ F_x^+`, and injectivity of the grid map at `x` applied to
  `(aω, ω)` and `(s_-ω, s_+ω)` forces `s_-ω = ω'`, so `y ∈ I^-`. The `ξ` case
  is the mirror, using the grid at `y`. Rationality (a swap is affine near a
  non-dyadic fixed point, with `b` dyadic, and slope 1 would make it the
  identity), the single orbits and the germ statement are all correct. So is
  the formula `I^-(ω,gω) = g(Z)`.
- Branching route, line by line. `Br ≅ Z/dZ` through
  `Stab_{F_p^-}([ω]) = M_p(H ∩ F_p^-)`. `H_p` fixes every branch, since left
  slopes at a common fixed point are conjugation invariant. `H_p` is
  transitive on `T_p` by 2-transitivity plus equivariance of `η`. Two
  non-`[ω]` branches would both lie in `T_p`, a contradiction, and this also
  excludes `d = 0`. The dichotomy, the parity rule (using the grid splitting at
  dyadic `p`) and the remark on odd-slope swaps are correct.
- Literature: web searches on 2026-09-16 turned up no resolution of Problem 2.20
  and no published version of these lemmas. The solver's other literature notes
  were not re-fetched.
- `bin/cairn search --similar`: no duplicate claim. The hull `[ξ,η]` and
  "swaps fix both endpoints" were already sketched in the Attempts of
  `thompson-f-has-no-faithful-2-transitive-action`, and this is now said in the
  claim's scope line.

Changed:

- Hull claim: added `ξ ≤ η` to item 1, which the route already proves.
  Replaced "Unreviewed" with a scope line (refereed, no novelty claimed,
  overlap with the existing Attempts named).
- Branching claim: the unsupported sentence "`\vec F` is not maximal" now has
  a proof from the landed lamplighter claim: `g ↦ |J(g)| mod 2` is a
  homomorphism with `\vec F < ker < F`. Added a scope line.

Verdict: both routes are sound and depend only on established claims. Landed
with small fixes. Problem 2.20 remains open. Neither stabilizer kind (I or II)
is excluded, and the non-dyadic `Θ^-` case is untouched.
