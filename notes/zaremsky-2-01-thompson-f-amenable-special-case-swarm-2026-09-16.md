# Zaremsky Problem 2.1 (amenability of F): special-case / strengthening lane, 2026-09-16

Agent: hi-spec-zaremsky-2-01-thompson-f-amena. Target root: `zaremsky-2-01-thompson-f-amenable`.
Angle: SPECIAL CASE / STRENGTHENING. Nothing here is committed.

## 1. External gate (checked 2026-09-16)

Abstract pages fetched on 2026-09-16, with dates as shown on arXiv:
- V. Guba, "Amenability problem for Thompson's group F: state of the art",
  arXiv:2305.07113. v1 11 May 2023, v2 14 Oct 2023, v3 18 Oct 2023, v4 19 Oct 2023. It is
  a survey, and the question is still open there.
- V. Guba, "Systems of equations over the group ring of Thompson's group F",
  arXiv:2201.02308, v1 7 Jan 2022. It proves that `(1 - x_0) u = b v` has nonzero solutions,
  and that the chain systems `(1 - x_0) u_0 = ... = (1 - x_m) u_m` do too. It says nothing
  about multi-bump binomials.
- L. Bartholdi and D. Kielak, "Amenability of groups is characterized by Myhill's Theorem",
  arXiv:1605.09133, v1 30 May 2016, v2 7 Jun 2016. The appendix by Kielak shows that for a
  group with `K[G]` a domain, `K[G]` is Ore iff `G` is amenable. That is the bridge the graph
  uses (`thompson-f-amenable-iff-group-ring-is-ore`).
- D. Staley, "Thompson's Group F and Uniformly Finite Homology", arXiv:0806.2877, v1 17 Jun
  2008, v2 11 Mar 2009. This is context only. An earlier web search today gave wrong dates
  for it; the dates above come from the abstract page.

Web searches earlier on 2026-09-16 (in this lane, before a context compaction) found no
2023–2026 source that resolves amenability of `F`, or the Ore condition for twisted
multi-bump binomials in `K[F]`. A further search on 2026-09-16 was refused because the
session's web-search budget was used up. So the novelty of §3 is checked only against the
graph and those earlier searches. No citation in this note beyond the four abstract pages
above was re-fetched, and none is relied on.

## 2. State of the art in the graph

Ore-side partial results for `K[F]` that bear on `thompson-f-is-not-amenable`, through
`thompson-f-amenable-iff-group-ring-is-ore`:
- `thompson-f-binomial-pairs-have-common-multiples` (ESTABLISHED): `(1 - a, 1 - c)` always,
  and `1 - h` against every `b` with `|supp b| <= 2`.
- `thompson-f-twisted-x0-binomial-is-ore-with-every-element` (route `requires: []`):
  `1 + lambda x_0` against every element, by Guba's count with weights.
- `thompson-f-rescaled-x0-binomials-have-common-multiples` and
  `thompson-f-one-bump-binomials-have-common-multiples`: every one-bump `g` has property O,
  so `1 + lambda g` meets every principal right ideal.
- Multi-bump `g`, against restricted `b` only:
  - `thompson-f-multibump-binomials-meet-stabilizer-ideals` (ESTABLISHED): `b` in
    `K[H_i × Z_i] s`, all bump endpoints dyadic.
  - `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals` (unreviewed): `b` in
    `K[W_g] s`, the pointwise stabilizer of the bump endpoints.
- In flight (another agent, not landed, not checked here):
  `thompson-f-twisted-binomial-pairs-have-common-multiples`, covering `|supp b| <= 2` for
  every `lambda`.
- `thompson-f-every-twisted-binomial-is-ore-with-every-element`: OPEN. It was locked by
  another agent while this lane ran (lock exit 3), so this lane did not touch it.

## 3. What was proven

New nodes (uncommitted):
- claim `thompson-f-binomials-meet-ideals-with-separated-conjugates`;
- route `thompson-f-binomials-meet-ideals-with-separated-conjugates-proof`, with
  `requires: [thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals]`.

**Theorem (modulo the unreviewed bump-endpoint claim).** Let `g ≠ 1` in `F` have bumps
`I_i = (p_i, q_i)`, `i = 1..k`, let `lambda` be in `K^x`, and let `b ≠ 0`. Suppose that for
every `i < k`, `max_(t in supp b) t^-1(q_i) <= min_(t in supp b) t^-1(p_(i+1))`, and that
`q_i` is dyadic when `q_i = p_(i+1)`. Then `(1 + lambda g) R ∩ b R ≠ 0`. The same holds for
binomials `alpha u + beta w` with `g = w u^-1`.

More generally, for dyadic `Z`, every finite family of `Z`-one-bump elements has a nonzero
common right multiple of its twisted binomials.

**What is new.**
- *Strict extension.* It contains both earlier multi-bump results, `K[W_g] s` and
  `K[H_i × Z_i] s`, as special cases of one separation condition. `supp b` may move every
  bump endpoint at once, as long as the conjugated bumps of each index stay between
  common dyadic separating points.
  - Example: `g` with bumps `(1/8, 1/2)`, `(1/2, 7/8)`, and `b = 1 + t + t^2` with `t` in
    `Stab_F(1/2)` moving `1/8` and `7/8`. No earlier node covers this pair.
  - For two bumps sharing a dyadic endpoint `m`, every `b` in `K[Stab_F(m)] F` is covered.
- *Sharp reduction.* A non-Ore pair with a twisted binomial side needs one of two things:
  - two conjugates `t^-1 g t` and `t'^-1 g t'`, with `t, t'` in `supp b`, such that bump
    `i` of the first ends to the right of the start of bump `i + 1` of the second
    (crossing conjugated bumps); or
  - `g` with a non-dyadic shared endpoint.
- *New nesting mechanism.* Families whose shapes (all `2k` bump endpoints) differ are
  handled by an induction that releases the endpoint coordinates one at a time.
  - Order the members by the coordinate being released.
  - The running multiple lies in the hull `∏ F_[min a_l, max d_l]`, so conjugation by its
    support freezes the released coordinate and all later ones.
  - The conjugates then fall under the previous stage, and the hull of the conjugates stays
    inside the next hull.
  - With `k = 1` this is Lemma D plus Item 1 of the rescaled route. The multi-coordinate
    version, and the use of the bump-endpoint claim as the base case, are new.

**Weakest steps.**
- The requires claim `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals` is
  unreviewed. It is only used through its item 1, for Z-one-bump `c` against `K[L]`, with
  `L = ∏ F_[a_l, d_l]`.
- Step (ii) of the induction: the coordinate being released is frozen by the running
  multiple only because of the ordering. For `d_i`, `D_i^j <= d_i(c^(j+1))`, and the
  support of `w_j` fixes `[D_i^j, z_i]` pointwise.
- Step (iv): the hull of the conjugates lies in `H_(j+1)`.

## 4. Approaches tried and where each dies

1. **A two-sided zoom monoid for multi-bump `g`.**
   - *Idea.* Guba's count for `x_0` rests on the shift `x_0^-1 x_j x_0 = x_(j+1)` on the
     positive monoid. Zoom at an interior endpoint `m` of `g` with an element of slope `2`
     at `m`, and count in a monoid of elements with a germ at `m`.
   - *Where it dies.* Elements of `supp b` that move `m` have no germ at `m` compatible with
     the zoom. So there is no analogue of the index shift, and the letter-window count has
     nothing to act on. It works only when `supp b` fixes `m`, which is already inside the
     separated case.
2. **Pushing bumps apart by translation or conjugation.**
   - *Idea.* Replace `(g, b)` by `(s g s^-1, s b s')` so that the conjugated bumps separate.
   - *Where it dies.* Separation is invariant under `T -> T s'` and under
     `(g, T) -> (s g s^-1, s T)`, since `(s t)^-1 (s I_i) = t^-1 I_i`. This was checked in
     this lane, and the proof route records the first. So crossing cannot be removed this
     way.
   - Nesting the bumps one at a time (Lemma D style) also stalls. The running multiple
     moves the interior endpoints of the next bump, and the Remark in
     `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof` shows that no nonzero
     element of `(1 + lambda c) R` lies in `K[Stab_F(z)] s` when `c` moves `z`.
3. **Treating the other bumps as a variable.**
   - *Idea.* The `H_i × Z_i` proof works over a rational function field in the other bumps.
     Try the `x`-degree filtration of `K[x^±] ⊗ R` for `b` that moves the endpoints of those
     bumps.
   - *Where it dies.* The conjugates `t^-1 g_j t` of the other bumps are no longer central
     in the relevant subring. The filtration does not stabilize, and no stage has a finite
     dimension count.
4. **Counting in the subgroup generated by the conjugates.**
   - *Idea.* If `S = <t^-1 g t : t in supp b>` is amenable, then `K[S]` is Ore, and
     Lemma B finishes.
   - *Where it dies.* For crossing families there is no reason for `S` to be amenable.
     Subgroups of `F` generated by elements with overlapping supports can contain copies of
     `F`; I recall this from Brin's ubiquity theorem and from chain groups, but did not
     re-fetch either source, so it is unverified here. So this route presupposes the root
     question.
5. **Lock conflict.** `thompson-f-every-twisted-binomial-is-ore-with-every-element` was held
   by another agent (`bin/cairn lock` exit 3, about 115 minutes remaining). This lane
   therefore added a separate claim and did not edit that node.

## 5. Next steps

1. **Smallest crossing case.** Take `g` with bumps `(0, 1/4)`, `(3/4, 1)`, and `b` with
   `supp b = {1, t, t'}` where `t^-1(1/4) > 3/4`.
   - Two-term `b` is item 3 of `thompson-f-binomial-pairs-have-common-multiples` for
     `lambda = -1`. For general `lambda` it would be item 2 of
     `thompson-f-twisted-binomial-pairs-have-common-multiples`, an uncommitted node another
     agent was validating while this lane ran; I did not check it.
   - So three terms is where the crossing case starts. A census of small common multiples
     (modest computation, as in `experiments/thompson-f/ore_census.py`) would test it.
2. **Replace `b` by a separated multiple.** Trivially, `(1 + lambda g) R ∩ b R ≠ 0` whenever
   `b R` contains a nonzero element whose support is `g`-separated. Two questions follow:
   - Does every nonzero `b R` contain such an element? A negative answer for one `(g, b)`
     would be a precise obstruction to this method, though not a non-Ore witness.
   - Bi-orderability of `F` shows that the extreme elements `s_min` and `t s_max` of
     `supp((1 + t) y)` survive cancellation. Crossing, however, is a property of pairs
     `(s, t s)`, and those can cancel.
3. **Non-dyadic shared endpoint.** An example is `g = 4x - 1` near `1/3`. The factorization
   into bumps leaves `F`, and (E) does not apply there because `g` moves points on both sides.
   - Transport to the group of PL maps with breakpoints in `Z[1/6]` is a candidate, since it
     contains the two bumps. Its group ring is not covered by any node.
4. **Review.** Before this claim is built on, the requires
   `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals` (unreviewed) needs review.
   The new route uses it only through its item 1, for `b` in `K[∏ F_[a_l, d_l]]`.
