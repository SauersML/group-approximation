---
rg: 2
id: coupled-rope-reader-has-nested-one-bit-fibres
kind: claim
title: A coupled rope reader on the modular-machine scaling seed (a transported region bit plus block links) links every free descent chain of every configuration into one bit, so each fibre is a nested chain of at most three points and the reader is pointwise rigid; its quantum rigidity is now exactly base-centrality (C_D)
distinct_from:
  rope-readers-cannot-be-deterministic-and-must-couple-chains: that shows uncoupled readers fail and proposes rules (L) and (R); this replaces (R) by a transported region bit, proves the linking, and proves pointwise fibre rigidity.
  modular-machine-scaling-seed-reads-regular-numerals: that is the uncoupled reader; this is the coupled one, with the same forced rope marks.
  downhill-centrality-needs-no-data-rigidity: that proves centrality when a one-predecessor rule descends toward every site; the reader's descent does not, so (C_D) is left open here.
---
**ESTABLISHED** for parts 1–4 (lane proof, bh-invent-15, 2026-09-18; not reviewed). Part 5 is
settled in `free-bit-components-are-central-iff-they-see-the-base` (09-19).
- **Scope (09-19).** Parts 2–5 treat the positional layer M (the digits) as base. It is not base
  data of the rigid seed, and over the true base the reader for Cohen's set is **not** quantum
  rigid: `cohen-rope-reader-is-not-quantum-rigid`. The results here hold relative to a frozen M.
- **Proof repair (09-19).** The first version of the linking step (part 2) had a gap: it passed
  the free choice through the common `l`-image of two neighbouring positions, which is forced to
  `bad` when a bad digit lies below the link. The theorem stands. The proof below routes the
  link through all-good positions ("detours"). The retracted node
  `absorbing-rope-readers-are-not-pointwise-rigid` took the gap for a counterexample.
- **Base hypothesis.** Part 2 uses the standard property of seeds built from locally finite
  splittings: in every configuration the pointer field has a unique sink, a coset or an end of
  the Bass–Serre tree. See `locally-finite-splittings-preserve-rigid-sft-compactifications`.
- **Notation.** As in the parents: `S_M` and its seed, the origin layer M, rows `β = 0`,
  `l`-descent, and Cohen's rope set `I`. `I` consists of the numerals with all base-`m` digits in
  `{1,…,2n}`, with `m − 1 > 2n`, and its automaton has states `ok` and absorbing `bad`.

## 1. The coupled reader
- **(Rg) Region bit.** Every coset carries `ρ ∈ {0,1}`:
  - `ρ = 1` on the sink coset;
  - if a coset's pointer toward the sink is an `l^{-1}`-edge with label `(a, 0)`, then its `ρ`
    equals its parent's `ρ`;
  - otherwise `ρ = 0`.

  Each case reads one bounded window.
- **(Q) Reader.** On row elements (`y`-marker `*`, `x`-marker in `{*, −}`) of cosets with
  `ρ = 1`:
  - `q = q_0` at origins;
  - otherwise `q(h) = δ(q(hl), α(h) mod m)`.

  Elsewhere `q = ⊥`.
- **(L) Block links.** For row elements `h` and `h' = h x^{a'−a}` of one `m`-block
  (residues `a, a'` of the same `⌊α/m⌋`) in a `ρ = 1` coset, impose `q(hl) = q(h'l)`.
- **The forced point.** In `y_*`:
  - `ρ = 1` exactly on the sink and its descendants along `l`-edges labelled `(a, 0)`;
  - `q(h) = 𝒜(numeral of α(h))`, so the rope marks `v(x^α) = [α ∈ I]` are forced at linear
    radius, exactly as in the parent;
  - (L) holds, because `hl` and `h'l` sit at the same position `⌊α/m⌋` in sibling cosets.

## Theorem
2. **Linking.** In every configuration, the free choices of the reader and region layers over the
   base amount to at most one region bit and one reader bit. The reader bit exists only when the
   region bit is 1.
3. **Nested fibres.** So every fibre over a base configuration is either:
   - one point;
   - `{ρ ≡ 0 on the spine} ∪ {ρ = 1, q forced}`; or
   - `{ρ ≡ 0} ∪ {ρ = 1, bit ok} ∪ {ρ = 1, bit bad}`.
4. **Pointwise rigidity.** Every `y`-relative family of this extension commutes.
5. **(C_D).** By `extension-rigidity-is-base-centrality-plus-pointwise-rigidity` (item 3),
   the coupled reader over the rigid base seed is quantum rigid iff (C_D) holds: every base
   marginal commutes with every reader marginal, near or far. This was OPEN here. It is proved in
   `free-bit-components-are-central-iff-they-see-the-base`.

## Proof
**2. The region.**
- *Sink at a coset.* `ρ` is anchored there. The `ρ = 1` region is the closure of the sink under
  `l`-edges labelled `(a, 0)`.
- *Sink at an end.* The spine is the pointer path `S_k` toward the end. Then
  `ρ(S_k) = ρ(S_{k+1}) ∧ [step k is an l^{-1}(a,0)-edge]`.
  - If infinitely many steps are of another type, `ρ ≡ 0` is forced.
  - Otherwise, from some `K` on, `ρ(S_k)` for `k ≥ K` is one free bit. When that bit is 1, the
    region is the `l(a,0)`-descendant closure of `{S_k : k ≥ K}`. Other cosets are forced to
    `ρ = 0`.
- *Either way,* the region is a single subtree `R` in which every coset except the top has its
  parent in `R`, joined by an `l(a,0)`-edge.

**2. Rows nest.** For a coset `C' = C x^a l` in `R`, the element at row position `j` of `C'`
has `l^{-1}`-neighbour `c x^{a+mj}`, which is in the row of `C` because the label is `(a, 0)`.
- So each child row is the residue class `a + mZ` of its parent row, and every descent chain in
`R` passes through the rows of all its ancestors in `R`.

**2. Free chains share tails.** A chain has a free run only if its digit stream has an all-good
tail (parent, part 4).
- Adding a bounded integer to such a position changes only finitely many low digits. A carry
  passes only through digits `m − 1`, which are bad, so it stops before the tail.
- So all positions between two free-tailed positions of one row are free-tailed, with the same
  tail.

**2. Which sites carry the choice.** For Cohen's automaton the value at a row site is
`ok` iff the tail run is `ok` and every digit of its position is good. So a site is **free**
(its value depends on the tail choice) iff its position is **all-good**. Every other site is
forced to `bad` by a finite deduction: the first bad digit above it. Chains with infinitely many
bad digits are forced entirely.

**2. Two kinds of links between free sites.** Write a site of the subtree below a coset `C ∈ R`
as `(w, q)`: position `q` in the descendant `C_w`, `w` a word of labels.
- *Sideways:* `(ua, q) ~ (ub, q)` for all labels `a, b`, by (L) in `C_u`. Both sites are free
  exactly when `q` is all-good, whatever `a, b` are.
- *Up:* `(ua, q) ~ (u, a + mq)` when `a` is good, by the reader rule. `ok ↦ ok` and `bad ↦ bad`
  under a good digit.

**2. Detours.** Every free site `(w, q)`, `w = w_1…w_k`, is linked to a free site of `C`'s row.
Go sideways to `(w_1…w_{k−1}g, q)` with `g` good, then up to `(w_1…w_{k−1}, g + mq)`, and
repeat. This ends at `(∅, g + mg + ⋯ + m^{k−1}g + m^k q)`, and every intermediate site is free.
The bad labels of `w` never matter, because sideways moves ignore labels.

**2. Global linking.**
- *Within one row.* Two free sites `p, p'` of `C`'s row share their tail. So for `k` large both
  descend by up-links to the same position `q* = ⌊p/m^k⌋ = ⌊p'/m^k⌋`, in cosets `C_w` and `C_{w'}`.
  The same detour (the same good `g`) lifts both to one site of `C`'s row.
- *Between cosets.* A coset `C = C'_a` of `R` is linked to its parent: `(∅_C, p) = (a, p)` in
  `C'`, then sideways to `(g, p)` and up.
- *Conclusion.* So all free sites of `R` form one linked class, and they carry one bit. The top of
  `R` is the sink coset or the spine; in the spine case, every spine coset is linked to the next.

**3.** This is the case count of part 2.

**4.** Let `G` be a `y`-relative family.
- **The spine.** The region rule gives `G_1(S_k)(1 − G_1(S_{k+1})) = 0` and the reverse along
  the free spine, so `G_1(S_k) = G_1(S_{k+1}) =: P`.
- **The reader.** At free-chain sites the letters are `⊥, ok, bad`. The chain rule and (L) forbid
  `ok` next to `bad` or `⊥` at linked sites, so `G_ok(u) = G_ok(u)G_ok(u')`, and symmetrically.
  Hence `G_ok` is one idempotent `E` on the whole linked family.
- **Nesting.** The pattern "`ok` in a `ρ = 0` coset" is forbidden, so `E(1 − P) = (1 − P)E = 0`,
  that is, `E = EP = PE`.
- All other letters are scalars. So the family generates the commutative algebra spanned by
  `1, P, E`.

**5.** Parts 3–4 give pointwise rigidity. The base seed is rigid, so the base marginals commute
pairwise (F1).
- **Why the downhill lemma does not settle (C_D).** Its hypothesis (F4) needs a potential that
  decreases along predecessor steps toward every site. The predecessor step here is `h ↦ hl`,
  which runs to origins or to infinity, never toward an arbitrary site.
- **A possible route.** Use the linked structure instead. By part 2, every reader marginal on a
  free chain is determined through (L) and the rules by a single `E` and by base patterns. So
  (C_D) reduces to commuting `E` with base marginals far away. That is a one-idempotent
  centrality statement.

## For the SEED TOWER team
- **The coupled reader is the right object.** One region bit and one reader bit, nested, and it
  is pointwise rigid.
- **What rope seeding over `K_M` waits on.** It now waits only on (C_D) for one idempotent `E`
  against the base marginals. That is a sharper target than (RR) or (RR′).

## Lesson for general BH
- **Tree-shaped links collapse the freedom.** Link the free choices at infinity along the
  seed's own tree structure: a transported region bit, plus links inside residue blocks. Then
  all freedom collapses into a nested chain of at most two bits, and pointwise rigidity is
  automatic.
- **What is left.** Rigidity of seed readers comes down to one centrality statement: a single
  idempotent against the base.
- **Where the tail invariant comes from.** Free chains link because bounded moves never change
  the digit tail. The relevant invariant is the tail of the `m`-adic position.
