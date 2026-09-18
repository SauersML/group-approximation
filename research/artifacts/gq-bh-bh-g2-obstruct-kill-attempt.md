# G2(e): an honest attempt to kill quantum rigidity for every free minimal SFT (lane bh-g2-obstruct, 2026-09-18)

This artifact records gate G2(e) of `research/artifacts/gq-bh-synthesis-master-route.md`:
- **Task.** Find an invariant that forces a noncommuting D-quantum family, for every free minimal
  SFT over some one-ended `Λ`, at all large `D`. Such an invariant would kill Strategy 1.
- **Status.** Everything here is lane work and unreviewed. The two landed claims carry their own
  status lines. No priority is claimed.

## 0. Verdict

- **No kill.** Every invariant available today is *first order*. Each one only produces
  wall-type certificates, which are commuting data on each side of a thick wall.
- **Over `Z^2`, first-order invariants provably cannot kill Strategy 1.** Labbé's shift is free,
  minimal and wall-rigid (`labbe-shift-is-wall-rigid`, itself unreviewed).
- **A kill over any amenable `Λ` is at least as hard as known open problems** (§2): Matui's question
  and the Labbé route to finitely presented simple amenable groups.
- **What the attempt did produce:** two general structure theorems that locate where rigidity can
  live (§3). They are the useful output of this gate.

## 1. Invariants tried, and what each gives

| Invariant | Result | Kills |
|---|---|---|
| Positive entropy (amenable `Λ`) | an ambiguous annulus recurring far away, i.e. a wall certificate | yes, at every scale; `positive-entropy-sft-crossed-products-are-not-fp`, and its proof generalizes to amenable `Λ` via the infimum rule and the ergodic theorem |
| One finitely supported modification (any `Λ`, `X` minimal) | two far copies of the modification in one configuration, i.e. a wall certificate | yes; **new** `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`. No entropy or amenability needed |
| Slabs of a multi-ended factor (`Λ_0 × H`) | independent faults in two branches give a wall certificate | forces a single free branch per slab; **new** `quantum-rigid-sfts-over-products-have-a-single-free-branch` |
| Invariant measure, Følner rank models (amenable `Λ`) | commuting families only; see §4 | nothing |
| Periodic quantum tilings (`Z^2`) | refute rigidity if they exist (`periodic-quantum-tilings-refute-quantum-rigidity`) | none constructed; for wall-rigid shifts they must be contextual, of dimension `>= 3` |
| Exact matriciality (`Z^2`) | gives periodic quantum tilings (`matricial-aperiodic-sft-rings-are-not-quantum-rigid`) | open for every free minimal `Z^2`-SFT |

The first three rows are all instances of the far-modification Lemma, i.e. of wall rigidity. By
`sft-wall-rigidity-iff-idempotent-commutator-ideal` (for `Z^2`), walls are exactly the first-order
obstructions. Beyond them only an idempotent commutator ideal `J_D = J_D^2 != 0` can refute
rigidity: genuinely contextual families, with no two-dimensional or finitely filtered piece.

## 2. Why a kill over amenable groups is hard

Suppose G2(e) held over `Z^2`: every free minimal `Z^2`-SFT is non-rigid at all large `D` over some
field of characteristic not 3 or 5. Then:
1. **No finitely presented derived full group.** For every free minimal `Z^2`-SFT `X`, `D([[X]])` is
   not finitely presented (contrapositive of `zd-derived-full-group-fp-forces-quantum-rigidity`).
2. **Matui's question, for expansive actions.** Finite presentation of the full group of a free
   subshift forces finite type (`fp-alternating-full-groups-of-free-subshifts-force-sft`;
   `zd-derived-full-group-fp-forces-finite-type` for `Z^d`). So item 1 extends to every free minimal
   `Z^2`-*subshift*. That answers Matui's question (arXiv:1602.00383, recorded as
   `free-minimal-zn-derived-full-groups-are-never-fp`) negatively for all expansive free minimal
   `Z^2`-actions.
   - Today that question is settled only for residually finite actions
     (`rf-free-minimal-zn-actions-have-non-fp-derived-full-groups`), and it is open exactly for the
     Robinson and Labbé type.
3. **Labbé.** `labbe-shift-derived-full-group-is-finitely-presented` would be refuted. So would the
   Labbé route to a finitely presented infinite simple sofic group.
4. **Any finitely generated `Λ`.** G2(e) over `Λ` is exactly the failure of P2 for every free minimal
   subshift over `Λ`, by `fp-v-times-subshift-full-groups-force-quantum-rigidity`, parts 1 and 2.

So a kill over amenable groups needs a tool strong enough to answer Matui's question. None is in
the graph, and every recorded non-finite-presentation mechanism for Cantor full groups (LEF, finite
models, entropy) is first order or needs periodic approximations.

## 3. Where rigidity can live

1. **Over any `Λ`.** Minimal rigid SFTs are *finitely rigid*: no configuration changes on a finite
   set. Every modification is infinite. More generally, all modifications of one configuration lie
   within `2D` of each other. This is the far-modification Lemma, equivalent to wall rigidity.
2. **Over amenable `Λ`.** The candidates are zero entropy and wall-rigid. The only open channel for
   refutation is contextual families. The heuristic "an invariant measure blocks compression"
   (master route, LRP corollary 3) is not a theorem, and §4 explains why measures alone produce
   nothing.
3. **Over `Λ_0 × H` with `H` multi-ended** (`Λ_0 × Z`, `Λ_0 × F_2`, `F_2 × F_2`). Every thick
   slab determines the configuration except on one branch.
   - In the tight case `X` is the spacetime of `H` acting by automorphisms of a strongly aperiodic
     fibre shift over `Λ_0`.
   - Extra rigidity from `H` can only come from commutation propagating along those automorphisms.
     This is the permutive mechanism of Ledrappier and of the permutive triangles, transported to
     non-amenable `H`.
   - This is a concrete design recipe for G2(c)/(d): an `F_2`-action by expansive local
     automorphisms on a strongly aperiodic `Λ_0`-subshift, with spacetime of finite type.
4. **What escapes both theorems:** coupled hierarchies whose free branch changes from slab to slab,
   with modifications that are infinite, coarsely connected, and not confined to any single branch.
   Examples are fault networks crossing every slab, as in Labbé's shift. A rigidity proof has to
   control these (Conjecture G2-fp of SYNTHESIS.md is one such attempt). A refutation has to be
   contextual on them.

## 4. The rank-ultraproduct idea, and why it collapses to walls

**The idea.** A kill needs noncommuting families satisfying (Q1)–(Q3) *exactly*. Take
finite-dimensional families `E^(n)` that satisfy each fixed instance of (Q1)–(Q3) up to normalized
rank `o(1)`, and whose commutators at fixed sites have normalized rank bounded below. Their
rank-metric ultraproduct acts on `W = ∏ M_(d_n)(k) / (rank null)`, viewed as a `k`-space, by left
multiplication. It is then an exact noncommuting D-quantum family.
- This is sound, and it gives one clean principle: **rigidity implies rank-stability of
  commutation.** Almost-legal finite families almost commute, uniformly on fixed sites.

**Why it produces nothing new.** Families built from classical tilings by changing basis across
approximate walls face a trade-off.
- The commutation defect at fixed nearby sites `q, q'` survives only if a wall separates them with
  probability bounded below. That forces walls at bounded mutual spacing `R`.
- The (Q2)/(Q3) defects are supported where the two tilings disagree on the wall. They vanish in
  rank only if those defects have density `o(1)`.
- Both are possible only if cells of bounded size carry two defect-free fillings. That is a finitely
  supported modification, i.e. exactly row 2 of §1, and so entropy over amenable `Λ`.

So measure- and Følner-based constructions of classical origin cannot beat first order. A kill has
to manufacture contextuality: frame changes around cycles of contexts, which classical tilings never
provide.

## 5. Lessons for general BH (also appended to board/LESSONS.md)

1. **An obstruction to Strategy 1 needs genuinely quantum contextuality.** Every classical or
   measure-theoretic invariant (entropy, amenability, Følner, finite modifications, slabs) is first
   order. Over `Z^2`, first order cannot kill Strategy 1 because of Labbé. And any kill over an
   amenable group would already answer Matui's question.
2. **Non-amenability via a free product factor does not create rigidity.** Over `Λ_0 × F_2`, a rigid
   free SFT is a near-deterministic spacetime of `F_2` acting on a strongly aperiodic `Λ_0`-shift.
   The design target is commutation propagating along expansive automorphisms, not compression
   alone.
3. **Finite rigidity is necessary everywhere.** No finite decoration of the crux object may be
   flippable, over any group.

Nodes landed by this lane:
- `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`
- `quantum-rigid-sfts-over-products-have-a-single-free-branch`
