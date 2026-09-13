# F-sets for following permutation models of Thompson's F (2026-09-13)

Lane `solve-f-sofic-nonspatial`.

**Question.** `thompson-f-spatial-permutation-models-almost-commute` covers `F`-sets over the interval.
On which other `F`-sets could permutation pairs that follow a genuine action of `F` separate the
commutator `c = x_0 x_1 x_0^-1 x_1^-1` while the error goes to 0? Such a family would witness
`thompson-f-is-sofic`.

**Verdict.** No witness. Two elementary theorems, and a classification of the natural `F`-sets.

## 1. The reduction

`thompson-f-following-models-separate-iff-mean-charges-commutator`:
- **Equivalence.** Following models on `Ω` with error `→ 0` and separation `≥ ε` exist exactly when some
  invariant mean `m` on `ℓ∞(Ω)` has `t = m(Moved(c)) > 0`.
- **Means from models.** Counting measures of the models are almost invariant; take a cluster point.
- **Models from means.** Day's convexity step and Namioka's level sets give a finite set; truncate the
  action to it.
- **Uniform mass.** For every invariant mean, `g ↦ m(Fix(g))` is a character. By the character simplex,
  every nontrivial element of `F'` moves mean-mass exactly `t`.
- **Null slabs.** For every equivariant `p : Ω → [0,1]`, `m(p^-1[y,z]) = 0` for `0 < y ≤ z < 1`. The
  proof: `κ(y) = m(p < y)` is monotone and constant on orbits.

So `t > 0` is killed by any nontrivial element of `F'` whose moved set sits over slabs. The spatial
bound is the case `g = c`, with an explicit rate.

## 2. Transitive F-sets `F/H`

| `H` | invariant mean on `F/H` | `t` | reason |
|---|---|---|---|
| contains `F'` (every `H` with nontrivial normal core, e.g. finite index) | yes, `F/H` is abelian | 0 | `c` acts trivially |
| stabilizers of points, including irrational points; finite configurations; germs at points; dyadic cones and intervals | yes (`thompson-f-end-rigid-schreier-graphs-are-amenable` for points and configurations) | 0 | spatial bound; confined moved sets |
| pointwise stabilizers `F_Z`, `Z` a finite union of dyadic intervals with interior: `F_[0,a]`, `F_[a,1]`, elements supported in `[a,b]` | yes for `F_[0,a]`, `F_[a,1]` (end-rigid node); not decided for the others | `t > 0` forces `F` amenable | `thompson-f-interval-stabilizer-cosets-separate-only-if-amenable`, item 2 |
| amenable `H`: `e`, `⟨x_0⟩`, copies of `Z wr Z`, every EA subgroup | only if `F` is amenable | 1 for `H = e` | same claim, item 3 |
| `F'` | yes | 0 | first row |
| every other non-amenable co-amenable `H` | open | open | the gap, §4 |

The first row uses the import that every nontrivial normal subgroup of `F` contains `F'`. It is pinned
in `thompson-f-is-lea-only-if-amenable-proof` (Burillo–Lodha–Reeves, citing Cannon–Floyd–Parry). The
claims themselves avoid it: corollary 1 of the reduction claim uses commutators with small supports
instead.

The directive's candidates:
- **`H = e`:** `t = 1` exactly when an invariant mean exists, i.e. when `F` is amenable.
- **`H = F'`:** `t = 0`.
- **`H = ⟨x_0⟩`:** amenable, so an invariant mean on `F/H` exists only if `F` is amenable.
- **Stabilizers of irrational points (Savchuk):** point stabilizers, so `t = 0`.
- **Parabolic subgroups:** stabilizers of points in `(0,1)`, so `t = 0`.

**Mechanism of the transfer.** Take `Z` with interior and an invariant mean charging `Moved(c)`.
- **Where the mass sits.** Null slabs put the mean-mass of `Moved(c)` on restrictions `f|_Z` that
  stretch one component interval `I` of `Z` over almost all of `(0,1)`. Everything else of `Z` is
  squeezed toward 0 and 1.
- **Why the section exists.** Near the ends every generator is a scaling by a power of 2. So the
  squeezed gaps have canonical scale-equivariant fillings, and `f|_Z ↦ f` is an almost equivariant
  injection into `F`.
- **Conclusion.** The mean pushes forward to almost invariant measures on `F`.

## 3. Step 2 (exact profiles): screened out, no computation run

- **No concrete candidate.** Every candidate named in the directive lands in a decided row of §2. The
  undecided row has no explicit member.
- **Collapsing rows.** On the rows where `t > 0` forces amenability, a computed family with error `→ 0`
  and separation bounded below would prove `F` amenable through the transfer lemma. In the limit its
  sets would give Følner sets of `F`.
- **Moore's bound.** `thompson-f-folner-function-exceeds-every-tower` (Moore, Theorem 1.1) says
  `C^-n`-Følner sets have at least `exp_n(0)` elements. So finite truncations cannot reach that regime.
  This is a screening remark, not a theorem: the slab nullity used by the transfer is asymptotic, and
  no quantitative link from error to Følner parameter is proved here.
- **Truncations.** Ball truncations of these Schreier graphs keep the error bounded below, like the
  truncations in `thompson-f-spatial-permutation-models-2026-09-13.md` §3.1.
- **MSI use.** No compute jobs; MSI was used only for the Cairn check.

## 4. Exact gap

1. **An exotic F-set.** A following-model witness needs an `F`-set `Ω` with an invariant mean and
   `t > 0`. By §1–2 the `F`-set must satisfy all of these:
   - the action is faithful;
   - every nontrivial element of `F'` moves mean-mass `t`;
   - no equivariant map to `[0,1]` confines the moved set of any nontrivial element of `F'` to slabs;
   - if `Ω` is transitive, its point stabilizer is non-amenable and co-amenable, and is not a
     pointwise stabilizer of a finite union of intervals.

   Not covered:
   - `H = F_Z · L` with `L` a nontrivial subgroup supported inside `Z`, where the transfer lands in
     `F/L`-like sets instead of `F`;
   - pointwise stabilizers of infinite closed sets, such as Cantor sets in `(0,1)`;
   - subgroups containing no rigid subgroup `F_J` at all.
2. **Infinitely many orbit types.** The claims are stated for one `Z`. A mean on a disjoint union of
   orbits can give 0 mass to each type and positive mass in total.
3. **Models following no F-set.** This case is untouched. A witness still needs a regular component in
   its fixed-point character (`thompson-f-sofic-iff-relator-system-unstable`).
4. **In general.** Open: does `t > 0` on some `F`-set force `F` to be amenable? If it does, following
   models are no route to soficity at all.
