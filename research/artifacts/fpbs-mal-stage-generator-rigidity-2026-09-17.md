# Generator rigidity for the stage pairs of Gamma_mal

Supporting proof for `fpbs-mal-stage-generators-lie-in-b-double-coset` and
`fpbs-mal-single-generator-packing-floor-uniform`. Worker
swarm-0917-w6-w6-fp-last2, 2026-09-17.

## 0. Setting and statement

`Gamma_mal = U_m H_m`, where `H_m` is free on `{a, b_m}` and
`b_{m-1} = b_m a b_m^{-2}`. Fix `n < m` and put `d = m - n`. In the basis
`{a, b} = {a, b_m}` of `F = H_m`,

    H_n = <a, W_d>,   W_1 = b a b^{-2},   W_{d+1} = W_d a W_d^{-2},

since `b_{m-d-1} = b_{m-d} a b_{m-d}^{-2}` and `b_{m-d} = W_d(a, b_m)`.

**Theorem R (generator rigidity).** For all `n < m` and `t ∈ H_m`,

    <H_n, t> = H_m   implies   t ∈ H_n b_m H_n ∪ H_n b_m^{-1} H_n.

**Corollary P.** For every `n < m` and every `t` with `<H_n, t> = H_m`, every
detour-packing certificate for `relC(H_m; H_n)` with the single new
generator `t` is at least `δ_mal`. Here `δ_mal > 0` is the constant of Item 4 of
`fpbs-malnormal-coset-cycles-linear-perimeter`. So
`inf_j exp(-h_{t_j}) >= δ_mal` along every sequence of generators of stage
pairs, and `fpbs-mal-long-generator-packing-growth` is false.

Letters `a, b` and inverses `A, B`. A Stallings graph is folded, based, and
labelled over `{a, b}`. For a vertex `p`, `L(p) ⊆ {a, A, b, B}` is the set of
labels of half-edges leaving `p`.

## 1. Generating elements come from vertex identifications

Let `H <= F = F(a, b)` be finitely generated with `H != F`. Let `Δ` be its
Stallings graph with base `o`. For a vertex `p`, let `g_p` be any word read in
`Δ` from `o` to `p`.

**Lemma 1.** Suppose `<H, t> = F`. Then there are vertices `p != q` of `Δ` with
`t ∈ H g_p g_q^{-1} H`. Moreover, the folding of `Δ/(p ~ q)` is the
one-vertex rose.

*Proof.* The Stallings graph of `<H, t>` is the folding of `Δ` with a loop
reading the reduced word `t` attached at `o`. Let `u` be the longest prefix
of `t` that can be read from `o` in `Δ`, ending at `p`. Let `u'` be the longest
suffix of `t` such that `u'` reads in `Δ` from some vertex to `o`.

**Case `|u| + |u'| < |t|`.** Write `t = u s u'` with `s` nonempty. Fold the
two ends of the loop along `Δ`. What remains is `Δ` with an arc reading `s`
attached from `p` to the start vertex `q'` of `u'`. By maximality, `s[0]` is not
in `L(p)` and `s[-1]^{-1}` is not in `L(q')`. So no fold involves an edge of
`Δ`. The only possible folds are between the two end edges of the arc, when
`p = q'` and `s[0] = s[-1]^{-1}`, and they fold the arc onto itself. Hence no
two vertices of `Δ` are ever identified. The folded graph has at least
`|V(Δ)| >= 2` vertices, since `H != F` forces `Δ` to be more than the rose.
So `<H, t> != F`, a contradiction.

**Case `|u| + |u'| >= |t|`.** Write `t = u s`. Then `s` is a suffix of `u'`, so
`s` reads from some vertex `q` to `o`. Since `u` and `g_p` both read `o -> p`,
`u g_p^{-1} ∈ H`. Since `g_q s` reads `o -> o`, `s ∈ g_q^{-1} H`. Hence
`t ∈ H g_p g_q^{-1} H`. Folding `u` and then `s` into `Δ` sends the middle
vertex of the loop to both `p` and `q`, and absorbs the loop into `Δ`. So the
fold of `Δ` with the loop equals the fold of `Δ/(p ~ q)`, which is the rose. If
`p = q`, then `t ∈ H`, and `<H, t> = H != F`. QED.

Call such an ordered pair `(p, q)` *generating* for `Δ`. The relation
`Δ/(p~q) = Δ/(q~p)` makes the notion symmetric. If `L(p) ∩ L(q) = ∅`, then
`Δ/(p ~ q)` is already folded, of rank `rank(H) + 1`. For `rank(H) = 2` this is
not the rose, so the pair is not generating.

## 2. Generating pairs descend along the stage morphism

Let `Δ_d` be the Stallings graph of `H_{m-d} = <a, W_d>` in `F(a, b_m)`. Since
`H_{m-d-1} <= H_{m-d}`, reading words gives a label-preserving morphism
`π: Δ_{d+1} -> Δ_d` of based graphs.

**Lemma 2.** If `(p, q)` is generating for `Δ_{d+1}`, then `(π p, π q)` is
generating for `Δ_d`.

*Proof.* Put `t = g_p g_q^{-1}`. Then `<H_{m-d-1}, t> = F` by Lemma 1, so
`<H_{m-d}, t> = F`. In `Δ_d` the word `g_p` reads `o -> π p`, and `g_q^{-1}` reads
`π q -> o`. The second case of the proof of Lemma 1 shows that the fold of
`Δ_d` with the loop `t` is the fold of `Δ_d/(π p ~ π q)`. That fold is the rose,
and `π p != π q` since `t ∉ H_{m-d}`. QED.

## 3. The Stallings graphs are dumbbells

**Lemma 3.** For every `d >= 1`, `Δ_d` is the following dumbbell:
- an `a`-loop at the base `o`;
- a bridge reading `β_d` from `o` to a vertex `v_d`;
- a loop reading `λ_d` at `v_d`;
- every other vertex has degree 2.

The words satisfy

    β_1 = b,  λ_1 = aB,
    β_{d+1} = β_d λ_d,
    λ_{d+1} = β_d^{-1} a β_d λ_d^{-1}.

Also `W_d = β_d λ_d β_d^{-1}`. At `v_d` the three half-edge labels
`β_d[-1]^{-1}`, `λ_d[0]`, `λ_d[-1]^{-1}` are pairwise distinct. So
`L(v_d) = {a, b, B}`, and `β_d[0] = b`.

*Proof.* Induction on `d`.

**Base.** `W_1 = b·aB·B` gives the 3-vertex dumbbell with
`L(v_1) = {B, a, b}`.

**Step.** Suppose the statement holds at `d`, and write `β = β_d`, `λ = λ_d`.
Then

    W_{d+1} = β λ β^{-1} · a · β λ^{-1} β^{-1} · β λ^{-1} β^{-1}
            = β λ β^{-1} a β λ^{-1} λ^{-1} β^{-1}.

Every junction of this word is reduced.
- **`λ|β^{-1}` and `β|λ^{-1}`.** These cancel iff `λ[-1] = β[-1]`, that is iff
  two half-edges at `v_d` coincide.
- **`β^{-1}|a|β`.** This reads `B a b`.
- **`λ^{-1}|λ^{-1}`.** `λ` is cyclically reduced, since its two half-edges at
  `v_d` are distinct.
- **`λ^{-1}|β^{-1}`.** This cancels iff `λ[0] = β[-1]^{-1}`, which is excluded
  at `v_d`.

Regroup as `(β λ)(β^{-1} a β λ^{-1})(β λ)^{-1}`. The word `β_{d+1} = βλ` is
reduced, since `λ[0] != β[-1]^{-1}`. The word `λ_{d+1}` has first letter
`β[-1]^{-1}` and last letter `λ[0]^{-1}`. The three half-edges at the new
vertex `v_{d+1}` are:
- `β_{d+1}[-1]^{-1} = λ[-1]^{-1}`;
- `λ_{d+1}[0] = β[-1]^{-1}`;
- `λ_{d+1}[-1]^{-1} = λ[0]`.

These are exactly the three half-edges at `v_d`, so they are pairwise distinct.
In particular `λ_{d+1}` is cyclically reduced, and `L(v_{d+1}) = L(v_d)`.

The bridge still begins with `b`, so `L(o) = {a, A, b}`. The dumbbell built
from `β_{d+1}, λ_{d+1}` is therefore folded, and its based loop words generate
`<a, β_{d+1} λ_{d+1} β_{d+1}^{-1}> = <a, W_{d+1}>`. So it is `Δ_{d+1}`. QED.

**Machine check.** `experiments/mal-long-generator-packing-2026-09-17/dumbbell.py`
extracts the bridge and the loop from the folded graphs for `d <= 7` and
confirms the recurrence. The lengths are `|β_d| = 1, 3, 8, 20, 49, ...` and
`|λ_d| = 2, 5, 12, 29, 70, 169` (Pell numbers).

**Consequence used below.** For `d >= 3`,

    β_d = β_3 λ_3 ... λ_{d-1},   β_3 = baBBabbA,   |β_d| >= 8.

## 4. The generating pairs of `Δ_d`

Write `0` for the base of `Δ_d`, and `0b`, `0ba` for the vertices reached from
`0` by reading `b` and `ba` along the bridge.

**Proposition 4.** For `d >= 2`, the generating ordered pairs of `Δ_d` are
exactly `(0, 0b)`, `(0, 0ba)` and their reverses. For `d = 1` there are 6
generating ordered pairs. In both cases every generating pair `(p, q)` has
`g_p g_q^{-1} ∈ H b H ∪ H B H`, where `H = H_{m-d}`.

The double coset `H g_p g_q^{-1} H` does not depend on the choice of the words
`g_p, g_q`. Two words read `o -> p` differ on the left by an element of `H`.

**Base `d = 1, ..., 5`: exact computation.**
`experiments/mal-long-generator-packing-2026-09-17/vertex_pairs.py 5` builds
`Δ_d`. For every ordered pair `p != q`, it tests whether `<H, g_p g_q^{-1}> = F`
by folding, and tests membership in `H b^{±1} H` by folding the graph
`o -b^{±1}- o'` over two copies of `Δ_d`. Output:

    d=1 |V|=3   generating ordered pairs=6  outside H b^+-1 H=0
    d=2 |V|=8   generating ordered pairs=4  outside H b^+-1 H=0
    d=3 |V|=20  generating ordered pairs=4  outside H b^+-1 H=0
    d=4 |V|=49  generating ordered pairs=4  outside H b^+-1 H=0
    d=5 |V|=119 generating ordered pairs=4  outside H b^+-1 H=0

`pairs_show.py 5` prints the pairs for `d >= 2`. They are
`('', 'b'), ('', 'ba')` and the reverses, that is `(0, 0b), (0, 0ba)` and the
reverses. The targets give `t = B`, `t = AB ∈ H B H` and `t = b`,
`t = ba ∈ H b H`.

**Induction step `d -> d+1` for `d >= 3`.** Assume Proposition 4 at `d`. Let
`(p, q)` be generating for `Δ_{d+1}`. By Lemma 2, `(π p, π q)` is generating
for `Δ_d`, so `{π p, π q} = {0, 0b}` or `{0, 0ba}`. By symmetry, take
`π p = 0` and `π q ∈ {0b, 0ba}`.

*Fibres of `π`.* By Lemma 3, `Δ_{d+1}` consists of the `a`-loop at `o`, the
bridge `β_{d+1} = β_d λ_d`, and the loop `λ_{d+1} = β_d^{-1} a β_d λ_d^{-1}`.
The map `π` sends these onto the following walks in `Δ_d`.
- The `a`-loop goes to the `a`-loop at `0`.
- The bridge goes to the bridge `β_d`, followed by one turn around `λ_d`.
- The loop goes to `β_d` backwards, then the `a`-loop at `0`, then `β_d`
  forwards, then `λ_d` backwards.

Interior vertices of the bridge and of the loop of `Δ_d` are distinct from
`0`. So `π^{-1}(0) = {o, y, z}`. Here `y -a-> z` is the middle `a`-edge of
the loop segment reading `β_d^{-1} a β_d`. Since `|β_d| >= 8`, the vertices
`0b` and `0ba` are interior to the bridge of `Δ_d`, which the walks above
cover three times. So

    π^{-1}(0b)  = {ob,  yb,  zb},
    π^{-1}(0ba) = {oba, yba, zba},

where `xb`, `xba` means reading `b`, `ba` from `x` along the corresponding copy
of `β_d`. For `y` the copy is read backwards into the loop segment. There are
`3 × 6 = 18` candidate pairs. Two of them are the targets `(o, ob)` and
`(o, oba)`.

*Local model.* Since `β_d` begins with `β_3 = baBBabbA`, the following
subgraph `M` of `Δ_{d+1}` is embedded:
- the `a`-loop at `o` and the path reading `β_3` from `o`;
- the loop segment `β_3^{-1} a β_3` around the edge `y -a-> z`.

Every vertex of `M` other than the three path ends has all of its
`Δ_{d+1}`-half-edges in `M`. These are `o` and the interior vertices of the
bridge and of the loop, which have degree 2. The path ends are called
*boundary vertices*. The labels in `M` are:

    o: {A, a, b}     y: {a, b}     z: {A, b}
    ob, yb, zb: {B, a}             oba, yba, zba: {A, B}

`M` is embedded injectively. The bridge prefix has 8 edges, and the bridge has
`|β_{d+1}| >= 20` edges. The loop segment has 17 edges, and it lies inside
`β_d^{-1} a β_d`, a subpath of the simple loop `λ_{d+1}`. Its ends may equal
`v_{d+1}` when `d = 3`, but that only makes them boundary vertices.

*Closure criterion.* Fold `Δ_{d+1}/(p ~ q)` by the least equivalence relation
`~` with `p ~ q` that is closed under the rule: if `u ~ v` and both have an
`x`-half-edge, then their `x`-neighbours are equivalent. `local_closure.py`
computes the least such relation `~_M` on `M`. Suppose no boundary vertex lies
in a nontrivial `~_M`-class. Then every vertex in a nontrivial class has all of
its `Δ_{d+1}`-half-edges inside `M`. So `~_M` is already closed in `Δ_{d+1}`,
and it equals the global relation. A vertex that is alone in its class has at
most one `x`-half-edge, because `Δ_{d+1}` is folded. So the quotient is folded,
with `|V(Δ_{d+1})| - merges` vertices.

*Hand checks.*
Write `x3` for the vertex read by `baB` along a copy of `β_3`. Its labels are
`{b, B}`.
- **`(y, ob)`.** `L(y) = {a, b}` and `L(ob) = {B, a}` share only `a`. So
  `z ~ oba`. Then `L(z) = {A, b}` and `L(oba) = {A, B}` share only `A`, and the
  `A`-neighbours are `y` and `ob`, which are already equivalent. The relation is
  closed: classes `{y, ob}` and `{z, oba}`, 2 merges, no boundary vertex.
- **`(o, yb)`.** `L(o) = {A, a, b}` and `L(yb) = {B, a}` share only `a`, so
  `o ~ yba` and the class is `{o, yb, yba}`.
  - `L(yba) = {A, B}`. Its `A`-neighbour `yb` matches the `A`-neighbour `o` of
    `o`, and they are already equivalent.
  - Its `B`-neighbour is `y x3`, and `yb` has `B`-neighbour `y`. So
    `y ~ y x3`.
  - `L(y) = {a, b}` and `L(y x3) = {b, B}` share only `b`, and the
    `b`-neighbours are `yb` and `yba`, which are already equivalent.

  The relation is closed: classes `{o, yb, yba}` and `{y, y x3}`, 3 merges, no
  boundary vertex.

*All 16 non-target candidates.* `local_closure.py` builds `M` and runs the
closure for each candidate. Output:

    pair (o,yb|zb|yba|zba): local, vertex merges=3
    pair (y,ob|yb|zb):      local, vertex merges=2
    pair (y,oba|yba|zba):   local, vertex merges=1
    pair (z,ob|yb|zb):      local, vertex merges=1
    pair (z,oba|yba|zba):   local, vertex merges=2
    ALL NON-TARGET CANDIDATES CLOSE LOCALLY

The two targets touch the boundary, as they must. By the closure criterion,
each non-target quotient folds to a graph with at least
`|V(Δ_{d+1})| - 3 >= 49 - 3` vertices. That is not the rose, so no non-target
pair is generating.

The targets are generating, since `<H, b> ∋ a, b`, and likewise for
`B, ba, AB`. So the generating pairs of `Δ_{d+1}` are exactly `(0, 0b)`,
`(0, 0ba)` and their reverses, and Proposition 4 holds at `d + 1`.

The base covers `d <= 5`, and the step applies for every `d >= 3`. So
Proposition 4 holds for all `d >= 1`. QED.

## 5. Proof of Theorem R and Corollary P

**Theorem R.** Let `n < m`, `d = m - n`, `H = H_n = H_{m-d}`, `F = H_m`, and
`<H, t> = F`. Since `H != F` (the index is infinite, since `Δ_d` is not a covering), Lemma
1 gives a generating pair `(p, q)` of `Δ_d` with `t ∈ H g_p g_q^{-1} H`. By
Proposition 4, `H g_p g_q^{-1} H` is `H b_m H` or `H b_m^{-1} H`. QED.

**Corollary P.** Imported verbatim from
[[fpbs-malnormal-coset-cycles-linear-perimeter]] Item 4:

> Every packing certificate for `relC(H_m; H_n)` with new generator `b_m`, or
> with any generator in `H_n b_m^{±1} H_n`, is at least the constant
> `δ_mal = δ(F_2, <a, b a b^{-2}>, b)`

(proof in that node's artifact §6, "Double-coset generators"). By Theorem R,
every `t` with `<H_n, t> = H_m` lies in `H_n b_m^{±1} H_n`. So every
single-generator packing certificate for every stage pair is at least
`δ_mal`, and `inf_j exp(-h_{t_j}) >= δ_mal > 0` along any sequence. Therefore
`fpbs-mal-long-generator-packing-growth` is false. QED.

**Correction.** Artifact §7 of the linear-perimeter node suggests long generators outside
`H_n b_m^{±1} H_n` "may" exist. They do not. The generating set of a stage pair
is as rigid as that of the top pair: up to `H_n` on both sides, it is `b_m`.

## 6. What dies and what survives

**Invariant.**
- The set of vertex pairs of the dumbbell `Δ_d` whose identification folds to
  the rose. It is `{(0, 0b), (0, 0ba)}` up to order, for all `d >= 2`.

**Dying step.**
- **Step.** The step of `fpbs-mal-long-generator-packing-growth` that must
  produce a generator `t_j` of `(H_{m_j}, H_n)` outside `H_n b_{m_j}^{±1} H_n`.
- **Why it dies.** No such `t_j` exists (Theorem R), so the floor of Item 4
  applies to every generator.
- **Consequence.** Together with Items 2 and 4 of the linear-perimeter node,
  single-generator detour packing (2.1) is dead for `Gamma_mal`:
  - at every stage pair;
  - with every generator;
  - in every growth regime.
  - Neither the stage-sum strategy nor the subsequence strategy can be
    certified this way.

**Survivors (not touched here).**
- Repairs using several new generators on correlated sets. For a stage pair,
  such a family can be `{b_m, h b_m h'}` with different syllables, and it is not
  a (2.1) certificate.
- Repairs that are not Bernoulli colorings, or that are not built from detours.
- Direct lower bounds on `relC(H_m; H_n)`. A positive lower bound would give
  infinite free cost for `Gamma_mal`.

## 7. Reproduction

From `experiments/mal-long-generator-packing-2026-09-17/`:

    python3 vertex_pairs.py 5      # base census, d = 1..5 (d = 5 takes a few minutes)
    python3 pairs_show.py 4        # the generating pairs for d <= 4
    python3 dumbbell.py 1 7        # dumbbell recurrence for d = 1..7
    python3 local_closure.py       # the 16 local closures of the induction step
    python3 gens_census.py 1 9     # brute force: 2850 generators of length <= 9, none outside H b^+-1 H
    python3 gens_census.py 2 8     # brute force: 226 generators of length <= 8, none outside
