# A monomial of S grafts only onto the first K(S) roots, so every factorisation of s z keeps the same tail and stubbornness is a fibrewise property of the finite prefix worlds

*Attempt artifact (2026-09-18), formerly route `thompson-f-stubborn-tail-splitting-proof` into
`thompson-f-stubborn-sets-split-off-the-tail`, requires
[thompson-f-p22-monomials-admit-no-private-pivot-order,
thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs]. Demoted from the graph at landing
because two of the three swarm-0917 referee lenses refuted item 4 of the target claim (the
"strictly stronger than `Lambda_S(D) >= 2`" corollary and the `distinct_from` that rests on it);
the referee reasons are recorded verbatim under `## Attempts` of the target. Lenses 2 and 3 both
judged Steps 0-3 and 5 sound and reproduced the computations, so restore this as a route once item
4 is restated (as `Lambda_S(D) >= 2` for all `D <= A`, re-derived) or dropped and the
`distinct_from` against `thompson-f-monomial-doubling-ratio-is-a-finite-computation` is rewritten.*

Artifacts: `experiments/thompson-f-pivot-orders-2026-09-18/` (`forests.py`, `prefix_core.cpp`,
`prefix_census.py`, `selftest.py`, `verify.jsonl`, `core_atoms.py`, `selftest.out`).

Notation as in the claim. The two required claims are used for the definition of a stubborn set and
of `core`, for the fact that a stubborn set kills every private pivot order (item 1 of
`thompson-f-p22-monomials-admit-no-private-pivot-order`), for the peeling characterization and the
counting bound (its items 2 and 3), and for the doubling consequence of a pivot order
(`thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs`, item 1).

**Step 0: the forest model, and `K(S)`.** `M` is the monoid of forests of binary trees on roots
`0, 1, 2, ...` with finitely many carets; `x_j z` replaces the roots `j, j+1` of `z` by one caret
above them; the product `s z` of two forests grafts the `i`-th root tree of `z` onto the `i`-th leaf
of `s`. This is the standard forest presentation of the positive monoid. It is a model of `M`: the
defining relation `x_j x_i = x_i x_(j+1)` for `i < j` holds in it, so the presented monoid maps onto
the forest monoid; and normal forms map bijectively onto forests, since applying the letters of a
non-decreasing word from the right and reading a forest off by repeatedly peeling its leftmost root
caret are mutually inverse (`selftest.py`, items 1 and 2 of its output). Write
`s = x_(s_0) ... x_(s_(d−1))` in normal form and build the forest by applying the letters from the
right: after the merges at positions `d−1, ..., t+1` the forest has `K − (d − 1 − t)` roots, so the
merge at position `t` needs `s_t + 1 <= K − (d−1−t) − 1`, that is `K >= s_t + d − t + 1`. Taking the
maximum over `t` and over `s ∈ S` gives `K = K(S)`, and for the maximising pair the inequality is
tight, so `K − 1` leaves do not suffice. Hence every `s ∈ S` is `s̄ ⊔ (trivial tail)` with `s̄` a
forest of `K` leaves, `d` carets and `K − d` roots.

**Item 1 (tail splitting).** Let `z = (u ; v)`, so the root sequence of `z` is the `K` trees of `u`
followed by the trees of `v`.
- *Products.* Grafting `z` onto `s` puts the trees of `u` on the leaves `0, ..., K−1`, which are the
  leaves of `s̄`, and puts the trees of `v` on the leaves `K, K+1, ...`, which are the trivial trees
  of the tail of `s`. So the root sequence of `s z` is the `K − d` roots of `s̄ · u` followed by the
  roots of `v`, i.e. `s z = (s̄ · u ; v)`.
- *Factorisations.* Let `w = s z = (s̄ · u ; v)` and suppose `w = s' z'` with `s' ∈ S`, `z' ∈ M`.
  Write `z' = (u' ; v')`. By the previous bullet `w = (s̄' · u' ; v')`. Both `s̄ · u` and `s̄' · u'`
  are forests with exactly `K − d` roots, so comparing the root sequences of the two expressions for
  `w` term by term gives `s̄' · u' = s̄ · u` (the first `K − d` roots) and `v' = v` (the rest).
- *Privacy.* Fix `Z ⊆ M_D` and `z = (u ; v) ∈ Z`. For `s ∈ S`, by the two bullets
  `N(s z) ∩ Z = { (u' ; v) : u' ∈ Z_v and s̄' · u' = s̄ · u for some s' ∈ S }`. So `s z` is private
  for `z` in `Z` if and only if `s̄ · u` is private for `u` in `Z_v` inside the prefix world. The map
  `s ↦ s̄` is a bijection of `S` onto its prefix forests, so the counts agree.

This is checked directly on random data (`selftest.py`, item 4: for random `u ∈ P_a`, random tails
`v` and all `s, s' ∈ S_(3,5)`, `s z = (s̄ · u ; v)` and every factorisation of `s z` by an element of
`S`, padded with trivial trees to the width of `s z`, keeps the tail `v`).

**Item 2 (fibrewise criterion).** By the privacy statement, the number of private successors of
`z = (u ; v)` in `Z` equals the number of private successors of `u` in `Z_v`. So `Z` is stubborn iff
every nonempty fibre `Z_v` is stubborn. Let `C = ⨆_v core(P_(D − c(v))) × {v}`, the union over all
tails `v` with `c(v) <= D`. Its fibre at `v` is `core(P_(D − c(v)))`, which is stubborn or empty, so
`C` is stubborn by the criterion just proved; and any stubborn `W ⊆ M_D` has every fibre `W_v`
stubborn, hence `W_v ⊆ core(P_(D − c(v)))` by maximality of the core, hence `W ⊆ C`. So `C` is the
union of all stubborn subsets of `M_D` (note that stubbornness is *not* inherited by subsets — no
one-point deletion of the 24-point `S(1,2)` core is stubborn, `core_atoms.py` — so this is an
argument about fibres, not about subsets). The remaining bullets follow:
`core(M_D) ≠ ∅` iff some `a <= D` has `core(P_a) ≠ ∅`; the least such `D` is the least such `a`
(take `v` trivial, so `a = D`); and by item 2 of the required claim a pivot order exists iff no layer
has a stubborn subset, i.e. iff `core(P_a) = ∅` for every `a`.

**Item 3 (letters).** Let `z ∈ P_a`. The normal form of a forest is read by repeatedly peeling the
leftmost root caret: if the current forest has `r` roots and its leftmost root caret is at index `j`,
the next letter is `j <= r − 1` and the peel leaves `r + 1` roots. The letters come out
non-decreasing — the roots to the left of `j` were leaves and stay leaves — so the sequence is the
normal form, and its largest letter is the last one. Starting from `r = K` and peeling `a` times, the
letter at step `t` is at most `K + t − 1`, so every letter is at most `K + a − 2`. The bound is
attained by the forest whose first root is the right vine on `a + 1` leaves. The census script uses
`R_S(a) = max_{s,t} ( s_t + a + d − t − 1 ) = a + K − 2`, so `P_a ⊆ M_(a, R_S(a))`; this equality and
the attainment are checked in `selftest.py`, item 3. A stubborn subset of `P_a` is a stubborn subset
of `M_(a, R_S(a))`, so `core(M_(a, R_S(a))) = ∅` forces `core(P_a) = ∅`, and then `core(M_a) = ∅` by
item 2.

**Item 4 (doubling).** Let `Y ⊆ M_D` be finite with `D <= A`, and decompose `Y = ⨆_v Y_v × {v}` by
tails. By item 1, `S Y = ⨆_v (S̄ Y_v) × {v}` — the products with different tails are distinct, and
products with the same tail agree iff their prefix parts agree. Each `Y_v` lies in `P_(D − c(v))`
with `D − c(v) <= A`, and `core(P_(D − c(v))) = ∅` forces `core(Y_v) = ∅` (a stubborn subset of `Y_v`
is a stubborn subset of the prefix world), so `|S̄ Y_v| >= 2|Y_v|` by item 3 of the required claim.
Summing, `|S Y| >= 2|Y|`. For a finite `Y` spread over several layers, `S` maps distinct layers to
distinct layers, so the bounds add.

**Item 5 (common left factor).** Let `S = t S''`. `M` embeds in `F`, so left multiplication by `t` is
injective on `M`, and `w ↦ t^(−1) w` is a bijection from `S M_D` onto `S'' M_D` with
`N_S(w) = N_(S'')(t^(−1) w)`: indeed `w = t s'' z` iff `t^(−1) w = s'' z`. The bipartite graph
`(M_D, S M_D)` is therefore isomorphic to `(M_D, S'' M_D)` by the identity on the left and this
bijection on the right, so the two have the same stubborn subsets and the same cores.
For `S(m,d) = { x_(i_1) ... x_(i_d) : i_1 <= ... <= i_d, i_t <= m + t − 1 }`, the case `m = 0` forces
`i_1 = 0`, so `S(0,d) = x_0 · { x_(i_2) ... x_(i_d) : i_t <= t − 1 }`, and re-indexing `j = t − 1`
identifies the second factor with `S(1, d−1)`.

**Item 6 (computations).** `prefix_core.cpp` enumerates `P_a` and the target layer
`B_a = {forests with K − d roots and a + d carets}` by an exact lattice-path rank, which is a
bijection with `[0, f(K+a, K))` and `[0, f(K+a, K−d))` respectively (a forest of `r` trees with `n`
leaves is the preorder word with `n` zeros for leaves and `n − r` ones for carets, every proper
prefix having fewer than `r` more zeros than ones); the rank is checked against `unrank` at 1000
points of each run. Predecessors are never stored: by item 1 they are recomputed by peeling each
product with every `s' ∈ S`. Peeling is the greedy deletion of the required claim, item 2, and the
survivor set is re-verified from scratch with a separate product table before anything is printed
(`verified_stubborn: true` on every row). `selftest.py` checks the model against the Python
reference `forests.py` on 14 layers, including the 1092-point `S_(3,5)` core, and checks that this
core is *the same set of forests* as the published word list `s35_stubborn_core_D7.txt`, which the
2026-09-17 word-rewriting implementation produced; it also checks item 5 on
`S(0,3) = x_0 · S(1,2)`, where the cores agree as sets for `a <= 4`. The reproduction of the
published census is `verify.jsonl`; the new layers are `survivors.jsonl` and `family.jsonl`.
