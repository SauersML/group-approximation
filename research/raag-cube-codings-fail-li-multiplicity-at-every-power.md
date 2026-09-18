---
rg: 2
id: raag-cube-codings-fail-li-multiplicity-at-every-power
kind: claim
title: For every right-angled Artin group, Li's multiplicity condition (t<d) fails for the pointed-cube coding of its Salvetti complex with the height-at-most-N Garside family, for every N; the only return of a maximal-clique state is itself
requires:
  - cubulated-groups-act-by-bisections-of-a-pointed-cube-category
  - commutative-cube-degree-maps-force-tree-products
distinct_from:
  cubulated-groups-act-by-bisections-of-a-pointed-cube-category: that reduces Q1.15 to Li's gates for C_X and leaves (t<d) open; this shows (t<d) fails there for every RAAG, at every power of the clique family.
---

**ESTABLISHED** (lane proof, elementary; Li's definitions read at source in
arXiv:2110.04505v2: (St) with (1_Γ), (2_Γ) at l.1219–1245, `lem:gamma` at l.1128,
(`t < d`) at l.1611, `lem:deg--desc:d` at l.1989; not independently reviewed; no
priority claimed). This is an obstruction to **the method** on this coding, not to
finite presentation of any group.

**Setting.** `X̃` is the Salvetti cover of `A_Γ`. `C_X` has objects the *states*: signed
cliques `Q`, the set of final letters, including `∅` at the base. Its morphisms are
reduced signed traces. The degree is `d: C_X → A_Γ^+` (forget signs), which has (UFP*).
`𝔖_N` is a transversal of the traces of Cartier–Foata height at most `N`. `𝔖_1` is
bh-free-36's clique family.

**Theorem.** Fix `N ≥ 1`. Suppose Li's data `𝔛, Γ` satisfy his condition (St) for
`(C_X, 𝔖_N)` and contain the base object. Then condition (`t < d`) fails. More
precisely, let `Q` be any maximal signed clique (its support is a maximal clique of
`Γ`). Then:
1. `X(Q) = X(Q; ∅)` lies in `𝔛(*)`: it is the piece of every maximal simple whose
   last layer is `Q`.
2. There is a generator `γ ∈ Γ(*)` with target `X(Q)` whose domain contains `X(Q)`
   **exactly once**:
   - for `N = 1`, the full expansion `γ(∅, 𝔖_1)`, forced by (1_Γ);
   - for `N ≥ 2`, the completion `γ(∅, 𝔰_c)` with `c = Q^{N−1}` and
     `𝔰_c = {s : ‖cs‖ = ‖c‖}`, forced by (2_Γ).

**Proof.**
- **Blocked letters.** From state `Q` a letter `x` (not an inverse of a letter of `Q`)
  is *blocked* if it starts a new layer: either it lies on a vertex of `Q` with the
  same sign, or it fails to commute with some letter of `Q`. Since `supp Q` is a
  maximal clique, every allowed letter is blocked.
- **The completion set.** Hence `‖Q^{N−1}s‖ = ‖Q^{N−1}‖` (one block of height `≤ N`)
  iff `s` is a single layer. So `𝔰_c` is the set of allowed cliques at `Q`; for
  `N = 1` it is `𝔖_1` itself.
- **Pieces of the expansion.** By `lem:gamma`, the domain of `γ(∅, 𝔰_c)` consists of:
  - the leftover `X(Q; 𝔰_c)`, which is empty because every path starts with a
    blocked letter;
  - the pieces `X(d(s); f_s)`.

  For non-maximal `s`, the set `f_s` contains the extensions of `s` inside `𝔰_c`, so
  the piece is not `X(Q; ∅)`. For maximal `s` (a maximal allowed clique), `f_s = ∅`.
- **Only `s = Q` returns.** The new state is
  `d(s) = s ∪ {q ∈ Q : q commutes with supp s and lies off supp s}`. Here `supp s` is
  a maximal clique, so the second set is empty and `d(s) = s`. So the piece equals
  `X(Q)` iff `s = Q`, which is exactly one index.
- **Units don't help.** Units of `C_X` are identities, so right multiplication by
  `𝐂^*` does not change the pieces. Hence (`t < d`) fails at `γ`.
- **Reachability.** For item 1: in the full expansion of the base, `X(Q)` is the piece
  of the maximal simple `Q^N`, with `f = ∅`.

**Why this is structural (label rigidity).** A single layer's new state is determined
by its signed labels. So from a state, at most one layer returns to that state. Li's
(`t < d`) needs two returns at every basic expansion. Passing to `𝔖_N` does not help,
because (2_Γ) always contains the one-layer completions of a block of height `N−1`.
This is the RAAG form of "labels are injective at vertices". The same argument should
apply to any special cube complex, where pointed-cube types carry injective labels; that
extension is not written out here.

**Calibrations (task 1).**
- **Free group** (`Γ` = two isolated vertices). Here `C_X` is the 4-state reduced-word
  automaton plus a base state. With the trace degree (the free monoid), (`t < d`) fails
  as above: from state `a`, only the letter `a` returns. The *length* degree to `N` is
  commutative, and the tree is a product of one tree, as in
  `commutative-cube-degree-maps-force-tree-products`. For it, power 2 plus phase `Z/2`
  give 3 loops of length 2 at every state, so Li's `k`-graph theorem applies. **The
  calibration passes only after recoding.**
- **Square** (`A_Γ = F_2 × F_2`, `X̃ = T × T`). The same holds with the two-colour
  count degree. This is the cube 2-graph of `cocompact-tree-product-lattices-lie-in-type-a-class`.
- **Path `P_4`** (`a–b–c–d`). This is the smallest `Γ` that is not a join of independent
  sets. By `commutative-cube-degree-maps-force-tree-products` there is no commutative
  (UFP*) degree, and by the theorem there is no trace-degree certificate at any power.
  The letter-count phase `ab(d) mod N` also fails: its phase-0 subcategory already has
  infinitely many atoms for the free group (`a b^{2k} a`, `N = 2`), so Li's local
  finiteness fails.

**Faithfulness (task 3).** Replace `G` by `G * Z`: for RAAGs, `A_{Γ ⊔ pt}`, still
special. Then `G * Z` acts faithfully on the regular Roller boundary `R`.
- The ends of the Bass–Serre tree of `G * Z` embed `G * Z`-equivariantly in `R`. Their
  rays cross `z`-hyperplanes infinitely often and never return to a piece, so they
  leave every carrier.
- The kernel of the action on `R` therefore fixes every end of a minimal non-elementary
  tree action, so it acts trivially on the tree.
- It lies in the intersection of conjugates of a free factor, which is trivial.

For `A_Γ` itself the kernel contains the centre, generated by the vertices adjacent to
all others, since central translations fix `R`. Closedness of `R` holds for trees and
tree products. In general it is **not checked**; Li's `Ω_∞` closure would be used
instead.

## Lesson for general BH

Li's (`t < d`) is loop-richness: every basic clopen piece must return at least twice in
one expansion step. Codings whose states are read off from injective labels (special
cube complexes, RAAG heaps) are **deterministic automata**. There each state has at most
one self-return per layer, and powers cannot fix this without an additive grading, which
exists only for products (`commutative-cube-degree-maps-force-tree-products`). So Li's
theorem certifies cube codings exactly for products of trees. Loops must come from
elsewhere:
- an overcoding into a loop-rich shift, as in Salo's RAAG ⊂ 2V through the full shift,
  which drops the reducedness constraint;
- or a finiteness theorem for deterministic codings. The natural replacement is to
  require only that the type-substitution matrix of full expansions be primitive with
  Perron eigenvalue `> 1`, instead of diagonal `≥ 2` (OPEN).

For non-special cubulated groups (Q1.15), labels are not injective. Self-returns may
genuinely multiply there, so that is where Li on `C_X` still has a chance.
