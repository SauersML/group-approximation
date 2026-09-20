# Finite shuffles for the H1 cloning identity

Status: mathematical construction and Lean continuation plan, 2026-09-20.
The diagonal homomorphism and its boundary action are now checked in
`EnvelopeHigmanVCSwindleDiag.lean`; the coherent shuffles and kernel identity
remain to be completed. `EnvelopeHigmanVCSwindleShuffle.lean` now supplies the
explicit elementary shuffle, incomparable-middle commutation, diagonal
conjugation, ordered-product insertion, and matched-expansion naturality.
`EnvelopeHigmanVCSwindleAction` and `EnvelopeHigmanVCSwindleSupport` now
check the boundary action and unchanged-cone calculation.
`EnvelopeHigmanVCSwindleCodeAction` checks leaf-expansion compatibility and
existence of a lift for each finite expansion tree.
`EnvelopeHigmanVCSwindleSeed` checks exact seed naturality for swaps of code
leaves, using the splitting and conjugation relators.
**The cloning product identity and H1 are not formalized by this note.** The
identities below have a direct finite algebraic argument, but canonical
code-shuffle coherence and compatible tables still need Lean proofs. Existence
of a lift alone does not supply coherence. No new Lean axiom was added.

## Target and existing results

Fix `d > 1`, write `A = Fin d`, and use the existing objects

- `Q = higmanVCCommon_Q d`;
- `E = higmanVCTreeNF_E d`;
- `s(x,y) = higmanVCCommon_mk d (FreeGroup.of (x,y))`;
- `φ_c = higSw_phi d c`.

Concatenation is written by juxtaposition. A letter `a` in a concatenation means
the singleton list `[a]`. Products of boundary permutations act on the rightmost
factor first.

The missing identity is

```
Δ(z) := ((List.finRange d).map fun a => higSw_phi d [a] z).prod = z
                                                        (z ∈ ker E).
```

The source already proves the following, without an H1 assumption:

| Declaration | Content needed here |
| --- | --- |
| `higmanVCCommon_mk_split` | `s(x,y) = ∏_a s(xa,ya)` for incomparable `x,y` |
| `higmanVCCommon_conj_mapsCone` | Exact conjugation of a swap by any word whose boundary action replaces its two cone prefixes |
| `higmanVCTreeNF_mk_surjective` | Choose a free-group representative when applying the preceding theorem to an element of `Q` |
| `higSw_phi_gen`, `higSw_phi_append`, `higSw_phi_nil` | Prefix cloning and its composition law |
| `higSw_E_phi`, `higSw_phi_ker` | Boundary localization and preservation of the kernel |
| `higSw_central` | Every kernel element is central in `Q` |
| `higSw_phi_ker_indep`, `higSw_phi_ker_fixed` | All nonempty-prefix clones of a kernel element agree; iterated clones are fixed |
| `higSw_prod_forcing`, `higSw_prod_forcing_two` | The missing product identity implies `z^(d-1)=1`, and implies `z=1` when `d=2` |

These declarations are in `EnvelopeHigmanVCCommon{Split,Conj}.lean` and
`EnvelopeHigmanVCSwindle{Phi,Indep,Prod}.lean`, under
`GroupApproximation/BooneHigman/Metabelian/`.

The argument below would close injectivity of `E` for **binary** alphabet after
formalization. For general `d` it supplies only the stated `(d-1)` torsion bound.
It does not close the all-arities H1 statement or automatically supply a binary
replacement for every host used by the BH route.

## 1. The elementary shuffle and its exact commutation law

For a word `c`, define the following explicit finite word in `Q`:

```
P_c = ∏_{a < b in Fin d} s(a c b, b c a).
```

Use a fixed enumeration of the ordered pairs with `a < b`. All endpoints have
length `|c|+2`, and endpoints from different unordered pairs are distinct.
Consequently the swap factors have disjoint supports and commute in `Q`: the
defining conjugation relation, or `higmanVCCommon_conj_mapsCone`, gives exact
commutation when a swap fixes both cones of the other swap. This does not use
injectivity of `E`.

The boundary action of `P_c` sends `a c b ξ` to `b c a ξ`, fixes `a c a ξ`, and
fixes all other streams. Thus it exchanges the first and last letters around
the middle word `c`.

If `c,e` are incomparable, **`P_c P_e = P_e P_c` in `Q`**. Indeed, each endpoint
of a factor of `P_c` has the form `a c b`; each endpoint for `P_e` has the form
`a' e b'`. Distinct first letters make the endpoints incomparable. If the first
letters agree, comparability would force comparability of `c,e`, which is
excluded. Every factor of the first product therefore commutes with every
factor of the second. Moving the finitely many factors past one another proves
the displayed equality.

The explicit word is now `higSw_shuffleWord`, its quotient is `higSw_shuffle`,
and the exact commutation statement is checked as `higSw_shuffle_commute`.
The proof first checks endpoint incomparability and the defining conjugation
relator factor by factor, then takes both finite products.
`higSw_shuffle_mapsCone` now proves its boundary action, including equal outer
letters, by tracking the finite product of pair transpositions.
`higSw_shuffle_fix` proves that every cone `a e` with `e` incomparable to `c`
is fixed pointwise.

## 2. Coherent lifts of code shuffles

A complete code is a finite prefix antichain whose cones cover the boundary.
For such a code `C`, consider the boundary table

```
r_C : c a ξ ↦ a c ξ                    (c ∈ C, a ∈ A).
```

Both the source code `{ca}` and the target code `{ac}` are complete. We need an
**explicit coherent lift** `R_C ∈ Q`, not an arbitrary lift of this boundary
permutation.

Let `I(C)` be the finite set of proper prefixes of leaves of `C`. Order its
elements by decreasing length, breaking ties by a fixed lexicographic order,
and define

```
R_C = ∏_{c ∈ I(C), in that order} P_c.
```

In particular `R_{ {[]} } = 1`. If `C[c]` expands a leaf `c` to its `d` children,
then `I(C[c]) = I(C) ∪ {c}`. Every old internal node preceding the newly inserted
`c` in this order has length at least `|c|`. Such a node is incomparable with
`c`: it cannot be an ancestor of that length, and it cannot descend from the
leaf `c`. Section 1 therefore moves `P_c` past all these factors and proves the
exact expansion law

```
R_{C[c]} = P_c R_C.                                      (1)
```

This gives a lift depending only on the leaf set, independent of an expansion
history. No general equality between two arbitrary lifts is being inferred.

Its boundary action is `r_C`. Prove this by finite tree expansion from `{[]}`
using (1). On an expanded leaf, write an input as `c b a ξ`:

```
r_C(c b a ξ) = b c a ξ,
P_c(b c a ξ) = a c b ξ = r_{C[c]}(c b a ξ).
```

For `a=b` the middle map fixes the stream. On every other leaf `e` of `C`, the
image under `r_C` lies in a cone `a e`, disjoint from all the cones affected by
`P_c`. Thus `E(R_{C[c]}) = P_c E(R_C)` has exactly the required table.

This action update is now checked as `higSw_codeAction_expand`.
`higSw_codeAction_exists` inducts over the existing finite expansion-tree
predicate to produce a lift. It deliberately makes no claim that arbitrary
choices of these lifts satisfy the exact expansion law (1).

The algebraic insertion step is now `higSw_shuffle_insert`: an inserted
shuffle commutes past any preceding list of incomparable middle words.
The finite combinatorics still to prove in Lean are: completeness implies the
code is obtainable by leaf expansions; the proper-prefix set changes by exactly
`{c}`; and the ordered-product insertion just used. These are substantive
obligations, not consequences of kernel centrality.

For completeness, the first combinatorial assertion has a direct construction.
For any internal prefix `c` and any `a`, completeness supplies a leaf extending
`ca`, unless `ca` is already a leaf. A shorter leaf would be comparable with a
leaf extending `c`, contradicting the antichain property. The finite tree of
proper prefixes is therefore full. Expanding its internal nodes in increasing
depth order from the root produces exactly `C`.

## 3. The diagonal map and matched expansion compatibility

The product defining `Δ` is now the checked homomorphism `higSw_diag`.
`higSw_phi_letters_commute` derives commutation of the two generating swaps
from the defining conjugation relator; `higSw_phi_commute` extends it to
arbitrary elements by induction on both free-group representatives.
`higSw_diag_list_mul` proves the finite product rearrangement for a duplicate-free
list, supplying the multiplication law of `higSw_diag`. No injectivity of
boundary evaluation is used in these proofs.

Its boundary action is `a ξ ↦ a E(q)(ξ)` on the first-letter cone `a`,
as proved by `higSw_E_diag` using the existing localization-product API.
`higSw_diag_mapsCone` proves the corresponding cone transport, and
`higSw_diag_ker` proves preservation of the evaluation kernel. Preservation
does not assert pointwise fixedness of the kernel.
In particular, if `E(q)` maps cone `c` to `c'` preserving suffixes, the boundary
of `Δ(q)` maps `a c b` to `a c' b` for every pair `a,b`.

Apply `higmanVCCommon_conj_mapsCone` to each factor of `P_c`. Multiplicativity of
conjugation proves the exact identity

```
Δ(q) P_c Δ(q)⁻¹ = P_{c'}.                               (2)
```

Now suppose a prefix table for `E(q)` sends a complete code `C` to `D`, matches
`c` with `c'`, and an exact identity has already been proved:

```
R_D q = Δ(q) R_C.                                       (3)
```

Expand the matched leaves `c,c'`. Equations (1) and (2) yield

```
R_{D[c']} q = P_{c'} R_D q
            = P_{c'} Δ(q) R_C
            = Δ(q) P_c R_C
            = Δ(q) R_{C[c]}.
```

Thus exact naturality propagates under matched expansion. Equality of the
boundary actions is used only as the hypothesis of the already proved exact
conjugation theorem, never as a substitute for equality in `Q`.

Equation (2) is now checked as `higSw_diag_conj_shuffle`; the displayed
propagation step is `higSw_shuffle_expansion_naturality`. Instantiating them
with the canonical code lifts still requires constructing those lifts and
proving (1).

## 4. Seed naturality for a generator

Let `q=s(x,y)` for incomparable `x,y`. Choose a complete code `B` containing
`x,y` as leaves; the swap permutes this code, exchanging these two leaves and
fixing its other leaves. The boundary of `R_B` sends `xa` to `ax` and `ya` to
`ay`. Splitting and exact conjugation therefore give

```
R_B s(x,y) R_B⁻¹
  = ∏_a R_B s(xa,ya) R_B⁻¹
  = ∏_a s(ax,ay)
  = Δ(s(x,y)).                                         (4)
```

So (3) holds for this seed table `B→B`. It continues to hold for every source
code refining `B`, with the target obtained by applying the swap, because a
refinement of a finite full prefix tree is a finite sequence of leaf expansions
and Section 3 propagates (3) along that sequence.

Equation (4) is now `higSw_codeAction_conj_swap`; its equivalent form (3) is
`higSw_codeAction_swap_naturality`. Both accept any lift with the stated code
action and prove the equality in `Q` directly from its relators. This closes
the seed algebra, while the coherent refinement step still needs formalization.

The completeness and antichain lemmas for `higmanVCPivotY_complete {x,y} L`, with
`L=max |x| |y|`, already supply a suitable seed leaf set. The remaining new
combinatorial bridge is expansion reachability of arbitrary complete refinements.
It follows constructively by expanding exactly the extra internal nodes, in
increasing depth order. No monotonicity assertion about antichain subgroups is
needed.

Comparable pairs represent `1` by `higmanVCCommon_mk_comparable`. Inverse
generators equal generators by `higmanVCCommon_mk_inv_of`. These cases can be
discarded or handled separately when extracting a finite swap list.

## 5. Compatible tables for a whole word

Write a representative as `w=s_m ⋯ s_1`, and let `g_j=s_j ⋯ s_1`, with `g_0=1`.
For each `s_j` fix a seed code `B_j` from Section 4, and let `L_j` bound its leaf
lengths. Choose a depth `N_j` for each boundary permutation `E(g_j)`. A single
level `M` can be chosen so that, for every relevant index,

```
M ≥ N_j,        M ≥ N_{j-1} + L_j.
```

For each word `u` of length `M`, define `v_j(u)` by the unique suffix-preserving
cone image under `E(g_j)` and set `C_j={v_j(u) : |u|=M}`. The existing
`higmanVCCommon_hasDepth_len` gives

```
|v_{j-1}(u)| ≥ M - N_{j-1} ≥ L_j.
```

Each `C_j` is an antichain by `higmanVCCommon_incomp_image`, and is complete by
surjectivity of the boundary permutation. Each leaf of `C_{j-1}` consequently
extends a leaf of `B_j`: use completeness of `B_j` and the length bound. Hence
`C_{j-1}` refines `B_j`. The identities `g_j=s_j g_{j-1}` give a table for `s_j`
matching `v_{j-1}(u)` with `v_j(u)`. These assertions use `MapsCone.inv`,
`MapsCone.comp`, and `MapsCone.unique`.

Section 4 now supplies, for every step,

```
R_{C_j} s_j = Δ(s_j) R_{C_{j-1}}.
```

Multiplying these equalities telescopes to

```
R_{C_m} w = Δ(w) R_{C_0}.                              (5)
```

If `E(w)=1`, uniqueness of cone images says `v_m(u)=u=v_0(u)`. Thus
`C_m=C_0`, and (5) gives `Δ(w)=R_{C_0} w R_{C_0}⁻¹`. Kernel centrality gives
`Δ(w)=w`, exactly the missing product identity. The already proved
`higSw_prod_forcing_two` then eliminates the binary kernel.

This is a finite construction. It does not posit a single conjugator taking
every generator to its diagonal clone: the intermediate code shuffles vary
with the adapted tables, and only telescope to one conjugation for the word.

## Lean continuation inventory

Prefer the existing `Finset (List (Fin d))` code representation and
`higmanVCTreeNFWitPivot_IsAC`. The existing inductive proposition
`higmanVCLeafExp_IsTree` already describes expansion from `{[]}`;
`higmanVCLeafExp_expand` defines one-leaf expansion, and
`higmanVCLeafExp_tree_isAC` / `higmanVCLeafExp_expand_isAC` prove its antichain
properties. Add the missing completeness/refinement bridges around these
objects rather than importing the Leavitt-algebra notion of completeness.

Useful existing finite-code declarations are
`higmanVCPivotY_complete`, `higmanVCPivotY_subset_complete`,
`higmanVCPivotY_complete_isAC`, `higmanVCPivotY_complete_cover`,
`higmanVCCentral_words`, and `higmanVCCentral_mem_words_iff`.

The boundary API is in `GroupApproximation/BooneHigman/V/Group.lean`:
`MapsCone`, `MapsCone.unique`, `.append`, `.inv`, `.comp`, `.image_cone`,
`HasDepth`, `coneTarget`, `mapsCone_coneTarget`, `HasDepth.mono`, and
`HasDepth.mul`. The actual group supplies existence of a finite depth.
`higmanVCCommon_hasDepth_len` provides the quantitative bound needed above.
`vgen_mapsCone_coneSwap_fix` proves that a swap fixes disjoint cones.

Suggested dependency order for new proofs:

1. The explicit free-group word for `P_c`, incomparable-prefix commutation,
   boundary action and unchanged-cone support calculation are checked.
2. Prove finite full-tree/completeness/refinement bridges; define the canonical
  ordered internal-node product `R_C`; prove (1) and its boundary action.
   The boundary-action update and existence for expansion trees are already
   checked; canonical coherence is still required.
3. The homomorphism `Δ`, its cone transport and (2) are checked.
4. Equation (4) is checked. Use it and the checked matched-expansion propagation
   with coherent code lifts for all adapted generator tables.
5. Build the simultaneous deep tables and prove the telescope (5).
6. Prove the kernel product identity and use the existing binary forcing theorem.

The diagonal homomorphism, disjoint first-letter clone commutation, boundary
action and kernel preservation passed MSI Lean checks with only `propext`,
`Classical.choice` and `Quot.sound`. The elementary shuffle commutation,
conjugation, insertion and propagation theorems also passed these guards.
The boundary-action, support and code-action modules passed in 21.0, 21.0 and
16.7 seconds respectively on MSI, with the same allowed axiom closure.
The seed conjugation and naturality theorems passed in 25.0 seconds, also with
only these three axioms.
Canonical code shuffles and the fixed-kernel identity remain open. In particular,
`H_C ≤ H_{C[c]}` remains false, arbitrary choices of lifts do not establish (1),
and a group generated by involutions need not have exponent two. None of these
invalid shortcuts is used in the construction above.
