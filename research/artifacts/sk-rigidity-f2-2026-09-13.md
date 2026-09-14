# Standardness of EL_3 isomorphisms over F_2: what is left to prove

Lane sk-rigidity-f2, 2026-09-13. Everything here is UNREVIEWED; review is queued with sk-verify-5.

Target (open node `subshift-el3-isomorphisms-are-standard-over-f2`): is every isomorphism
`α: EL_3(R_X) → EL_3(R_Y)` standard? With `cantor-crossed-product-matrix-ring-iso-forces-soe` (sk-rigidity-ring)
a yes settles the note's question Q3 in its strong-orbit-equivalence form.

Notation. `X, Y` infinite minimal subshifts, `A = LC(X,F_2)`, `R = R_X = A ⋊_T Z`, `G = EL_3(R)`, and
`A_ij = {e_ij(r) : r ∈ R}` the six root subgroups. All rings are unital associative. `C_G(S)` is a centralizer.

## 1. What this lane adds

- **Theorem 1 (§3).** Each `A_ij` is bicommutant closed: `C_G(C_G(A_ij)) = A_ij`.
- **Theorem 2 (§4), the main one.** If `α` carries the six root subgroups of `G_X` onto the six root subgroups of
  `G_Y`, then there is a ring isomorphism `ψ: R_X → R_Y` with `α(e_ij(r)) = e_ij(a_i ψ(r) a_j^{-1})` after an inner
  and a graph correction. So `R_X ≅ R_Y`, and `X`, `Y` are strongly orbit equivalent.
  The proof needs `R_Y` to be **directly finite**, which is exactly what the note's finite models give.
- **Firewall FW-MAXAB and the reformulation (§5).** The root subgroups are not maximal abelian: the six "row" and
  "column" subgroups `Row_i`, `Col_j` are abelian and self-centralizing, and `A_ij = Row_i ∩ Col_j`. So "maximal
  abelian and bicommutant closed" does not pick out root subgroups, but it does reduce the whole problem to one
  statement about a single group: **(†) every maximal abelian bicommutant-closed subgroup of `G` is conjugate to a
  `Row_i` or a `Col_j`**, plus an alignment step for the intersection pattern.
- §6 records the literature check and why `n = 3` in characteristic 2 is the exceptional zone.

## 2. Preliminaries used

- `Z(R) = F_2`. Let `c = Σ_j c_j u^j` be central. For clopen `V`, `e_V c − c e_V = Σ_j c_j(e_V − e_{T^jV})u^j = 0`.
  If `x ∈ supp c_j` with `j ≠ 0`, then `x ≠ T^{-j}x` because `T` has no periodic points, so a clopen `V` containing
  `x` but not `T^{-j}x` gives `c_j(x) = 0`, a contradiction. So `c = c_0 ∈ A`, and `u c u^{-1} = c` makes `c_0`
  `T`-invariant, so constant by minimality.
- **`R` is directly finite** (`ab = 1 ⟹ ba = 1`). By `minimal-subshift-algebra-is-simple-lef-ring`, `R` is a LEF
  ring, so it embeds unitally in an ultraproduct `∏_ω M_{N_ℓ}(F_2)`. Each `M_N(F_2)` is directly finite, direct
  finiteness is a first-order condition preserved by ultraproducts, and it passes to unital subrings.
- Permutation matrices lie in `G`: over `F_2`, `e_12(1)e_21(1)e_12(1)` is the transposition matrix, so every
  permutation matrix is a product of elementary matrices.
- `R` has an anti-automorphism `τ(Σ_j f_j u^j) = Σ_j u^{-j} f_j`, so `g ↦ (τ(g)^t)^{-1}` is an automorphism of `G`
  (the graph automorphism); it sends `A_ij` to `A_ji`.

## 3. Theorem 1: root subgroups are bicommutant closed

**Lemma 1.1.** `C_{GL_3(R)}(A_12) = {g : g_11 = g_22 = 1, g_21 = g_31 = g_23 = 0}`.

*Proof.* `g` centralizes `A_12` iff `g·rE_12 = rE_12·g` for every `r ∈ R`. Now
`(g·rE_12)_{pq} = g_{p1} r` when `q = 2` and `0` otherwise, while `(rE_12·g)_{pq} = r g_{2q}` when `p = 1` and `0`
otherwise. Comparing entries for all `r`:
- `(2,2)` and `(3,2)` give `g_21 r = g_31 r = 0`, so with `r = 1`, `g_21 = g_31 = 0`;
- `(1,3)` gives `r g_23 = 0`, so `g_23 = 0`;
- `(1,2)` gives `g_11 r = r g_22`; with `r = 1`, `g_11 = g_22 =: c`, and then `c ∈ Z(R) = F_2`.

If `c = 0` the first column of `g` is zero, contradicting invertibility, so `c = 1`. The converse is the same
computation read backwards. ∎

The same computation with the indices permuted gives
`C_{GL_3(R)}(A_13) = {g_11 = g_33 = 1, g_21 = g_31 = g_32 = 0}` and
`C_{GL_3(R)}(A_32) = {g_22 = g_33 = 1, g_13 = g_23 = g_21 = 0}`.

**Theorem 1.** `C_G(C_G(A_12)) = A_12`, and likewise for every `A_ij`.

*Proof.* `A_12`, `A_13` and `A_32` all satisfy the conditions of Lemma 1.1, so all three lie in `C_G(A_12)`. Hence
`C_G(C_G(A_12)) ⊆ C_G(A_12) ∩ C_G(A_13) ∩ C_G(A_32)`. Intersecting the three displayed conditions leaves
`g_21 = g_31 = g_23 = g_32 = g_13 = 0` and `g_11 = g_22 = g_33 = 1`, that is `g = e_12(g_12) ∈ A_12`. The reverse
inclusion is trivial. Permuting indices and applying the graph automorphism gives the other five. ∎

## 4. Theorem 2: root preservation gives a ring isomorphism

**Lemma 4.1 (the commuting hexagon).** `A_ij` and `A_kl` commute iff `j ≠ k` and `l ≠ i`. So the commuting graph on
the six root subgroups is a hexagon `A_32 – A_12 – A_13 – A_23 – A_21 – A_31 – A_32`, and `Aut` of that graph has
order 12. Conjugation by permutation matrices realizes the `S_3` relabelling `A_ij ↦ A_{σ(i)σ(j)}`, which is simply
transitive on the six subgroups; the graph automorphism realizes `A_ij ↦ A_ji`, which is not of that form. So all 12
hexagon automorphisms are realized by automorphisms of `G`.

**Theorem 2.** Let `R`, `S` be unital rings with `S` directly finite, and let `α: E_3(R) → E_3(S)` be an isomorphism
with `α(A_ij(R)) = A_ij(S)` for all `i ≠ j`. Then there is a ring isomorphism `ψ: R → S` and a unit `a ∈ S^×` with
`α(e_12(r)) = e_12(aψ(r))`. In particular `R ≅ S`.

*Proof.* Since `e_ij(r+s) = e_ij(r)e_ij(s)`, the maps `φ_ij: R → S` defined by `α(e_ij(r)) = e_ij(φ_ij(r))` are
additive bijections. Applying `α` to `[e_ik(r), e_kj(s)] = e_ij(rs)` for distinct `i, j, k` gives

  (∗) `φ_ij(rs) = φ_ik(r) φ_kj(s)` for all `r, s ∈ R`.

Put `a = φ_12(1)` and `b = φ_23(1)`. Taking `(i,j,k) = (1,3,2)` in (∗):
- `s = 1`: `φ_13(r) = φ_12(r) b`, and `φ_13` is onto, so `S = Sb`;
- `r = 1`: `φ_13(s) = a φ_23(s)`, and `φ_13` is onto, so `S = aS`.

So `b` has a left inverse and `a` has a right inverse, and direct finiteness of `S` makes both two-sided:
`a, b ∈ S^×`. Substituting `φ_23(s) = a^{-1}φ_13(s) = a^{-1}φ_12(s)b` into (∗) for `(1,3,2)`,

  `φ_12(rs) b = φ_13(rs) = φ_12(r) φ_23(s) = φ_12(r) a^{-1} φ_12(s) b`,

and cancelling the unit `b` gives `φ_12(rs) = φ_12(r) a^{-1} φ_12(s)`. Set `ψ(r) = a^{-1}φ_12(r)`. Then `ψ` is
additive and bijective, `ψ(1) = 1`, and `ψ(rs) = a^{-1}φ_12(r)a^{-1}φ_12(s) = ψ(r)ψ(s)`. ∎

**Corollary 2.1.** Let `α: G_X → G_Y` be an isomorphism carrying the set of six standard root subgroups of `G_X`
onto the set of six standard root subgroups of `G_Y`. Then `R_X ≅ R_Y`, and `X` and `Y` are strongly orbit
equivalent.

*Proof.* `α` induces an automorphism of the commuting hexagon, so by Lemma 4.1 we may compose `α` with conjugation
by a permutation matrix and, if needed, with the graph automorphism of `G_Y`, and assume `α(A_ij) = A_ij` for every
pair. `R_Y` is directly finite by §2, so Theorem 2 gives `R_X ≅ R_Y`. Then
`cantor-crossed-product-matrix-ring-iso-forces-soe` with `m = 1` gives strong orbit equivalence. ∎

Two remarks on Corollary 2.1.
- It gives strong orbit equivalence, not flip conjugacy: `ψ` need not carry `LC(X,F_2)` onto `LC(Y,F_2)`. That is
  the Cartan-uniqueness question owned by sk-rigidity-cartan, and it is also firewall F1 of
  sk-rigidity-intrinsic.
- Direct finiteness is the only analytic input, and the note proves it: the finite models of Theorem 1 of the
  manuscript are exactly what makes one-sided inverses two-sided. Without it, `a` and `b` are only one-sided
  invertible and the argument breaks.

## 5. FW-MAXAB: root subgroups are not maximal abelian

For `1 ≤ i ≤ 3` write `Row_i = {I + Σ_{j≠i} E_ij b_j : b_j ∈ R}` and `Col_j = {I + Σ_{i≠j} E_ij b_i : b_i ∈ R}`.
Each is a product of the two root subgroups it contains, so `Row_1 = A_12 A_13` and `Col_2 = A_12 A_32`.

**Lemma 5.1.** Every `Row_i` and every `Col_j` is abelian and self-centralizing in `G`.

*Proof.* For `Row_1`, `(E_12 b + E_13 c)(E_12 b' + E_13 c') = 0` because `E_1j E_1k = 0`, so `Row_1` is abelian, and
by Lemma 1.1 and its `A_13` analogue `C_G(Row_1) = C_G(A_12) ∩ C_G(A_13)` is cut out by
`g_21 = g_31 = g_23 = g_32 = 0` and `g_11 = g_22 = g_33 = 1`, which is `Row_1`. For `Col_2`,
`C_G(A_12) ∩ C_G(A_32)` is cut out by `g_21 = g_31 = g_23 = g_13 = 0` and `g_11 = g_22 = g_33 = 1`, which is
`Col_2`. The other four follow by permuting indices. ∎

So each `Row_i` and `Col_j` is a maximal abelian subgroup, is bicommutant closed, and properly contains two root
subgroups. Consequence: the maximal members of the family of bicommutant-closed abelian subgroups are not the root
subgroups, so that lattice-theoretic characterization fails. This complements firewall F-EA of
`subshift-el3-isomorphisms-are-standard-over-f2`, which rules out picking the unipotent radicals out by maximal
elementary abelian 2-subgroups.

**Lemma 5.2.** `A_ij = Row_i ∩ Col_j`, and these six intersections are exactly the root subgroups.

*Proof.* An element of `Row_i` has its off-diagonal entries in row `i`, an element of `Col_j` has them in column
`j`, and the two conditions together leave only the `(i,j)` entry. ∎

So root-subgroup preservation, which by Theorem 2 is the whole problem, follows from:

  (†) every maximal abelian bicommutant-closed subgroup of `G` is conjugate in `G` to some `Row_i` or `Col_j`.

The words "conjugate in `G`" are needed: `gRow_1g^{-1}` is again abelian and self-centralizing and is not one of the
six. A first version of this artifact stated (†) without them and was wrong.

(†) is a statement about one group, with no reference to a second subshift, so it is a better target than
standardness itself. It is not proved here, and it does not by itself finish the job: from (†) one still has to
show that an isomorphism matches up the intersection pattern, that is, that the root subgroups are recovered as the
intersections `Row_i ∩ Col_j` inside the class rather than as intersections of unrelated conjugates. That alignment
step was not verified by this lane.

## 6. Literature check (bounded: three web searches, one secondary source read)

`arXiv:2307.12920` (Bunina–Vladykina), introduction, quoted verbatim from the arXiv HTML on 2026-09-13:
- "Isomorphisms of the groups `GL_n(R)` and `GL_m(S)` over arbitrary associative rings with 1/2 for `n,m ⩾ 3` were
  described in 1981 by I.Z. Golubchik and A.V. Mikhalev [23]";
- "In 1997 I.Z Golubchik [24] described isomorphisms between these groups for `n,m ⩾ 4`, but over arbitrary
  associative rings with 1.";
- "If `n = 3`, automorphisms of given linear groups are not always standard. They are standard either if in a ring
  `2` is invertible, or if a ring is a domain, or it is a semisimple ring." (their [30], Petechuk 1982).

`R_X` has `2 = 0`, is not a domain (it has idempotents `e_V`) and is not semisimple (it is simple but not
Artinian), so `n = 3` here sits precisely in the exceptional zone. This independently confirms firewalls F-PET and
the Golubchik entry already recorded by sk-rigidity-ring; note the year discrepancy (their Attempts say Golubchik
1992, Contemp. Math. 131; the Bunina–Vladykina introduction says 1997, reference [24]). Neither primary was read by
this lane, so neither is landed as a citation route.

**Scope warning for any future use of Golubchik.** It is stated for `GL_n`, and `EL_3(R_X) ≠ GL_3(R_X)` because
`K_1(R_X) ≅ Z` (firewall F-GL). Any `n ≥ 4` statement for the note's groups needs a version for subgroups between
`E_n` and `GL_n`, which this lane did not verify.

## 7. Status and next target

- Theorem 1, Lemma 5.1 and Theorem 2 have complete proofs above and are UNREVIEWED.
- The open node stays open. What remains is exactly: **an isomorphism `EL_3(R_X) → EL_3(R_Y)` carries root
  subgroups to root subgroups.**
- Sharpest next target: characterize `A_12` inside `G` from the pair `(A_12, C_G(A_12))`, for instance as an
  intersection of maximal abelian bicommutant-closed subgroups, or through the three-element trick of
  sk-rigidity-ring §3. Failing that, look for a non-standard automorphism of `EL_3(R_X)`: §5 shows the usual
  lattice obstructions are live, and a counterexample would settle the node negatively.
