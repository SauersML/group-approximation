---
rg: 2
id: strong-atiyah-simple-kazhdan-atoms-proof
kind: route
title: Normal intersections, fixed vertices, one colimit stage and one projection keep a simple FA group out of every closure; Titz Mite--Witzel lattices are such atoms
target: strong-atiyah-permanence-closure-omits-simple-kazhdan-groups
requires:
  - property-t-implies-property-fa
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
  - two-generator-fp-torsion-free-universal-whitehead-container
---

Standard facts used without proof:
- Bass--Serre theory (Serre, *Trees*, Chapter I);
- directed colimits of groups are computed on underlying sets;
- property (T) passes to finite-index subgroups, and an amenable Kazhdan group
  is finite (Bekka--de la Harpe--Valette);
- Strong Atiyah over a field `K` passes to subgroups: for `H <= G` and a
  matrix `A` over `K[H]`, `rk_(N(H))(A) = rk_(N(G))(A)`.

## 0. Why this, and how it is checked

- **Why it succeeds where the T-closure stopped.**  The invariant of
  `atiyah-permanence-closure-kazhdan-subgroups-are-rf` ("every Kazhdan subgroup
  is residually finite") is lost under central extensions: `Lambda_n` is a
  non-residually-finite extension of residually finite pieces.  The invariant
  used here ("no subgroup isomorphic to `S`") cannot be lost by building a
  group from pieces.  A simple group meets a normal subgroup trivially or
  entirely; an FA group sits in one vertex group; a finitely presented group
  enters a colimit or limit at a finite stage.  The only operation that creates
  `S` is taking quotients, and Strong Atiyah is not proved by quotients.
- **First falsifiable step.**  Check that `Lambda_n` contains no copy of `S`.
  If `S <= Lambda_n`, then `S ∩ Z = 1`, since `S` is not abelian and `S ∩ Z` is
  normal in `S`.  So `S` embeds in the residually finite `Gamma'`, which is
  impossible for an infinite simple group.  This separates the new invariant
  from the T-invariant at the recorded sharpness example.
- **Calibration.**
  - Congruence Kazhdan groups are in `A(RF)`, so property (T) forces nothing.
  - The Burger--Mozes simple lattices are finitely presented, simple and
    torsion-free, but lack FA.  They lie in `A(LI)` through (O4), so FA is
    needed.
  - Every group with recorded Strong Atiyah lies in `A(Y_0)` (Section 3).  A
    closure argument that excluded one of these groups would be false.

## 1. Closure lemma

Let `S` be infinite, finitely presented, simple, with FA.  Put
`Sim_S = {G : no subgroup of G is isomorphic to S}`.

**Lemma 0.**  Every homomorphism `phi: S -> G` is injective or trivial, because
`ker phi` is normal in `S`.

**(O1)** is immediate.

**(O2) Directed colimits.**
- *Setup.*  Let `(G_i, phi_ij)` be a directed system in `Sim_S` with colimit
  `G` and canonical maps `phi_i`.  Suppose `iota: S -> G` is injective.
- *Lift the generators.*  Fix a presentation
  `S = <s_1, ..., s_k | r_1, ..., r_m>` with every `s_a != 1`.  Each
  `iota(s_a)` is the image of some element of some `G_(i_a)`.  By
  directedness there are one index `i` and elements `g_a` in `G_i` with
  `phi_i(g_a) = iota(s_a)`.
- *Kill the relators at one stage.*  For each `b`, `r_b(g_1, ..., g_k)` maps
  to `1` in `G`.  Colimits are computed on sets, so it already maps to `1` in
  some `G_(j_b)`.  Choose `j >= i, j_1, ..., j_m`.
- *Conclude.*  `s_a -> phi_ij(g_a)` defines `psi: S -> G_j` with
  `phi_j ∘ psi = iota`.  Since `iota` is injective, so is `psi`, and
  `G_j ∉ Sim_S`.

**(O3) Extensions.**  Let `N ⊴ G` and `iota: S -> G` be injective.
- `iota(S) ∩ N` is normal in `iota(S)`, so it is `1` or `iota(S)`.
- In the second case `S` embeds in `N`.
- In the first case `S -> G -> G/N` is injective.

So if `N` and `G/N` are in `Sim_S`, so is `G`.

**(O4) Graphs of groups.**  Let `G = pi_1(𝔾)` act on its Bass--Serre tree,
without inversions.  Vertex stabilizers are the conjugates `g G_v g^-1` of
vertex groups.  `iota(S)` has FA, so it fixes a vertex, and
`g^-1 iota(S) g <= G_v`.  Edge groups and edge maps play no role.

**(O5) Subdirect products.**  Let `pi_i: G -> G_i` with `∩ ker pi_i = 1`, every
`G_i` in `Sim_S`, and `iota: S -> G` injective.
- `iota(S) != 1`, so some `pi_i ∘ iota` is nontrivial.
- By Lemma 0 that map is injective, so `S` embeds in `G_i`.

Restricted and unrestricted products and residual systems are special cases.
For the wreath product `A wr B = (⊕_B A) ⋊ B`, the base `⊕_B A` is a subgroup
of `∏_B A`, so it lies in `Sim_S` by (O5) and (O1); then apply (O3).

**(O6) Marked limits and local embeddability.**
- *Marked limits.*  Let `(G_n, x^(n)) -> (G, x)` in the space of `d`-generated
  marked groups, with every `G_n` in `Sim_S` and `iota: S -> G` injective.
  - Choose words `w_a` in `F_d` with `w_a(x) = iota(s_a)`.
  - The finitely many words `r_b(w_1, ..., w_k)` are relations of `(G, x)`.
    The word `w_1` is not.
  - By the definition of the topology, for all large `n` the relations hold
    in `G_n` and `w_1(x^(n)) != 1`.
  - So `s_a -> w_a(x^(n))` defines a nontrivial `psi_n: S -> G_n`, which is
    injective by Lemma 0.  (This is the argument of `fp-simple-groups-are-isolated`.)
- *Local embeddability.*  Suppose `G` is locally embeddable into `Sim_S` and
  `iota: S -> G` is injective.
  - Let `F` be the finite subset of `iota(S)` consisting of `1`, the elements
    `iota(s_a)` and the images of all prefixes of the relators.
  - A local embedding `theta: F -> H` with `H` in `Sim_S` is multiplicative
    on `F`.  So `theta(iota(r_b)) = 1` for every `b`.
  - `theta` is injective on `F`, so `theta(iota(s_1)) != 1`.
  - So `s_a -> theta(iota(s_a))` defines a nontrivial, hence injective,
    homomorphism `S -> H`.

**Item 1 (atomicity).**  Suppose no group of `Y` contains `S`.  Then
`Y ⊆ Sim_S`.  `Sim_S` is closed under (O1)--(O6), so `A(Y) ⊆ Sim_S`.
Contrapositive: if a group of `A(Y)` contains `S`, some group of `Y` does.  `∎`

## 2. The atoms

Let `S = Gamma^_i^q`.  By `titz-witzel-simple-kazhdan-cat0-lattices-exist`,
`Gamma_i^q` is finitely presented, torsion-free, of type F and Kazhdan, and
`S` is a simple subgroup of finite index.
- `S` is finitely presented (Reidemeister--Schreier) and torsion-free.
- `S` has (T), since it has finite index, and so FA by
  `property-t-implies-property-fa`.
- `S` is infinite (finite index in an infinite group), so it is not amenable:
  an amenable Kazhdan group is finite.
- `S` is not residually finite: an infinite simple group has no proper
  finite-index normal subgroup.
- `S` is not locally indicable: it is finitely generated, nontrivial and
  perfect, so it has no surjection onto `Z`.

The classes of amenable, residually finite and locally indicable groups are
closed under subgroups.  So none of their members contains `S`, and
`Y_0 = amenable ∪ RF ∪ LI ⊆ Sim_S`.  By item 1, `A(Y_0) ⊆ Sim_S`.

The Deligne lattice `Lambda_n` is a central extension of `Z` by the residually
finite `Gamma'`, so it is in `A(Y_0)` by (O3).  Any class `Y ⊆ Sim_S` may be
added to the base without changing the conclusion.

## 3. Every recorded Strong Atiyah class lies in `A(Y_0)`

| node | group | why in `A(Y_0)` |
|---|---|---|
| `elementary-amenable-torsion-free-strong-atiyah` | torsion-free elementary amenable | amenable |
| `p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah` | subgroups of compact `p`-adic analytic | RF |
| `congruence-kazhdan-groups-satisfy-strong-atiyah` | `Gamma(3)`, `E_3(3)` | RF |
| `raag-out-and-mapping-class-virtually-strong-atiyah` | finite-index subgroups of `Out(A_Gamma)`, `MCG` | RF |
| `one-relator-groups-satisfy-strong-atiyah` | torsion-free one-relator groups | LI (Brodskii--Howie) |
| `strong-atiyah-passes-to-locally-indicable-extensions`, `atiyah-passes-to-torsion-free-elementary-amenable-extensions` | extensions | (O3) |
| `tree-by-elliptic-lattices-satisfy-strong-atiyah` | locally free normal subgroup, abelian quotient | LI by amenable, (O3) |
| `two-variable-kun-thom-actor-satisfies-strong-atiyah` | `K ⋊ Gamma_2(p)` | RF |
| `one-compressor-support-atiyah-reduces-to-base`, `double-ascending-hnn-strong-atiyah-reduces-to-kernel-tree` | ascending HNN extensions of a base | (O4) |
| `algebraic-atiyah-with-determinant-closed-under-colimits` | colimits | (O2) |

- Linnell's class `C` is the closure of free and elementary amenable groups
  under directed unions (O2) and extensions with elementary amenable quotient
  (O3).  So it is in
  `A(Y_0)`.
- The virtually compact special, 3-manifold and braid groups are residually
  finite.

## 4. The master host and the gate

- **The master host contains `S`.**
  `two-generator-fp-torsion-free-universal-whitehead-container` embeds every
  finitely presented torsion-free group in `E`, in particular `S`.  The same
  holds for any group containing all finitely presented torsion-free groups.
  So for every `Y ⊆ Sim_S`, `E ∉ A(Y)` by item 1, which gives item 3.  The
  listed permanences are instances of (O2)--(O6), and `Lambda_n` is in `Sim_S`
  (Section 2).
- **The gate.**  Consider a proof of `SA(E)` that applies (O1)--(O6) to base
  groups for which Strong Atiyah is proved otherwise.
  - By item 1 some base group `B` contains `S`.
  - By subgroup permanence, `SA(B)` gives `SA(S)`.
  - `SA(S)` also follows from `SA(E)`, and from the root over `Qbar`.
  - So `titz-witzel-simple-lattices-satisfy-strong-atiyah` is necessary, and
    any proof must reach it by a method that is not (O1)--(O6) from `S`-free
    groups.
- **Quotients.**  Permanence of Strong Atiyah over `K` to torsion-free
  quotients implies the conjecture over `K`.  Every countable torsion-free
  group is a quotient of a free group, and free groups satisfy Strong Atiyah
  (they lie in class `C`).  So the one operation outside (O1)--(O6) that
  creates `S` from pieces is equivalent to the conjecture itself.  `∎`

## 5. Direct methods at the atom

Each statement below is a property of `S`, followed by the recorded method it
removes.
- **No proper finite-index subgroup.**  A finite-index subgroup contains a
  finite-index normal subgroup, which is `1` or `S`; `S` is infinite.  This
  also rules out finite quotients.  Removed: Lück approximation along a normal
  chain, pro-`p` completions and Iwasawa algebras (the `p`-adic method),
  congruence arguments, and passing to a virtually special finite-index
  subgroup.
- **No proper nontrivial normal subgroup.**  Removed: the Linnell--Schick
  crossed-product induction `K[N] * G/N` and locally indicable extension
  permanence, which apply to `S` only through `N = S` or `N = 1`.
- **Perfect.**  Removed: Hughes-free division rings and the locally indicable
  uniqueness arguments.
- **FA.**  Removed: every Bass--Serre reduction, including the Cohn coproduct
  route `atiyah-amalgam-rank-from-cohn-coproduct` and the compressor-tree
  reductions.
- **Isolated** (`fp-simple-groups-are-isolated`).  Removed: approximation of
  `S` by other marked groups.

What remains:
- approximations not by groups, such as sofic ones (`titz-witzel-kernel-sofic`
  and its negation are both OPEN);
- geometric arguments on the exotic `C~_2` building;
- ring-theoretic arguments inside `Qbar[S]`.

Soficity would give the determinant conjecture and approximation of ranks, but
no integrality theorem for sofic groups is recorded.
