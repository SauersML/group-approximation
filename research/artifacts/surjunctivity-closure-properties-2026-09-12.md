# Closure properties of surjunctivity: commensurability, products, graph products, finite normal subgroups, quotients

Lane `gk-p-products`, 2026-09-12.

**Established claims supported:**
- `surjunctivity-is-a-commensurability-invariant`
- `products-with-lef-factors-preserve-surjunctivity`
- `separated-finite-normal-subgroups-preserve-surjunctivity`

**Open claims supported:**
- `finite-direct-products-of-surjunctive-groups-are-surjunctive`
- `graph-products-of-surjunctive-groups-are-surjunctive`
- `finite-normal-subgroups-do-not-affect-surjunctivity`
- `surjunctivity-passes-to-quotients`

## 0. Conventions and inputs

A cellular automaton over a group `Λ` has a finite alphabet `B`, a finite memory `M` and a local rule
`μ: B^M -> B`, with `τ(x)(λ) = μ((x(λm))_(m in M))`. It commutes with the left shifts
`(λ'.x)(λ) = x(λ'^-1 λ)`. `Λ` is *surjunctive* when, for every finite alphabet, every injective
automaton is surjective.

- **(F1)** Curtis–Hedlund–Lyndon holds over every group: a continuous self-map of `B^Λ` commuting with
  the left shifts is a cellular automaton.
- **(T)** Corollary 1 of `strict-pairs-transfer-to-table-realizations`: if every finite subset of a
  group embeds, as a partial multiplication table, into some surjunctive group, then the group is
  surjunctive.
- **(R)** `surjunctivity-is-axiomatized-by-rectangle-clauses`: subgroups, ultraproducts, local
  embeddings and directed colimits preserve surjunctivity.
- **(H)** `surjunctivity-passes-to-subgroups`.
- **(GF)** `graph-folds-over-surjunctive-groups-are-surjunctive`.

## 1. Theorem A: commensurability invariance

**Theorem A.** If `H <= G` has finite index and `H` is surjunctive, then `G` is surjunctive. Together
with (H): if `G_1` and `G_2` have isomorphic finite-index subgroups, `G_1` is surjunctive iff `G_2` is.

*Proof.* Write `G = H r_1 ⊔ ... ⊔ H r_n` as a union of right cosets, and define

```text
Φ: A^G -> (A^n)^H,   Φ(x)(h) = ( x(h r_1), ..., x(h r_n) ).
```

`Φ` is a homeomorphism. For `k in H`,

```text
Φ(k.x)(h) = ( x(k^-1 h r_i) )_i = Φ(x)(k^-1 h) = (k.Φ(x))(h),
```

so `Φ` intertwines the left `H`-shifts. An injective cellular automaton `τ` over `G` is continuous
and commutes with the `G`-shifts, in particular with the `H`-shifts. So `Φ τ Φ^-1` is a continuous,
`H`-equivariant, injective self-map of `(A^n)^H`. By (F1) it is a cellular automaton over `H` with the
finite alphabet `A^n`. Since `H` is surjunctive, it is surjective, and therefore so is `τ`.

For commensurable `G_1 ⊇ H_1 ≅ H_2 ⊆ G_2`: if `G_1` is surjunctive, then `H_1` is by (H), hence
`H_2`, hence `G_2` by the first part. QED

**Remark A.1 (the index must be finite).** For `[G:H]` infinite, the fibre alphabet `A^(H\G)` is
infinite. With a compact infinite alphabet `C = A^N`, the map `y(h) -> (a_0, y(h)_0, y(h)_1, ...)` is a
continuous, equivariant, injective map of `C^H` that is not onto, over every group. So Theorem A has no
infinite-index form through this device.

## 2. Theorem B: products with an LEF factor

**Theorem B.** Let `G` be surjunctive, and let `K` be LEF: every finite subset of `K` embeds, as a
partial multiplication table, into a finite group. Then `G x K` is surjunctive. In particular this holds
for every residually finite `K`.

*Proof.* Let `F` be a finite subset of `G x K` and `F_K` its projection to `K`. Choose a finite group
`L` and an injective map `ψ: F_K -> L` with `ψ(ab) = ψ(a)ψ(b)` whenever `a, b, ab` lie in `F_K`.

The map `id x ψ: F -> G x L` is injective. If `(g,k)(g',k')` lies in `F`, then `kk'` lies in `F_K`, so
the map preserves every product of `F` that lies in `F`. So `F` embeds as a partial multiplication table
into `G x L`.

`G x L` contains `G x {1}` with finite index `|L|`, so it is surjunctive by Theorem A. By (T), `G x K`
is surjunctive. QED

**Remarks.**
- **General form.** The same proof gives: `G x K` is surjunctive whenever every finite subset of `K`
  embeds as a partial table into some group `L` with `G x L` surjunctive.
- **Free products.** The free-product analogue with an LEF factor is the case `Γ = 1` of
  `free-centralizer-amalgams-are-surjunctivity-inert`, already landed.
- **Products of known surjunctive nonsofic groups.** Take Kun–Thom-type wreaths
  `W_1 = A wr_X G_1` and `W_2 = A wr_Y G_2` with residually finite lamps and residually finite bases.
  Their product is `(⊕_(X⊔Y) A) ⋊ (G_1 x G_2)`, the permutational wreath product of `A` over the
  `G_1 x G_2`-set `X ⊔ Y`. Its base is residually finite, so it is surjunctive by
  `rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`.

## 3. Products in general: equivalent forms (open)

**Proposition C.** Suppose surjunctivity is closed under binary direct products. Then:

- **(a)** it is closed under arbitrary unrestricted direct products;
- **(b)** graph products of surjunctive groups over any simplicial graph are surjunctive, and in
  particular free products are.

Conversely, (b) implies binary product closure: take the complete graph on two vertices. Moreover,
binary product closure holds iff the class of surjunctive groups is a quasivariety, meaning it is
axiomatized by quasi-identities `forall x (AND equations -> equation)`.

*Proof of (a).* Let `W = ∏_(i in I) G_i` with every `G_i` surjunctive, and let `F ⊆ W` be finite. For
each pair of distinct elements of `F`, choose a coordinate where they differ. Let `J` be the finite set
of those coordinates. The projection `p_J: W -> ∏_(i in J) G_i` is a homomorphism injective on `F`, and
the finite product is surjunctive by induction. By (T), `W` is surjunctive.

*Proof of (b).* First let `X` be a finite graph, and induct on its vertices. For a vertex `v`, with star
`st v` and link `lk v`, the graph product decomposes as the amalgam

```text
Γ(X) = Γ(st v) *_(Γ(lk v)) Γ(X∖v),     Γ(st v) = G_v x Γ(lk v).
```

Subgraph products embed, so both edge maps are injective. For every full subgraph `Y`, the retraction
`ρ_Y: Γ(X) -> Γ(Y)` that kills the vertex groups outside `Y` is a homomorphism restricting to the
identity on `Γ(Y)`. So

```text
f = (ρ_(st v), ρ_(X∖v)): Γ(X) -> Γ(st v) x Γ(X∖v)
```

is injective on both vertex groups of the amalgam. The target is surjunctive:
- `Γ(lk v)` and `Γ(X∖v)` by induction;
- `Γ(st v)` by product closure;
- the product of the two by product closure again.

(GF) then makes `Γ(X)` surjunctive. For an infinite graph, `Γ(X)` is the directed union of `Γ(Y)` over
finite full subgraphs `Y`, and (R) passes surjunctivity to the union.

*Quasivariety form.* The surjunctive class contains the trivial group. It is closed under isomorphic
copies, subgroups and ultraproducts by (R). By Mal'cev's characterization of quasivarieties, a class of
algebras containing the trivial algebra is a quasivariety exactly when it is also closed under direct
products. Closure under all products follows from binary closure by (a). QED

**Where the general product problem stops.**
- **Coset transplant along one factor.** Transplanting an injective automaton over `G x K` to coset
  spaces needs a family of subgroups separating finite sets. Using `G_0 x {1}` with `G_0` of infinite
  index gives infinite fibre alphabets, and Remark A.1 kills those. Using `G_0` of finite index needs
  `G` residually finite, which is Theorem B's case.
- **Table transfer.** Rectangle clauses have disjunctive conclusions. The reverse inequality of a strict
  certificate on `G x K` can use both coordinates at once, so neither factor inherits a certificate
  (remark (d) of `gottschalk-rectangle-clauses-and-recognition-2026-09-12.md`).
- **Counting.** A Gromov–Weiss count in one factor needs Følner or sofic structure in that factor and
  finitely many rows in the other.
- **Self-copies.** The tester host contains `U x U`, so at `U` product closure is automatic and gives
  nothing new.

## 4. Theorem D: separated finite normal subgroups

**Theorem D.** Let `N` be a finite normal subgroup of `E`. Suppose some finite-index subgroup
`E_0 <= E` meets `N` trivially; equivalently, `N` injects into some finite quotient of `E`. Then `E` is
surjunctive iff `E/N` is surjunctive.

*Proof.* Since `E_0 ∩ N = 1`, the quotient map restricts to an isomorphism `E_0 -> E_0N/N`. Its image
has finite index in `E/N`.
- If `E/N` is surjunctive, then `E_0` is surjunctive by (H), and `E ⊇ E_0` is surjunctive by Theorem A.
- If `E` is surjunctive, then `E_0` is by (H), and `E/N ⊇ E_0N/N ≅ E_0` is by Theorem A.

For the equivalence of hypotheses: the kernel of a finite quotient injective on `N` is a finite-index
subgroup meeting `N` trivially; conversely, the normal core of `E_0` is one. QED

**Corollary D.1.** Every virtually split finite central extension of a surjunctive group is surjunctive.
For a finite central extension `1 -> Z -> E -> Q -> 1` whose center `Z` injects into a finite quotient of
`E`, surjunctivity of `E` and of `Q` agree.

**The residue (open).** Theorem D does not apply to finite normal subgroups in the finite residual of
`E`. First test instance: Deligne's triple cover of `Sp_4(Z)`. By
`deligne-triple-cover-finite-residual-is-center`, its finite residual is its center of order three,
while the quotient `Sp_4(Z)` is residually finite and hence surjunctive. No surjunctivity proof for the
triple cover is recorded.

**Where it stops.**
- **Table transfer through the quotient certifies nothing.** Reverse inequalities are never certified
  through a surjunctive quotient (corollary 2 of `strict-pairs-transfer-to-table-realizations`, and
  `surjunctivity-recognition-dichotomy`). Dually, a strict pair over `E/N` does not lift, since lifting
  forward coincidences creates none.
- **Twisted shifts.** A set-theoretic section `E/N -> E` identifies `A^E` with `(A^N)^(E/N)`. The
  `E`-action becomes a shift over `E/N` twisted by a cocycle into the finite group `N`, acting on the
  fibre alphabet. (F1) applies to plain shifts, and the twist is plain exactly over finite-index
  subgroups on which the extension splits, which is Theorem D's hypothesis.
- **Linear case.** For central `N` and `p ∤ |N|`, `F_p[E]` splits along the characters of `N` into
  twisted group algebras `F_p^c[Q]`. Stable finiteness of `F_p[Q]` does not imply stable finiteness of
  the twisted summands.

## 5. Quotients

**Proposition E.** Surjunctivity passes to all quotients iff Gottschalk's conjecture holds.

*Proof.* Every group is a quotient of a free group. Free groups are residually finite, hence surjunctive
(`residually-finite-groups-are-surjunctive`), so quotient closure gives the conjecture. The converse is
trivial. QED

So "surjunctivity passes to quotients" is exactly as hard as the conjecture. By Theorem D, quotients by
separated finite normal subgroups are harmless. What remains open is finite normal subgroups in finite
residuals, and infinite normal subgroups.
