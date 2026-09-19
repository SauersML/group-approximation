---
rg: 2
id: fibred-ore-rank-comparison-is-local-indicability
kind: claim
title: For a group G with an epimorphism phi onto Z, the von Neumann rank dominates the Alexander rank rank_{Q(t)} phi(A) on all matrices exactly when G is locally indicable, and then already on the kernel; so in a fibred cd-2 amenable counterexample every Ore or Folner rank comparison over Q[L] x| <t> fails on constant-in-t Fox matrices of a finitely generated rationally perfect subgroup of the fibre, and the Alexander inequality rk H_2(L) <= rk H_1(L) needs amenability, cd 2 and projectivity at once
distinct_from:
  flat-weak-bass-holds-exactly-for-locally-indicable-groups: that compares the von Neumann rank with the augmentation rank; this compares it with the Alexander rank over Q(t) through an epimorphism onto Z, the rank the fibred step of the brief needs, and locates the failure in the fibre, where t plays no role
  cd-two-z-kernels-have-zero-or-free-alexander-h2: that reduces the fibred type (II) to rk_Lambda H_2(L) <= rk_Lambda H_1(L); this shows that no matrix-level Ore, Folner or specialization argument over Q[L] x| <t> proves that inequality, and that the inequality fails for amenable fibred groups of infinite cd and for non-amenable fibred groups of cd 2 whose rank comparison holds
  l2-finite-projectives-over-amenable-groups-satisfy-weak-bass: that is the open module inequality; this shows that its Alexander form for Gamma = Z is not easier and is equivalent to it on the relation module
---

**ESTABLISHED** (proposed; referee pending) through
`fibred-ore-rank-comparison-is-local-indicability-proof`, from
`flat-weak-bass-holds-exactly-for-locally-indicable-groups` (item 1, (ii) ⇔ (i), and its
recalled imports: universality of the Hughes-free division ring for locally indicable groups,
Jaikin-Zapirain 2021, and `D(G)` Hughes-free, Jaikin-Zapirain–López-Álvarez 2020),
`amenable-cd-two-kropholler-iff-locally-indicable` (amenable locally indicable groups of cd
`<= 2` are solvable: `1`, `Z`, a subgroup of `Q`, or `BS(1,m)`), and
`cd-two-z-kernels-have-zero-or-free-alexander-h2` (items 1, 2, 4). Recalled imports: Stallings–
Swan; Fox calculus; Lück's induction formula for `dim_U`.

**Notation.** `G` is a group, `φ : G ↠ Z = ⟨t⟩`, `L = ker φ`, `Λ = Q[t^{±1}]`, and
`ε : Q[G] → Q` is the augmentation. For a matrix `A` over `Q[G]`, `rk_U(A)` is its von Neumann
rank over `U(G)`, `rk_φ(A) = rank_{Q(t)} φ(A)` is its **Alexander rank**, and
`rk_ε(A) = rank_Q ε(A)`. Write **RD(G, φ)** for "`rk_φ(A) <= rk_U(A)` for every matrix `A` over
`Q[G]`", and RD(G, ε) likewise with `rk_ε`. For amenable `G` with `Q[G]` a domain, `rk_U` is the
rank over the Ore field, so RD(G, φ) is exactly the matrix form of the brief's "Ore
localisation of `Q[L] ⋊ ⟨t⟩`, then `Λ`-rank against Ore rank".

1. **Characterization.** For every group `G` and every `φ : G ↠ Z` the following are equivalent.
   - (i) `G` is locally indicable.
   - (ii) RD(G, φ).
   - (iii) RD(G, ε).
   - (iv) *RD on the fibre:* `rk_φ(A) <= rk_U(A)` for every matrix `A` over `Q[L]`. Such an `A`
     has `φ(A) = ε(A)` constant in `t`.
   - (v) `L` is locally indicable.

   Always `rk_ε(A) <= rk_φ(A)`: evaluation at `t = 1` does not raise rank.
2. **Where the fibred Ore/Følner step fails.** Let `K` be a finitely generated amenable group of
   cd 2 with finite abelianization, `K ≠ 1` (a counterexample to Kropholler's question in
   dimension 2), and let `φ : H ↠ Z` with `[K : H] < ∞` (type (II) of the cd-2 Z-kernel node).
   - (a) *Fibre descent.* `L` contains a finitely generated subgroup `J ≠ 1` with
     `H_1(J; Q) = 0`. Every such `J` has cd 2 and is again a counterexample with finite
     abelianization, lying inside the fibre.
   - (b) *Exact failing matrices.* If `J = ⟨s_1, …, s_m⟩` and `w_1, …, w_m` are relators of `J`
     whose exponent-sum vectors are linearly independent (they exist because `b_1(J) = 0`),
     the Fox matrix `C = (∂w_i/∂s_j)` over `Z[J] ⊂ Z[L]` has `φ(C) = ε(C)` invertible over
     `Q ⊂ Q(t)`, but `rk_U(C) <= m − 1`.
   - (c) So any argument proving `rk_Λ H_2(L) <= rk_Λ H_1(L)` by comparing Alexander rank (or
     `Λ`-rank, or rank after Følner averaging in the `t`-direction) with von Neumann or Ore rank
     on finite matrices over `Q[L] ⋊ ⟨t⟩` must fail. It fails on `C`, a matrix with no
     `t`-dependence. The failure sits in the fibre's own group ring, not in the `t`-direction.
3. **The Alexander inequality needs three hypotheses at once.** The inequality
   `ρ_2 <= ρ_1` (with `ρ_k = rank_Λ H_k(L; Q)`) fails in each of these cases.
   - *Amenable and RD, but cd `= ∞`:* `Z ≀ Z` with `φ` onto the top `Z`. Here `L = Z^{(Z)}`,
     `ρ_1 = 1` and `H_2(L; Q) = Λ²_Q Λ ≅ Λ^{(∞)}`, so `ρ_2 = ∞`. RD holds, since `Z ≀ Z` is
     locally indicable.
   - *cd 2 and RD, but not amenable:* `F_2 × F_2`, with `ρ_2 − ρ_1 = 1`. RD holds since the group
     is locally indicable. The slack is `b_2^{(2)} = 1`.
   - *Amenable and cd 2, but RD fails:* this is exactly a type (II) counterexample, by 1 and 2.

   For cd 2, RD and amenability together give `χ <= 0`, hence `ρ_2 <= ρ_1`, via item 4.
4. **The module form that remains.** Let `H` be finitely generated, amenable, of cd 2, with
   relation module `P`. Suppose RD(H, φ) holds for the finitely many matrices formed by
   lifts to `P ⊂ Q[H]^{(N)}` of a `Λ`-basis of `Λ ⊗ P` (any finite part of it). Then
   `rank_Λ(Λ ⊗ P) <= dim_U(U ⊗ P) = n − 1`, so `χ_Q(H) <= 0` and `ρ_2 <= ρ_1`. The inequality
   `rank_Λ(Λ ⊗ P) <= dim_U(U ⊗ P)` is target item 6(b) for `Γ = Z` on `P`. Since
   `rank_Λ(Λ ⊗ P) = n − b_1 + b_2`, it is equivalent to `χ_Q(H) <= 0`, i.e. to the open inequality of
   `l2-finite-projectives-over-amenable-groups-satisfy-weak-bass` on the core of `P`. By 1, the
   needed rank comparison can hold only for matrices whose rows lie in a projective summand, and
   not for all matrices of `Q[L]`.

**Calibrations.** `Z²` with a projection: `L = Z`, RD holds (commutative domain, determinant),
and `ρ_1 = ρ_2 = 0`. `HW × Z` (Hantzsche–Wendt times `Z`): torsion-free, amenable, virtually
`Z⁴`, not locally indicable; RD(G, φ) fails on a Fox matrix of `HW ⊂ L`, although `Q[G]` is an
Ore domain. So Ore localization alone never gives RD. Finite `G`: RD(G, ε) fails for
`A = (Σ g)`. That is irrelevant here, since `φ` needs `G` infinite and the groups are
torsion-free.

**What this changes.** It closes the Ore/Følner route to type (II) that the brief proposes. In a
fibred counterexample, RD fails already on constant Fox matrices of a rationally perfect,
finitely generated counterexample `J` inside the fibre. The `t`-direction and the free
`Λ`-structure of `H_2(L)` cannot compensate. Type (II) is therefore no easier than the module
inequality for the relation module. Fibre descent also shows that type (II) is never
"self-contained": it always contains, inside a fibre, a finitely generated counterexample with
finite abelianization, which is again of type (I) or (II).

**Next step.** Any proof must separate the projective relation module from flat modules and
arbitrary matrices over `Q[L]`. One route is to use the splitting `P ⊕ P'' = Q[H]^{(∞)}` together
with the `Λ`-freeness of `Λ ⊗ P`. Another is to show that fibre descent terminates, i.e. that some
counterexample is of type (I). Then settle type (I): a residually finite amenable group of cd 2
all of whose finite-index subgroups have `b_1 = 0`. Lück approximation in degree 1 cannot decide
this, since `b_1(N) = 0` is compatible with `b_1^{(2)} = 0`. Only degree 2 carries the defect
(target item 1).
