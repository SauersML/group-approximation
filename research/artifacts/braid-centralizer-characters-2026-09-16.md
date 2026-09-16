# Centralizer characters detect every infinite-order braid (2026-09-16)

Agent `swarm-some-braid-group-has-no-proper`. This is the full proof for route
`braid-centralizer-characters-detect-infinite-order-proof`, which establishes
claim `braid-centralizer-characters-detect-infinite-order`. It was written
while attacking `some-braid-group-has-no-proper-cat0-action`.

## 0. Statement

**Property (Z).** A group `G` has (Z) if every `g ∈ G` of infinite order has
infinite order in `H_1(Z_G(g); Z)`, the abelianization of its centralizer.

Since `Q` is divisible, `[g]` has infinite order in `H_1(Z_G(g); Z)` iff some
homomorphism `Φ : Z_G(g) → Q` has `Φ(g) ≠ 0`.
- (⇐) If `m[g] = 0` with `m ≥ 1`, then `mΦ(g) = 0`.
- (⇒) The map `Z[g] → Q` with `[g] ↦ 1` extends to `H_1(Z_G(g); Z)`, because
  `Q` is an injective `Z`-module.

**Theorem.**
- **(a)** `B_n` has (Z) for every `n ≥ 1`.
- **(b)** (Z) passes to subgroups, to finite-index overgroups and to direct
  products of groups with (Z). So it holds for:
  - `P_n` and every other subgroup of `B_n`;
  - `B_n × Z^r`;
  - `PMod(S_{0,n+1}) ≅ P_n / Z(P_n)`;
  - `B_n / Z(B_n)`;
  - `Mod(S_{0,n+1})`.

**Corollary (§6).** For each of these groups `G`, the elements that are torsion
in the abelianization of their centralizer are exactly the finite-order elements.
Bridson's centralizer criterion (arXiv:0908.0685) forces zero translation length
only on such elements, so for these groups it forces nothing beyond what finite
order already gives. That criterion drives Bridson's obstructions for
`Mod(Σ_g)`, `g ≥ 3`, and with semisimplicity it recovers Kapovich–Leeb's
theorem. Whether Kapovich–Leeb's own proof goes this way was not checked.

## 1. Conventions and standard inputs

**Conventions.**
- `D_n` is the closed disk with marked points `p_1, …, p_n` in its interior, and
  `B_n = Mod(D_n)`.
  - `Mod(D_n)` is orientation-preserving homeomorphisms that fix `∂D_n`
    pointwise and permute the marked points, up to isotopy relative to `∂D_n`
    and the marked points.
  - `P_n` is the pure braid group, the kernel of the permutation map to `S_n`.
  - `Δ²` is the Dehn twist about a curve parallel to `∂D_n`.
- `S = S_{0,n+1}` is the sphere obtained by collapsing `∂D_n` to a marked point
  `p_∞`. `PMod(S)` is the subgroup of `Mod(S)` fixing every marked point.
- A **curve** is an isotopy class of essential simple closed curves in `S` minus
  the marked points. Essential means each complementary disk contains at least
  2 marked points.
  - A **multicurve** is a finite, possibly empty, set of curves with pairwise
    disjoint representatives.
  - A curve avoids `p_∞`, so it is also a curve in `D_n`.
  - `S_c ⊆ [n] = {1, …, n}` is the set of indices of the marked points inside the
    disk that `c` bounds in `D_n`. This is the component of `S − c` not
    containing `p_∞`.
  - `T_c ∈ Mod(S)` and `T̃_c ∈ B_n` are the Dehn twists about `c`.
- `P` is the set of 2-element subsets of `[n]`. For `A ⊆ [n]`, `χ_A ∈ Q^P` is
  the vector with `χ_A(p) = 1` if `p ⊆ A` and `χ_A(p) = 0` otherwise.

**Standard inputs, not re-proved.**

Sources (none fetched in this pass, so no statement numbers are given):
- Farb–Margalit, *A Primer on Mapping Class Groups*, Princeton University Press
  (2012), Chapters 3, 9 and 13.
- N. V. Ivanov, *Subgroups of Teichmüller Modular Groups*, Translations of
  Mathematical Monographs 115, AMS (1992).
- Birman–Lubotzky–McCarthy, "Abelian and solvable subgroups of the mapping class
  group", Duke Math. J. 50 (1983).
- J. McCarthy, "Normalizers and centralizers of pseudo-Anosov mapping classes"
  (preprint, 1982).
- Referee pins (2026-09-16), through a secondary source: Chen–Salter,
  arXiv:1804.11235v1, §2 (read on ar5iv), quotes (N1) as Farb–Margalit
  Corollary 13.3 together with `CRS(h^n) = CRS(h)` (their Proposition 2.2), and
  (N3) as McCarthy [McC82] Theorem 1 (their Proposition 2.6). (N2) is
  Farb–Margalit Proposition 3.20, a number taken from a committed artifact of
  this repository and not re-checked against the book.

- **(B1) Capping.** For `n ≥ 2`, collapsing `∂D_n` to `p_∞` induces a
  homomorphism `π : B_n → Mod(S)`.
  - Its image is the stabilizer of `p_∞` and its kernel is `⟨Δ²⟩`.
  - `π(T̃_c) = T_c` for every curve `c`, and `π(P_n) = PMod(S)`.
  - The permutation of `β ∈ B_n` is the permutation of `p_1, …, p_n` induced by
    `π(β)`.
- **(B2) Linking numbers.** For `{i, j} ∈ P`, forgetting all strands except `i`
  and `j` is a homomorphism `lk_{ij} : P_n → P_2 = ⟨σ_1²⟩ ≅ Z`.
  - For every curve `c`, `T̃_c ∈ P_n` and `lk_{ij}(T̃_c) = χ_{S_c}({i, j})`.
  - `lk_{ij}(Δ²) = 1`.
  - Reason: filling in marked points sends the twist about `c` to the twist
    about `c` in `D_2`. That twist is `σ_1²` if `c` encloses both `i` and `j`,
    and trivial if `c` encloses at most one of them.
  - The script in `experiments/braid-centralizer-characters-2026-09-16/` checks
    the formula, including sign conventions, on 400 random conjugates of full
    twists on blocks of strands.
- **(N1) Canonical reduction systems and pure powers.** Every `f ∈ Mod(S)` has
  a canonical reduction system `C(f)`, a possibly empty multicurve, with
  `C(h f h⁻¹) = h·C(f)` for all `h ∈ Mod(S)`. Every `f` has a power `f^k`,
  `k ≥ 1`, with the following properties, where `C = C(f^k)`:
  - `f^k` fixes every marked point, every curve of `C` and every component of
    `S − ∪C`;
  - for each component `R`, the restriction of `f^k` to `R̂` is either the
    identity or pseudo-Anosov. Here `R̂` is `R` with each boundary curve replaced
    by a marked point.
- **(N2) Cutting.** Let `C` be a multicurve, and let `Stab⁰(C) ≤ Mod(S)` be the
  classes fixing every marked point, every curve of `C` and every component of
  `S − ∪C`.
  - Restriction gives homomorphisms `ρ_R : Stab⁰(C) → Mod(R̂)`, one for each
    component `R`.
  - `⋂_R ker ρ_R` is generated by `{T_c : c ∈ C}`.
  - For `C = ∅`, `Stab⁰(∅) = PMod(S)` and `ρ_S` is the inclusion.
- **(N3) McCarthy.** If `φ ∈ Mod(Σ)` is pseudo-Anosov, then `Z_{Mod(Σ)}(φ)` is
  virtually infinite cyclic.

## 2. Two group-theoretic lemmas

**Lemma T (transfer criterion).** Let `g ∈ G` and let `H ≤ Z_G(g)` have finite
index `j`. Suppose there are a homomorphism `ψ : H → Q` and an `N ≥ 1` with
`g^N ∈ H` and `ψ(g^N) ≠ 0`. Then some homomorphism `Φ : Z_G(g) → Q` has
`Φ(g) ≠ 0`, so `g` has infinite order in `H_1(Z_G(g); Z)`.

*Proof.*
1. **Set-up.** Write `Z = Z_G(g) = ⊔_{i=1}^{j} t_i H`. For `z ∈ Z` write
   `z t_i = t_{σ(i)} h_i(z)` with `h_i(z) ∈ H`. The transfer is
   `V(z) = ∏_i h_i(z) mod [H, H]`; it is a homomorphism `V : Z → H^{ab}`.
2. **The transfer of a central element.** Let `z` be central in `Z` and let
   `(i, σ(i), …, σ^{ℓ−1}(i))` be a cycle of `σ`. Iterating the defining
   relation gives `z^ℓ t_i = t_i · h_{σ^{ℓ−1}(i)}(z) ⋯ h_i(z)`. So the product of
   the `h`'s along the cycle is `t_i⁻¹ z^ℓ t_i = z^ℓ`. Multiplying over the
   cycles gives `V(z) = [z^j]`, where the cycle lengths add up to `j`. In
   particular `z^j ∈ H`.
3. **The element `g`.** `g` is central in `Z`, so `V(g) = [g^j]`. The
   homomorphism `ψ` factors through `H^{ab}`, so `Φ := ψ ∘ V` is a homomorphism
   `Z → Q` with `Φ(g) = ψ(g^j)`.
4. **Nonvanishing.** Both `g^N` and `g^j` lie in `H`, so
   `N · ψ(g^j) = ψ(g^{jN}) = j · ψ(g^N) ≠ 0`. Hence `Φ(g) ≠ 0`. ∎

**Lemma P (permanence of (Z)).**
- **(i)** If `G` has (Z), so does every subgroup `L ≤ G`.
- **(ii)** If `K ≤ G` has finite index and `K` has (Z), then `G` has (Z).
- **(iii)** `Z` has (Z). If `G_1` and `G_2` have (Z), so does `G_1 × G_2`.

*Proof.*
- **(i)** Let `g ∈ L` have infinite order. Restrict a character
  `Φ : Z_G(g) → Q` with `Φ(g) ≠ 0` to `Z_L(g) = Z_G(g) ∩ L`, which contains `g`.
- **(ii)** Let `g ∈ G` have infinite order.
  1. The cosets `g^i K`, `0 ≤ i ≤ [G : K]`, cannot all be distinct, so
     `g^a ∈ K` for some `a ≥ 1`.
  2. `g^a` has infinite order in `K`, so there is `Φ_0 : Z_K(g^a) → Q` with
     `Φ_0(g^a) ≠ 0`.
  3. `H := Z_K(g^a) = Z_G(g^a) ∩ K` has finite index in `Z_G(g^a)`. Lemma T,
     applied to `g^a` with `N = 1`, gives `Φ : Z_G(g^a) → Q` with `Φ(g^a) ≠ 0`.
  4. `Z_G(g) ≤ Z_G(g^a)`, so `Φ` restricts to `Z_G(g)`, where
     `Φ(g) = Φ(g^a)/a ≠ 0`.
- **(iii)** `Z` is abelian, so the identity character works. Now let
  `(g_1, g_2) ∈ G_1 × G_2` have infinite order. Then
  `Z((g_1, g_2)) = Z_{G_1}(g_1) × Z_{G_2}(g_2)`, and some `g_i` has infinite
  order. Compose the projection onto the `i`-th factor with a character that
  detects `g_i`. ∎

## 3. Laminar independence

**Lemma L.** Let `F` be a family of distinct subsets of `[n]`, each of size at
least 2, that is **laminar**: any two members are nested or disjoint. Then the
vectors `(χ_A)_{A ∈ F}` are linearly independent over `Q`.

*Proof.*
1. **Children.** The *children* of `A ∈ F` are the maximal members of `F`
   properly contained in `A`.
   - Two children meet only if they are nested. By maximality they are then
     equal, so distinct children are disjoint.
   - `F` is finite, so every member of `F` properly contained in `A` lies in some
     child.
2. **Private pairs.** Choose `p_A ∈ P` with `p_A ⊆ A` as follows:
   - if `A` has at least two children, one point from each of two different
     children;
   - if `A` has exactly one child `A_1`, one point of `A_1` and one of `A − A_1`,
     which is nonempty;
   - if `A` has no children, any two points of `A`.

   In every case `p_A` lies in no child of `A`. So `p_A` lies in no member of `F`
   properly contained in `A`.
3. **Incidence.** For `A, B ∈ F`, `p_A ⊆ B` iff `A ⊆ B`.
   - If `A ⊆ B`, then `p_A ⊆ A ⊆ B`.
   - Conversely, if `p_A ⊆ B`, then `A ∩ B ≠ ∅`, so `A` and `B` are nested. The
     case `B ⊊ A` is excluded by step 2.
4. **Triangularity.** The square matrix `M_{B,A} := χ_B(p_A)` is therefore the
   zeta matrix `[A ⊆ B]` of the poset `(F, ⊆)`. Listed by decreasing size, it is
   unitriangular, hence invertible.
5. **Conclusion.** If `Σ_B a_B χ_B = 0`, evaluating at each `p_A` gives
   `Σ_B a_B M_{B,A} = 0` for all `A`. So `a = 0`. ∎

*Check.* `experiments/braid-centralizer-characters-2026-09-16/check_laminar_and_lk.py`
verifies independence and step 3 for every maximal laminar family on `[n]` with
`n ≤ 7`. These are the full binary hierarchies, `(2n−3)!!` of them. Every laminar
family of sets of size at least 2 extends to one of them, and independence
passes to subfamilies.

## 4. Proof of Theorem (a)

For `n ≤ 2`, `B_1 = 1` and `B_2 ≅ Z` are abelian, so (Z) holds. Let `n ≥ 3`,
let `β ∈ B_n` have infinite order, and put `f := π(β) ∈ Mod(S)`, with `π` as in
(B1).

**Step 1 (power and multicurve).** By (N1) choose `k ≥ 1` so that `f^k` has the
properties listed there, and put `C := C(f^k)` and `g := β^k`.
- `π(g) = f^k` fixes every `p_i`, so `g ∈ P_n` by (B1).

**Step 2 (a finite-index subgroup of the centralizer).**
- **Invariance.** Let `h ∈ Z_{B_n}(β)`. Then `h` commutes with `g`, so `π(h)`
  commutes with `f^k`. Naturality in (N1) gives `π(h)·C = C(π(h) f^k π(h)⁻¹) = C`.
  So `π(Z_{B_n}(β))` lies in the setwise stabilizer `Stab(C)`.
- **Finite index.** `Stab(C)` permutes three finite sets: the marked points, the
  curves of `C`, and the components of `S − ∪C`. The kernel of this action is
  `Stab⁰(C)`, which therefore has finite index in `Stab(C)`. Hence

  `H := Z_{B_n}(β) ∩ π⁻¹(Stab⁰(C))`

  has finite index in `Z_{B_n}(β)`.
- **Properties of `H`.** `H ≤ P_n`, because `π(H)` fixes every marked point.
  Also `g ∈ H`, by Step 1.

By (N1), each `ρ_R(f^k)` is the identity or pseudo-Anosov. The homomorphism
`ρ_R` is defined on `Stab⁰(C)`, which contains `f^k`.

**Case A: some `φ := ρ_R(f^k)` is pseudo-Anosov.**
1. **A virtually cyclic image.** `θ := ρ_R ∘ π : H → Mod(R̂)` is a homomorphism.
   Every `h ∈ H` commutes with `g`, so `θ(h)` commutes with `θ(g) = φ`. Thus
   `θ(H) ≤ Z_{Mod(R̂)}(φ)`, which is virtually infinite cyclic by (N3).
   - `θ(H)` contains `φ`, which has infinite order. So `θ(H)` is an infinite
     virtually cyclic group and has an infinite cyclic subgroup `⟨t⟩` of finite
     index.
2. **A power of `φ` in the cyclic subgroup.** Some `a ≥ 1` has `φ^a ∈ ⟨t⟩`, say
   `φ^a = t^b`. Here `b ≠ 0` because `φ` has infinite order.
3. **The character.** `H' := θ⁻¹(⟨t⟩)` has finite index in `H`, hence in
   `Z_{B_n}(β)`. Since `t` has infinite order, `ψ(h)` defined by
   `θ(h) = t^{ψ(h)}` is a homomorphism `H' → Z ⊆ Q`.
4. **Apply Lemma T.** `β^{ka} = g^a ∈ H'` and `ψ(g^a) = b ≠ 0`. Lemma T with
   `N = ka` gives a character of `Z_{B_n}(β)` nonzero on `β`.

**Case B: `ρ_R(f^k) = 1` for every component `R`.**
1. **`g` is a multitwist.** By (N2), `f^k ∈ ⟨T_c : c ∈ C⟩`. Twists about disjoint
   curves commute, so `f^k = ∏_{c∈C} T_c^{e_c}` with `e_c ∈ Z`.
   - Put `x := ∏_{c∈C} T̃_c^{e_c}`, which lies in `P_n` by (B2).
   - By (B1), `π(x) = f^k = π(g)`, and `ker π = ⟨Δ²⟩` is central. So
     `g = x·Δ^{2e}` for some `e ∈ Z`.
2. **The linking vector.** Let `v := (lk_{ij})_{{i,j}∈P} : P_n → Q^P`. This is a
   homomorphism, and (B2) gives

   `v(g) = Σ_{c∈C} e_c χ_{S_c} + e·χ_{[n]}.`

3. **The family `F := {S_c : c ∈ C} ∪ {[n]}`.**
   - **Sizes.** `c` is essential in `S`, so each component of `S − c` contains at
     least 2 of the `n + 1` marked points. Hence `2 ≤ |S_c| ≤ n − 1`. In
     particular `S_c ≠ [n]`, and every member of `F` has size at least 2.
   - **Laminar.** Let `c ≠ c'` in `C`, with disjoint representatives bounding
     closed disks `D, D' ⊆ D_n` (Schoenflies). If `c' ⊆ int D`, then `D' ⊆ D`.
     Otherwise `c'` lies outside `D`, and either `D ⊆ int D'` or `D ∩ D' = ∅`. So
     `S_c` and `S_{c'}` are nested or disjoint.
   - **Distinct.** Suppose `S_c = S_{c'}`. The two sets are nonempty, so they are
     nested, say `D' ⊆ D`. Then the annulus `D − int D'` contains no marked point
     and does not contain `p_∞`. So `c` and `c'` are isotopic in `S` minus the
     marked points, contradicting `c ≠ c'`. Hence `c ↦ S_c` is injective, and the
     coefficients `e_c`, `e` are the coefficients of distinct members of `F`.
4. **Some linking number is nonzero.** If `v(g) = 0`, Lemma L forces `e_c = 0`
   for all `c` and `e = 0`. Then `g = 1`, contradicting the infinite order of `β`.
   So `lk_{ij}(g) ≠ 0` for some `{i, j}`.
5. **Apply Lemma T.** `H ≤ P_n` from Step 2, so `ψ := lk_{ij}|_H` is defined, and
   `ψ(β^k) = lk_{ij}(g) ≠ 0`. Lemma T with `N = k` gives a character of
   `Z_{B_n}(β)` nonzero on `β`.

In both cases `β` has infinite order in `H_1(Z_{B_n}(β); Z)`. ∎

**Remark (what Case B shows).** A nontrivial power of a reducible braid whose
components are all trivial is always seen by pure-braid linking numbers. This
is where genus 0 differs from `Mod(Σ_g)`, `g ≥ 3`.
- There, the twist about a curve is killed in the abelianization of its
  centralizer, because a complementary piece has genus at least 2 and perfect
  or finite-abelianization mapping class group. This is the proof of Bridson's
  Proposition on Dehn twists in arXiv:0908.0685.
- In `B_n`, the complementary pieces are punctured disks. Their braid groups
  have abelianization `Z`, and the twist `Δ_a²` maps to `a(a−1) ≠ 0` in it.

## 5. Proof of Theorem (b)

The permanence statements are Lemma P. Applied to `B_n`:
- **`P_n`, subgroups and products.** `P_n` and every subgroup of `B_n` have (Z)
  by Lemma P(i). `B_n × Z^r` has (Z) by Lemma P(iii).
- **The splitting of `P_n`.** Let `K := ker(lk_{12}) ≤ P_n`, where `n ≥ 2`.
  - `Δ²` is central with `lk_{12}(Δ²) = 1`, so `P_n = K × ⟨Δ²⟩` and
    `K ≅ P_n/⟨Δ²⟩`.
  - `Z(P_n) = ⟨Δ²⟩` for `n ≥ 3`, so `K ≅ P_n/Z(P_n)`. By (B1),
    `P_n/⟨Δ²⟩ ≅ PMod(S_{0,n+1})`.
  - `K` has (Z) by Lemma P(i), so `PMod(S_{0,n+1})` has (Z).
- **The sphere groups.** `PMod(S_{0,n+1})` has index `(n+1)!` in
  `Mod(S_{0,n+1})`, so `Mod(S_{0,n+1})` has (Z) by Lemma P(ii). Its subgroup
  `Mod(S_{0,n+1}, p_∞) ≅ B_n/⟨Δ²⟩` has (Z) by Lemma P(i). ∎

Case B of §4 also runs directly in `PMod(S_{0,n+1})`, using the characters of
`Q^P / Q·χ_{[n]}`. Lemma L applied to `F`, which already contains `[n]`, shows that
`Σ e_c χ_{S_c}` is not a multiple of `χ_{[n]}` unless all `e_c = 0`.

## 6. Consequence for isometric actions on CAT(0) spaces

**Bridson's criterion.** Bridson, "Semisimple actions of mapping class groups on
CAT(0) spaces", arXiv:0908.0685. The following was read from the arXiv LaTeX
source on 2026-09-16.
- **Proposition `l:hyp`:** "Let Γ be a group acting by isometries on a complete
  CAT(0) space X. If γ ∈ Γ acts as a hyperbolic isometry then γ has infinite
  order in the abelianisation of its centralizer Z_Γ(γ)."
- **Theorem `t:paras`:** in the proof, "The proof of Theorem [B] will apply
  provided we can extend Proposition [l:hyp] to cover non-neutral parabolics."
  This is done through Karlsson–Margulis and a Busemann character
  `φ : Z_Γ(γ) → R` with `φ(γ) = −|γ|`.
- **Combined contrapositive.** If `γ` is torsion in `H_1(Z_Γ(γ); Z)`, then
  `|γ| = 0` in every isometric action on a complete CAT(0) space.
- **Mapping class groups.** For `Mod(Σ_g)`, `g ≥ 3`, Dehn twists are torsion in
  the abelianizations of their centralizers. This is the source of Theorem
  `t:paras`. With semisimplicity it gives Kapovich–Leeb's theorem that
  `Mod(Σ_g)` has no proper semisimple action. Kapovich–Leeb's own proof was not
  read.

**Corollary.** Let `G` be any group in Theorem (b), for example `B_n`, `P_n` or
`Mod(S_{0,n+1})`, and let `G` act by isometries on a complete CAT(0) space.
- The elements that are torsion in the abelianization of their centralizer are
  exactly the finite-order elements.
- So the criterion above forces `|g| = 0` only on finite-order elements, where
  it is automatic.
- The same holds for every finite-index overgroup of `G`, and after inducing an
  action to `X^m`, since (Z) passes to finite-index overgroups by Lemma P(ii).

**Why this matters for the target `some-braid-group-has-no-proper-cat0-action`.**
- **The Kapovich–Leeb/Bridson template has no input here.** The template is:
  - find an infinite-order element that is torsion in the abelianization of its
    centralizer;
  - conclude that it has zero translation length;
  - use semisimplicity (cocompactness) to make it elliptic;
  - contradict properness.

  By the Corollary, the first step fails for every braid.
- **Necessary for the parabolic case.** Even without semisimplicity, forcing
  some braid to be neutral is a necessary first step toward the "rule out
  parabolics" programme recorded in the target's `## Attempts`. This step
  cannot come from abelian characters of centralizers.
- **What an obstruction must use instead.** It needs something beyond centralizer
  abelianizations. Examples:
  - relations among translation lengths of non-commuting elements;
  - local compactness of `X`, through the boundary at infinity;
  - rigidity for higher-rank abelian subgroups.
- **What the Corollary does not do.** It produces no action, proper or not, and
  gives no lower bound on translation lengths. It removes one mechanism only.

**Same equivalence class as the target.** The existence of a proper isometric
action on a proper CAT(0) space passes along the same operations as (Z):
- **Subgroups:** restrict the action.
- **Finite-index overgroups:** if `K ≤ G` has index `m` and acts properly on
  `X`, then `G` acts properly on the `ℓ²`-product `X^m`, by multiplicative
  induction as in Bridson's Remark `r:abelian`. Properness can be read on one
  coordinate after passing to a finite-index normal subgroup of `G` contained
  in `K`.
- **Products with `Z`:** use `X × R`.

So, for each `n`, `B_n` acts properly on a proper CAT(0) space iff
`Mod(S_{0,n+1})` does. The chain is
`B_n ⊇ P_n = K × Z`, with `K ≅ PMod(S_{0,n+1}) ≤ Mod(S_{0,n+1})` of finite
index.

## 7. Checks and weakest points

**Worked examples.**
- **`β = σ_1σ_2 ∈ B_3`.** `β³ = Δ²`, so `β` has infinite order and `f = π(β)`
  has order 3 in `Mod(S_{0,4})`.
  - With `k = 3`, `C = ∅` and `f^3 = 1`, we are in Case B with `x = 1` and
    `g = Δ²`.
  - `lk_{12}(g) = 1`, and `H = Z(β) ∩ P_3`.
  - The character of Lemma T is `Φ = ψ ∘ V`, where `ψ = lk_{12}|_H` and
    `j = [Z(β) : H]`. Since `β^j ∈ H ≤ P_3`, `j` is divisible by 3, and
    `Φ(β) = ψ(β^j) = lk_{12}(Δ^{2j/3}) = j/3 ≠ 0`.
- **`β = T̃_c`, with `c` enclosing strands `1, …, a`, `2 ≤ a ≤ n − 1`.**
  - `C = {c}` and `f` is a multitwist, so Case B applies with `k = 1`.
  - `v(β) = χ_{[a]} ≠ 0`, so `lk_{12}` restricted to `Z(β) ∩ P_n` detects it.
- **`β = σ_1σ_2⁻¹ ∈ B_3`.** Its image in `Mod(S_{0,4})` is pseudo-Anosov, so Case A
  applies with `C = ∅` and `R̂ = S_{0,4}`.
  - The character comes from the virtually cyclic centralizer of the image.

**Weakest points, in the order a referee should attack.**
1. **(N1) and (N2) as used.** The proof needs:
   - the *natural* canonical reduction system of a pure power;
   - that restrictions to components are identity or pseudo-Anosov;
   - that the common kernel of the restriction maps is generated by the twists
     about `C`.

   These are standard (Birman–Lubotzky–McCarthy, Ivanov, Farb–Margalit Ch. 13
   and §3.6), but their statement numbers were not re-checked in this pass. The
   kernel statement is needed only in Case B, and only in the form "all
   restrictions trivial ⇒ multitwist about `C`".
2. **(N3)** is used only in Case A, and only for the virtual cyclicity of
   `Z_{Mod(R̂)}(φ)` where `R̂` is a punctured sphere. The target group `Mod(R̂)`
   may permute marked points; that does no harm, since only a subgroup of the
   centralizer is used.
3. **(B2)** is a sign and normalization convention. It was checked numerically
   (400 random conjugates of block full twists, `3 ≤ n ≤ 8`). The proof uses
   only that `lk_{ij}(T̃_c) = χ_{S_c}({i,j})` up to a common nonzero factor, and
   the same factor for `Δ²`.
4. **The transfer formula for central elements** (Lemma T, step 2) is a
   textbook computation, reproduced in full above.
