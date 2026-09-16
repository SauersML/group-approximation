# BVC groups that split over virtually cyclic subgroups (2026-09-16)

Swarm lane on `finitely-presented-bvc-groups-are-virtually-cyclic`. This is the full proof of
`bvc-groups-splitting-over-vc-subgroups-are-vc`.

## Statement

**Theorem.** Let `G` have property BVC. Suppose `G` splits nontrivially over a virtually cyclic
subgroup, in one of two ways:

- (amalgam) `G = A *_C B` with `C != A`, `C != B` and `C` virtually cyclic; or
- (HNN) `G = <H, t | t x t^{-1} = theta(x), x in C>` with `theta: C -> C'` an isomorphism
  between subgroups of `H` and `C` virtually cyclic.

Then `C` is finite and `G` is virtually cyclic. More precisely, in the amalgam case
`[A:C] = [B:C] = 2`, so `C` is normal and `G/C` is infinite dihedral. In the HNN case
`C = C' = H` is finite, so `G = H ⋊ Z`.

No finite generation of `G`, `A`, `B` or `H` is assumed.

## Inputs

- (NF) The normal form theorem for amalgams (Lyndon–Schupp, *Combinatorial Group Theory*,
  Ch. IV §2; Serre, *Trees*, §I.1). A reduced form of `g` in `A *_C B` is a product
  `g_1 ... g_n` whose letters alternate between `A - C` and `B - C`. Any two reduced forms of
  one element have the same length and the same sequence of factors. `(g_1, ..., g_n)` and
  `(h_1, ..., h_n)` represent the same element iff `h_1 = g_1 c_1`,
  `h_i = c_{i-1}^{-1} g_i c_i` and `h_n = c_{n-1}^{-1} g_n` for some `c_i` in `C`. If
  right transversals of `C` in `A` and in `B` are fixed, both containing `1`, then every
  element is uniquely `c s_1 ... s_n` with `c` in `C` and the `s_i` alternating nontrivial
  representatives. The factors embed in `G`.
- (CT) The conjugacy theorem, Lyndon–Schupp IV.2.8, in the form used by the landed route
  `bvc-amalgams-have-two-transitive-vertex-actions-proof`. Every element is conjugate to a
  cyclically reduced one. If `g` is cyclically reduced and conjugate to a cyclically reduced
  `p_1 ... p_n` with `n >= 2`, then `g` is obtained by cyclically permuting `p_1 ... p_n`
  and then conjugating by an element of `C`.
- Landed claims: `bvc-amalgams-have-two-transitive-vertex-actions` (`|C\A/C| = 2`),
  `non-ascending-hnn-extensions-lack-bvc` (von Puttkamer–Wu 1607.03790, Lemma 2.4) and
  `virtually-solvable-bvc-groups-are-virtually-cyclic` (von Puttkamer–Wu, Proposition 1.12).
- Elementary facts about virtually cyclic (VC) groups, proved in §0.

**Property P.** `G` has *property P* if there are finitely many VC subgroups `V_1, ..., V_n`
such that every element of `G` is conjugate into some `V_i`. BVC implies P (apply BVC to
`<g>`). P passes to quotients: if `N` is normal, `G/N` has P with witnesses `V_i N / N`,
which are VC.

## §0. Virtually cyclic groups

Let `V` be an infinite VC group.

- (V1) *Every infinite subgroup `U` of `V` has finite index.* Let `<z>` have finite index `r`
  in `V`. If `U ∩ <z> = 1`, then `u ↦ u<z>` is injective on `U`, so `|U| <= r`. Otherwise
  `U ∩ <z> = <z^k>` with `k >= 1`, which has finite index in `V`. The same argument shows
  that a finite normal subgroup of `V` has order at most `r`.
- (V2) *`V` has a normal infinite cyclic subgroup of finite index.* Take the normal core of
  `<z>`: it has finite index, lies in `<z>`, and is infinite by (V1). For `v` in `V` and a
  normal `<x>` of index `R`, `v^R` lies in `<x>` and `v x v^{-1} = x^{±1}`.
- (V3) *`V` is finitely generated, and has a characteristic infinite cyclic subgroup of
  finite index.* Let `<x>` have index `r`. A finitely generated group has finitely many
  subgroups of index `r` (they correspond to actions on `r` points), so their intersection
  `K` is characteristic of finite index. It lies in `<x>` and is infinite.
- (V4) *`V` has a unique maximal finite normal subgroup `F(V)`, and `V/F(V)` is `Z` or
  `D_∞`.* The product of two finite normal subgroups is finite and normal, and their orders
  are bounded by (V1), so a finite normal subgroup of maximal order contains every other.
  Put `W = V/F(V)`, which has no nontrivial finite normal subgroup. Let `<x>` be normal of
  finite index in `W` and `W^+` its centralizer, of index at most 2. `<x>` is central in
  `W^+` of some finite index `r`. The transfer `W^+ -> <x>` into a central subgroup of
  index `r` is `w ↦ w^r` (textbook transfer evaluation: `V(w) = prod_i t_i w^{m_i}
  t_i^{-1} = prod_i w^{m_i} = w^r`, because each `t_i w^{m_i} t_i^{-1}` is central and
  therefore equals `w^{m_i}`). So `w ↦ w^r` is a homomorphism. Its kernel is characteristic
  in `W^+`, hence normal in `W`. It meets `<x>` trivially, so it is finite by (V1), hence
  trivial. So `W^+` embeds in `<x>` and `W^+ ≅ Z = <y>`. If `W != W^+`, take `s` outside
  `W^+`. It inverts `x`, a nonzero power of `y`, so `s y s^{-1} = y^{-1}`. Now `s^2` lies in
  `W^+` and commutes with `s`, so `s^2 = y^j` with `y^{-j} = y^j`, which forces `s^2 = 1`.
  Hence `W ≅ Z ⋊ Z/2 = D_∞`.
- (V5) *In `Z` and in `D_∞`, a nontrivial finite subgroup has finite normalizer.* `Z` has no
  nontrivial finite subgroup. In `D_∞ = <s, r | r^2, r s r = s^{-1}>` the elements of finite
  order other than 1 are the reflections `s^i r`. Two distinct reflections generate an
  infinite group, so a nontrivial finite subgroup is `{1, s^i r}`. Its normalizer is its
  centralizer, and `s^j` or `s^j r` commutes with `s^i r` only when `j = 0`, respectively
  `j = i`. So the normalizer has order 2.
- (V6) *A VC group mapping onto `Z` has finite kernel.* The kernel has infinite index, so it
  is finite by (V1). Equivalently: a group with an infinite normal subgroup of infinite index
  is not VC.

**Lemma 0 (finite-by-solvable).** If `L` is a finite normal subgroup of `Γ` and `Γ/L` is
solvable, then `Γ` is virtually solvable.

*Proof.* `C_Γ(L)` is the kernel of `Γ -> Aut(L)`, so it has finite index. `C_Γ(L) ∩ L` is
central in `C_Γ(L)`, hence abelian, and `C_Γ(L)/(C_Γ(L) ∩ L) ≅ C_Γ(L) L / L <= Γ/L` is
solvable. So `C_Γ(L)` is abelian-by-solvable, hence solvable, of finite index in `Γ`. `∎`

## §1. The length function and the class bound under property P

Let `G = A *_C B` with `C` proper in both factors. By (CT), if some cyclically reduced
conjugate of `g` has length `n >= 2`, every cyclically reduced conjugate has length `n`.
Put `λ(g) = n` in that case, and `λ(g) = 0` otherwise, so `λ(g) = 0` exactly when `g` is
conjugate into `A` or `B`. `λ` is a conjugacy invariant. If `g` is cyclically reduced of
length `n >= 2`, then `g^k` (`k >= 1`) is the concatenated word, cyclically reduced of length
`kn`, and `g^{-1}` is cyclically reduced of length `n`. So `λ(g^k) = |k| λ(g)` and `g` has
infinite order.

**Lemma 1.** If `G = A *_C B` (with `C` proper in both factors) has property P, there is an
integer `K` such that for every `l >= 2` the elements `g` with `λ(g) = l` lie in at most `K`
conjugacy classes of `G`.

*Proof.* This is Step 3 of `bvc-amalgams-have-two-transitive-vertex-actions-proof`, with P
in place of BVC. Let `V` be an infinite VC subgroup and `<z>` normal of index `R` in `V`
(V2). Suppose `v` in `V` has `λ(v) = l >= 2`. Then `v^R = z^s` with `s != 0`. If
`λ(z) = 0`, then `z^s` is conjugate into a factor and `λ(z^s) = 0`, contradicting
`λ(v^R) = Rl`. So `λ(z) >= 2` and `|s| = Rl / λ(z)`: `v^R` takes one of two values. Fix a
coset `<z> f`, where `f z f^{-1} = z^e` with `e = ±1`.

- If `e = 1`, then `(z^j f)^R = z^{jR} f^R` is injective in `j`, so at most 2 elements of
  the coset have `λ = l`.
- If `e = -1`, then `z (z^j f) z^{-1} = z^{j+2} f`, so the coset lies in at most 2 classes
  of `V`.

So the elements of `V` with `λ = l` lie in at most `2R` classes of `V`. Let `V_1, ..., V_n`
witness P. An element with `λ = l >= 2` has infinite order, so it is conjugate into an
infinite `V_i`, to an element with `λ = l`. Hence `K = sum over infinite V_i of 2R(V_i)`
works. `∎`

## §2. Rigidity of length-two products

**Lemma 2.** Let `G = A *_C B`, `a` in `A - C`, and `b, b'` in `B - C`. If `ab'` is conjugate
to `ab`, then `b' = (a^{-1} c a) b c^{-1}` for some `c` in `D_a := C ∩ a C a^{-1}`. So each
conjugacy class of `G` contains at most `|D_a|` of the elements `ab`, `b` in `B - C`. The same
holds with the roles of `A` and `B` exchanged.

*Proof.* `ab` and `ab'` are cyclically reduced of length 2. By (CT), `ab' = c p c^{-1}` with
`c` in `C` and `p` in `{ab, ba}`. The element `c(ba)c^{-1} = (cb)(a c^{-1})` has a reduced
form with factor sequence `(B, A)`, while `ab'` has `(A, B)`. By (NF) they differ, so
`ab' = (ca)(b c^{-1})`. By (NF) there is `c_1` in `C` with `ca = a c_1` and
`b c^{-1} = c_1^{-1} b'`. Then `c = a c_1 a^{-1}` lies in `C ∩ a C a^{-1}`, and
`b' = c_1 b c^{-1}` with `c_1 = a^{-1} c a`. The exchanged statement is the same argument for
`B *_C A`. `∎`

**Proposition 3 (a weakly malnormal edge forces finiteness).** Let `G = A *_C B` (with `C`
proper in both factors) have property P. If `D_a = C ∩ a C a^{-1}` is finite for some `a` in
`A - C`, then `B` is finite. If moreover `C` is finite, then `A` is finite.

*Proof.* The elements `ab`, `b` in `B - C`, are pairwise distinct and all have `λ = 2`. By
Lemmas 1 and 2, `|B - C| <= K |D_a|`. `B - C` contains a coset `bC`, so `|C| <= |B - C|`
and `B` is finite. If `C` is finite, apply the exchanged Lemma 2 to some `b` in `B - C`,
where `C ∩ b C b^{-1}` is finite. `∎`

**Lemma 4 (counting with finite factors).** Let `Ḡ = Ā *_Q B̄` with `Ā`, `B̄` finite and `Q`
proper in both, `p = [Ā:Q]`, `q = [B̄:Q]`. For each `m >= 1`, at least
`((p-1)(q-1))^m / m` conjugacy classes of `Ḡ` have `λ = 2m`.

*Proof.* Fix right transversals as in (NF). The elements `c s_1 s_2 ... s_{2m}`, with `c` in
`Q`, odd `s_i` nontrivial representatives in `Ā` and even `s_i` in `B̄`, are
`|Q| ((p-1)(q-1))^m` distinct elements. Each has a reduced form of factor sequence
`(A, B, ..., A, B)`, so it is cyclically reduced with `λ = 2m`. Let `h` and `h'` be two of
these elements in one conjugacy class. By (CT), `h' = c h* c^{-1}` with `c` in `Q` and `h*` a
cyclic permutation of the reduced word of `h`. Conjugation by `c` keeps the factor sequence,
so by (NF) `h*` starts with an `A`-letter: it is one of the `m` rotations by an even number of
letters. So a class contains at most `m |Q|` of these elements, and there are at least
`|Q| ((p-1)(q-1))^m / (m |Q|)` classes. `∎`

## §3. The amalgam case

Let `G = A *_C B` have BVC, with `C` proper in both factors and VC.

**Step 1: `[A:C]` and `[B:C]` are finite.** By `bvc-amalgams-have-two-transitive-vertex-actions`,
`A = C ⊔ C a C` for any `a` in `A - C`. The left cosets of `C` inside `CaC` are the `caC`
(`c` in `C`), and `caC = c'aC` iff `c^{-1} c'` lies in `C ∩ a C a^{-1} = D_a`. So

    [A:C] = 1 + [C : D_a].

If `C` is finite, `[A:C] <= 1 + |C|`. If `C` is infinite and `[A:C] = ∞`, then `D_a` has
infinite index in `C` and is finite by (V1). Proposition 3 then makes `B` finite, so `C` is
finite, a contradiction. The same holds for `B`. So `A` and `B` are VC.

**Step 2: `[A:C] = [B:C] = 2`.** If `C` is finite, put `Z = 1`. If `C` is infinite, then `A`
and `B` are infinite VC groups. Take normal infinite cyclic subgroups `<x_A>` of index `R_A`
in `A` and `<x_B>` of index `R_B` in `B` (V2), fix `z` in `C` of infinite order, and put
`M = R_A R_B`. For `a` in `A`, `z^{R_A}` is a nonzero power of `x_A` and
`a x_A a^{-1} = x_A^{±1}`, so `a z^{R_A} a^{-1} = z^{±R_A}` and `a z^M a^{-1} = z^{±M}`.
Likewise for `b` in `B`. So `Z = <z^M>` is normalized by `A` and `B`, hence normal in
`G = <A, B>`, and `Z <= C`.

Put `Ḡ = G/Z`. By the universal property of the pushout, `Ḡ ≅ (A/Z) *_{C/Z} (B/Z)`. Homomorphisms
from `A/Z` and `B/Z` agreeing on `C/Z` are the same as homomorphisms from `G` killing `Z`,
and `C/Z` embeds in both factors. The factors are finite, and `C/Z` is proper in both with
`p = [A:C]` and `q = [B:C]`. `Ḡ` has property P. Lemma 1 for `Ḡ` bounds the number of
classes with `λ = 2m` by a constant `K̄`, while Lemma 4 gives at least `((p-1)(q-1))^m / m`.
If `p >= 3` or `q >= 3`, then `(p-1)(q-1) >= 2` and `2^m / m -> ∞`, which is impossible. So
`p = q = 2`.

**Step 3: `C` is finite and `G` is VC.** Index 2 makes `C` normal in `A` and in `B`, hence in
`G`. By the same pushout argument `G/C ≅ Z/2 * Z/2 ≅ D_∞`.

- *If `C` is infinite.* `G` is not VC by (V6): `C` is an infinite normal subgroup of infinite
  index. By (V3), `C` has a characteristic infinite cyclic subgroup `K` of finite index. It is
  normal in `G`. `G/K` has the finite normal subgroup `C/K` with quotient `D_∞`, which is
  solvable. By Lemma 0 some finite-index `S/K <= G/K` is solvable, and `S` is solvable because
  `K` is abelian. So `G` is virtually solvable, has BVC and is not VC. This contradicts
  `virtually-solvable-bvc-groups-are-virtually-cyclic`.
- *So `C` is finite.* Let `G_0` be the preimage of the translation subgroup `Z` of `D_∞`, so
  `[G:G_0] = 2`. Pick `t` in `G_0` mapping to a generator. Then `<t> ∩ C = 1`, so `<t> ≅ Z`,
  and `G_0 = C <t>`, so `[G_0 : <t>] <= |C|`. Hence `G` is VC. `∎`

## §4. The HNN case

Let `G = <H, t | t x t^{-1} = theta(x), x in C>` have BVC, with `theta: C -> C'` an
isomorphism of subgroups of `H` and `C` VC.

**Step 1: ascending.** By `non-ascending-hnn-extensions-lack-bvc`, `C = H` or `C' = H`. With
`s = t^{-1}`, `G = <H, s | s y s^{-1} = theta^{-1}(y), y in C'>`, so we may assume `C = H`.
Then `H` is VC and `theta: H -> H` is an injective endomorphism with image `C'`.

**Step 2: the kernel.** `t ↦ 1`, `H ↦ 0` defines `phi: G -> Z`. Put `H_k = t^{-k} H t^k` for
`k >= 0`. Since `t H t^{-1} = theta(H) <= H`, we get `H <= H_1` and `H_k <= H_{k+1}`. The union
`N = ∪_k H_k` is a subgroup. `t^{-1} H_k t = H_{k+1}`, `t H_k t^{-1} = H_{k-1}` for `k >= 1`,
`t H t^{-1} <= H`, and `H <= N`, so `N` is normal in `G = <H, t>`. `G/N` is generated by `tN`,
and `phi(t) = 1`, so `G/N ≅ Z` and `N = ker phi`. `H` embeds in `G` (Britton's lemma), so each
`H_k ≅ H`.

**Step 3: `H` finite.** Then `theta` is bijective, `C' = H`, `H_k = H = N` and `G = H ⋊ <t>`
with `[G : <t>] = |H|`. So `G` is VC, and `C = C' = H` is finite.

**Step 4: `H` infinite is impossible.** `G` is not VC by (V6), since `N ⊇ H` is infinite and
`G/N ≅ Z`. We show that `G` is virtually solvable, which contradicts
`virtually-solvable-bvc-groups-are-virtually-cyclic`.

- *A finite normal subgroup.* Put `F_k = F(H_k)` (V4). `H_k` is infinite of finite index in
  `H_{k+1}` (V1). Its image in `H_{k+1}/F_{k+1}`, which is `Z` or `D_∞`, is infinite and
  normalizes the finite image of `F_k`. By (V5) that image is trivial, so `F_k <= F_{k+1}`.
  Conjugation by `t^k` carries `H` onto `H_k` and `F(H)` onto `F_k`, so all `F_k` have the
  same order. So `F_k = F(H) =: L` for all `k`. `L` is normal in `H`, and `t^{-1} L t = F_1 = L`,
  so `L` is normal in `G`.
- *`G/L` is solvable.* Put `T_k = {1} ∪ {elements of infinite order in H_k/L}`. Since
  `H_k/L ≅ H/L` is `Z` or `D_∞` (V4), `T_k` is an infinite cyclic subgroup of index at most 2 in
  `H_k/L`. `T_k <= T_{k+1}`, so `M = ∪_k T_k` is an increasing union of infinite cyclic groups.
  It is abelian. `M = {1} ∪ {elements of infinite order in N/L}` is invariant under every
  automorphism of `N/L`, so `M` is normal in `G/L`. `M ∩ (H_k/L) = T_k` has index at most 2 in
  `H_k/L`, so at most two cosets of `M` meet each `H_k/L`, and `[N/L : M] <= 2`. The series
  `1 <= M <= N/L <= G/L` has abelian factors (`M`, order at most 2, `Z`), so `G/L` is solvable.
- By Lemma 0, `G` is virtually solvable. `∎`

## §5. Consequences and remarks

- **Corollary 1.** A group with BVC that is not VC admits no nontrivial one-edge splitting over
  a VC subgroup. In particular it is not a nontrivial amalgam or HNN extension over a finite
  subgroup. (It is not virtually free either. That follows from von Puttkamer–Wu Lemmas 1.10
  and 1.11, since a free group of rank at least 2, of any rank, is a nontrivial free product. It
  does not follow from Corollary 1 alone for groups that are not finitely generated.)
- **Corollary 2 (with `fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension`).** If a
  finitely presented BVC group `G` maps onto `Z` and is not VC, the ascending base `H` given by
  that claim is not VC. Otherwise `G` would split over the VC subgroup `H`.
- **Standard consequence, not used in any route.** For finitely generated `G`, Stallings'
  theorem (a finitely generated group with more than one end splits over a finite subgroup) and
  Corollary 1 show that a non-VC BVC group is one-ended. Stallings' theorem is quoted from
  memory, not re-verified this session.
- **Weakest points.**
  1. (CT) is used exactly as in the landed amalgam route: the cyclic-permutation-and-conjugation
     statement for cyclically reduced elements of length at least 2.
  2. The transfer evaluation in (V4) is textbook material, and only the special case of a
     central subgroup is used.
- **Literature overlap (checked by the referee on 2026-09-16 against the arXiv LaTeX sources
  of 1607.03790v2 and 1310.6289).** The theorem is not new. Every case follows, with no finite
  generation assumed, from published results plus the glue in §§0, 3 and 4:
  - *`D_a` finite for some `a`.* Then `C` is weakly malnormal in `G`. Minasyan–Osin
    (arXiv:1310.6289, Corollary 2.2, label `cor:amalg-intr`, imported as
    `fpbs-minasyan-osin-weakly-malnormal-splittings`) make `G` virtually cyclic or
    acylindrically hyperbolic. Their definition allows infinite generating sets. von
    Puttkamer–Wu Proposition 3.2 says acylindrically hyperbolic groups lack BVC, and its proof
    uses no finite generation.
  - *All `D_a` infinite.* Step 1 makes `A`, `B` VC and Step 2 builds `Z`. `G/Z` is an amalgam of
    finite groups over the finite, hence weakly malnormal, `C/Z`. By Minasyan–Osin it is VC or
    acylindrically hyperbolic, and von Puttkamer–Wu Corollary 3.4 (a group mapping onto an
    acylindrically hyperbolic group lacks BVC) rules out the second. So `G` is
    cyclic-by-VC, hence virtually polycyclic, and von Puttkamer–Wu Proposition 1.12 applies.
  - *HNN.* von Puttkamer–Wu Lemma 2.4 plus Proposition 1.12, as in §4. For non-ascending
    extensions, Minasyan–Osin Corollary 2.3 is another route.

  So the novelty here is only methodological. Lemmas 1, 2 and 4 replace the Minasyan–Osin
  acylindricity criterion by elementary normal-form counting. (The solver's earlier remark that
  the absence of finite generation was new is withdrawn.)
