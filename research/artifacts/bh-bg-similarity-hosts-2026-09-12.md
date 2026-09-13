# Baumslag--Gersten group: Thompson-like and Röver--Nekrashevych hosts

Lane `bh-bg-similarity-hosts`, 2026-09-12. This lane follows
`research/artifacts/bh-baumslag-gersten-2026-09-12.md` (commit c6d492eb1).

`BG = < a, t | b a b^-1 = a^2 >` with `b = t a t^-1`. `B = <a, b>` is
`BS(1,2)`, and `BG/<<a>> = Z`.

## 0. Results

| # | Statement | Status |
|---|---|---|
| T1 | Let `g, h` be almost automorphisms of `T_{d,r}` with `h g^k h^-1 = g^l`, where `k, l ≠ 0` and `|k| ≠ |l|`. Then `<g>` is equicontinuous. If `g` is in `V_{d,r}`, then `g` has finite order. | proved (§2–§4) |
| C1 | `BS(k,l)` with `|k| ≠ |l|` embeds in no Higman--Thompson group `V_{d,r}`. In particular it embeds in none of `V`, `T`, `F`. | proved (§4); also follows from arXiv:1107.0672 (§9) |
| T2 | If `BG` acts on a compact zero-dimensional metrizable space and `<a>` is equicontinuous, then `a` acts trivially. | proved (§5) |
| C2 | Every homomorphism from `BG` to an almost-automorphism group of `T_{d,r}` kills `a`. So `BG` embeds in no Röver--Nekrashevych group `V_{d,r}(G)`, for any self-similar `G`, and in no `V_{d,r}`. | proved (§6) |
| O | Brin--Thompson `nV`, twisted Brin--Thompson groups, and rational similarity groups. | open; only the restrictions in §7 apply |

The directive's premise that `BS(1,2)` embeds in `F` is false by C1.
`BS(1,2)` does embed in `PL_2(R)` via `x ↦ x+1` and `x ↦ 2x`, and in the
Röver--Nekrashevych group `V_3(G)` for the affine ternary group
`G = < x ↦ x+1, x ↦ 2x > ≤ Aut(T_3)` (c6d492eb1, item 3).

## 1. Setup

- **Space.** `Σ = {0,…,d-1}` with `d ≥ 2`, and `X = X_{d,r} = {1,…,r} × Σ^N`.
- **Words and cones.** A *word* `u` is a root together with a finite digit
  string. `|u|` is the number of digits. The *cone* is
  `C(u) = { u w : w ∈ Σ^N }`. Since `d ≥ 2`, a cone determines its word.
- **Metric.** `dist(x,y) = 2^-k` if `x, y` share a root and their longest common
  word has `k` digits, and `dist = 2` otherwise.
- **The almost-automorphism group.** `A_{d,r}` is the set of homeomorphisms `g`
  of `X` with two partitions `X = ⊔_i C(u_i) = ⊔_i C(v_i)` and tree
  automorphisms `g_i ∈ Aut(Σ^*)` such that `g(u_i w) = v_i g_i(w)`.
  - **Similarity.** Say that `g` *acts as a similarity on* `C(u)` if
    `g(u w) = v h(w)` for some word `v` and some `h ∈ Aut(Σ^*)`.
  - **Group.** Sections of tree automorphisms are tree automorphisms. So
    refining the partitions shows that `A_{d,r}` is a group.
  - **Subgroups.**
    - `V_{d,r}` (all `g_i = 1`), and so `T_{d,r}`, `F_{d,r}`, `V`, `T` and `F`.
    - The Röver--Nekrashevych group `V_{d,r}(G)`, for every self-similar
      `G ≤ Aut(Σ^*)`.
- **Table length.** `L(g)` is the maximum of all `|u_i|` and `|v_i|` over one
  fixed table. Every cone `C(q)` with `|q| ≥ L(g)` lies in some `C(u_i)`, so
  `g` acts as a similarity on it.

## 2. The exponent cocycle

**Definition.** For `x ∈ X`, choose a cone `C(u) ∋ x` on which `g` acts as
`u w ↦ v h(w)`, and set `δ_g(x) = |v| - |u|`.

**Well defined.**
- `h` is onto `Σ^N`, so `g(C(u)) = C(v)`, and `C(v)` determines `v`.
- Two such cones containing `x` are nested, say `C(us) ⊆ C(u)`. On `C(us)`,
  `g` acts as `u s w ↦ v h(s) h|_s(w)`, and the length difference is the same.

**Properties.**
- `δ_g` is locally constant and `|δ_g| ≤ L(g)`.
- **Cocycle.** `δ_{gh}(x) = δ_g(hx) + δ_h(x)`. To see this, compose the
  similarities on a small cone. It follows that `δ_{h^-1}(hx) = -δ_h(x)`.
- **Birkhoff sums.** For `m ≥ 0`, `S_m(g,x) := δ_{g^m}(x) = Σ_{j<m} δ_g(g^j x)`.

**Periodic exponent.** Let `x` have least period `p` under `g`. Set
`e_g(x) = δ_{g^p}(x)`, `ρ_g(x) = e_g(x)/p ∈ [-L(g), L(g)]`, and
`R(g) = { ρ_g(x) : x periodic }`.

**Lemma 2.1.**
- (i) `R(h g h^-1) = R(g)` for `h ∈ A_{d,r}`.
- (ii) `R(g^m) = m R(g)` for `m ≠ 0`.
- (iii) If `h g^k h^-1 = g^l` with `k, l ≠ 0` and `|k| ≠ |l|`, then
  `R(g) ⊆ {0}`.

*Proof.*
- (i) `h` carries periodic orbits of `g` bijectively to those of `hgh^-1`, and
  the cocycle gives
  `δ_{h g^p h^-1}(hx) = δ_h(x) + e_g(x) + δ_{h^-1}(hx) = e_g(x)`.
- (ii) Every periodic point of `g^m` is periodic for `g`. If `x` has least
  period `p` for `g`, its least period for `g^m` is `q = p/gcd(p,m)`. Then
  `(g^m)^q = (g^p)^{mq/p}`. At the fixed point `x` of `g^p`, the cocycle gives
  `δ_{(g^p)^j}(x) = j e_g(x)` for all `j ∈ Z`. So `ρ_{g^m}(x) = m ρ_g(x)`.
- (iii) By (i) and (ii), `k R(g) = l R(g)`. Say `|k| < |l|`, and suppose
  `s = sup |R(g)| > 0`. This is finite by the bound `|ρ| ≤ L(g)`. Pick
  `ρ ∈ R(g)` with `|ρ| > s|k|/|l|`. Then `lρ = kρ'` for some `ρ' ∈ R(g)` with
  `|ρ'| > s`, a contradiction. ∎

## 3. Reading length and pumping

Fix `g ∈ A_{d,r}` and write `L = L(g)` and `S_m = S_m(g, ·)`. Let `ℓ_m(x)` be
the least `|u|` over cones `C(u) ∋ x` on which `g^m` acts as a similarity.

**Lemma 3.1.** `ℓ_m(x) ≤ max(0, max_{0≤j<m} (L - S_j(x)))`.

*Proof.* We have `ℓ_0 = 0`. Suppose `g^m` acts on `C(u) ∋ x` as
`u w ↦ p h(w)`, with `|u| = ℓ_m(x)` and `|p| = |u| + S_m(x)`.
- If `|p| ≥ L`, then `g` acts as a similarity on `C(p)`, so `g^{m+1}` does on
  `C(u)`.
- If `|p| < L`, let `s` be the next `L - |p|` digits of `x` after `u`. Then
  `g^m(C(us)) = C(p h(s))`, a cone of length `L`, so `g^{m+1}` acts as a
  similarity on `C(us)`. The section `h|_s` is again a tree automorphism.

So `ℓ_{m+1}(x) ≤ max(ℓ_m(x), L - S_m(x))`, and induction finishes the proof. ∎

**Lemma 3.2 (pumping).** If `sup { S_m(x) : x ∈ X, m ≥ 0 } = ∞`, then `g` has
a periodic point `z` with `e_g(z) > 0`.

*Proof.*
- **Setup.** Pick `x` and `M` with `S_M(x) - min_{k≤M} S_k(x) ≥ L(r d^L + 2)`,
  and let `m_0 = min_{k≤M} S_k(x)`. For each level `h` with
  `m_0 ≤ h < S_M(x)`, let `τ_h = max { k ≤ M : S_k(x) ≤ h }`.
- **Record times.** Then `τ_h < M` and `S_k(x) > h` for `τ_h < k ≤ M`. Also
  `S_{τ_h}(x) > h - L`, since one step changes `S` by at most `L`.
- **Two levels in the same state.** Take the levels `h_i = m_0 + iL` with
  `h_i < S_M(x)`. There are at least `r d^L + 1` of them. Let
  `y_i = g^{τ_{h_i}} x`. By pigeonhole there are `i < i'` with
  `y_i|_L = y_{i'}|_L =: q`, where `y|_L` denotes the word of `y` with `L`
  digits.
- **The two times differ.** `S_{τ_{h_{i'}}}(x) > h_{i'} - L ≥ h_i ≥ S_{τ_{h_i}}(x)`.
  So `τ := τ_{h_i} < τ' := τ_{h_{i'}}`, and
  `Δ := S_{τ'}(x) - S_τ(x) ≥ 1`.
- **Similarity on `C(q)`.** For `0 ≤ j ≤ M - τ`,
  `S_j(g, y_i) = S_{τ+j}(x) - S_τ(x) ≥ 0`. With `D = τ' - τ`, Lemma 3.1 gives
  `ℓ_D(y_i) ≤ L`. So `g^D` acts on `C(q)` as `q w ↦ p h(w)` with
  `|p| = L + Δ > L`.
- **Shape of `p`.** `p` is a prefix of `g^D y_i = y_{i'}`, which begins with
  `q`. So `p = q c` with `|c| = Δ ≥ 1`.
- **Fixed point.** `w ↦ c h(w)` is a `2^-Δ`-contraction of `Σ^N`, because `h`
  is an isometry. It has a fixed point `w*`. Then `z = q w*` satisfies
  `g^D z = z` and `δ_{g^D}(z) = Δ > 0`. So `z` is periodic, with period `p'`
  dividing `D`, and `e_g(z) = (p'/D)·Δ > 0`. ∎

## 4. Elements conjugate to proper powers

**Proposition 4.1.** Let `g ∈ A_{d,r}` with `R(g) ⊆ {0}`. Then there are `N`
and `K` such that for every `m ∈ Z` and every word `q` with `|q| = N`, `g^m`
acts on `C(q)` as `q w ↦ p h(w)` with `||p| - N| ≤ K`. Consequently:
- (a) every `g^m` is `2^K`-Lipschitz on each level-`N` cone, so `<g>` is
  equicontinuous;
- (b) some `g^k` with `k ≥ 1` fixes every level-`N` cone and acts on each of
  them by a tree automorphism;
- (c) if `g ∈ V_{d,r}`, then `g` has finite order.

*Proof.*
- **Bounded sums.** Since `e_{g^-1} = -e_g`, neither `g` nor `g^-1` has a
  periodic point of positive exponent. By Lemma 3.2 applied to both,
  `S_m(g,·)` and `S_m(g^-1,·)` are bounded above for `m ≥ 0`. Since
  `S_m(g^-1, x) = -S_m(g, g^-m x)`, there is `K` with `|S_m(g^{±1}, ·)| ≤ K`
  for all `m ≥ 0`.
- **Levels.** Lemma 3.1, applied to `g` and to `g^-1`, gives `ℓ_m ≤ N` for all
  `m ∈ Z`, where `N = max(L(g), L(g^-1)) + K`. The image word has length
  `N + δ_{g^m}(x) ∈ [N-K, N+K]`.
- **(a)** If `dist(x,y) < 2^-N`, then `x = qw` and `y = qw'` with `|q| = N`, and
  `dist(g^m x, g^m y) = 2^{N-|p|} dist(x,y) ≤ 2^K dist(x,y)`.
- **(b)** The cones `g^m C(q)`, for `m ∈ Z` and `|q| = N`, have lengths in
  `[N-K, N+K]`. So they form a finite set, which `g` permutes. Some `g^k`
  fixes each of them. `g^k C(q) = C(q)` forces `p = q`.
- **(c)** Let `g ∈ V_{d,r}`, and let `n = L(g^k)`.
  - On a cone `C(q s)` with `|s| ≥ n`, `g^k` replaces a prefix and has trivial
    section.
  - So on each level-`N` cone, `g^k` acts as `q w ↦ q h_q(w)`, where `h_q` is a
    tree automorphism whose sections at depth `n` are trivial.
  - Such automorphisms form a finite group, and `g^{kj}` acts on `C(q)` by
    `h_q^j`.
  - There are finitely many level-`N` cones, so `g^k` has finite order, and
    hence so does `g`. ∎

**Theorem 4.2 (T1).** Let `h g^k h^-1 = g^l` in `A_{d,r}`, with `k, l ≠ 0` and
`|k| ≠ |l|`. Then (a)–(c) of Proposition 4.1 hold for `g`. This follows from
Lemma 2.1(iii).

**Corollary 4.3 (C1).** In `BS(k,l) = < s, u | u s^k u^-1 = s^l >`, the element
`s` has infinite order. So if `|k| ≠ |l|`, no homomorphism
`BS(k,l) → V_{d,r}` is injective, and every such homomorphism sends `s` to an
element of finite order. Since `F ≤ T ≤ V = V_{2,1}`, this covers `V`, `T` and
`F`.

## 5. Equicontinuous `a` acts trivially

**Theorem 5.1 (T2).** Let `BG` act by homeomorphisms on a compact
zero-dimensional metrizable space `X`, with `{a^m : m ∈ Z}` equicontinuous.
Then `a` acts trivially.

*Proof.*
- **Step 0 (topology).**
  - `Homeo(X)`, with the uniform topology, is a topological group.
  - Because `X` is zero-dimensional, stabilizers of finite clopen partitions
    form a neighbourhood basis of open subgroups at `1`. So every compact
    subgroup of `Homeo(X)` is profinite.
  - By Arzelà--Ascoli, applied to `a^m` and `a^-m` together, the closure `K` of
    `<a>` is compact. So `K` is a procyclic profinite group.
  - Conjugation by `t` carries `K` onto `K_b := closure of <b>`, so
    `K_b ≅ K` as topological groups.
  - Let `P` be the set of primes `p` for which `K` has a continuous quotient
    `Z/p`. If `K ≠ 1` then `P ≠ ∅`.
  - For each index `m` that occurs, `K` has a unique open subgroup
    `U_m = closure of <a^m>` of index `m`.
- **Step 1 (`2 ∉ P`).**
  - Suppose `2 ∈ P`. Since `U_2` is open in `K`, there is an open set
    `O ∋ 1` in `Homeo(X)` with `O ∩ K ⊆ U_2`.
  - The set `W = { k ∈ K_b : k a k^-1 a^-1 ∈ O }` is an open neighbourhood of
    `1` in `K_b`.
  - `K_b` is a compact group, so `b^j ∈ W` for some `j ≥ 1`.
  - But `b^j a b^-j a^-1 = a^{2^j - 1}` lies in `K`, and hence in
    `O ∩ K ⊆ U_2`.
  - `K/U_2 = Z/2` is generated by the image of `a`, and `2^j - 1` is odd. So
    this is false.
- **Step 2 (`K_b` normalizes each `U_m`).**
  - The index of `closure <a^{2m}>` is the part of `2m` that occurs as an
    index. Since `2 ∉ P`, that part is `m`.
  - So `b U_m b^-1 = closure <a^{2m}> = U_m`, and in particular `b K b^-1 = K`.
  - By continuity, `K_b` normalizes `K` and every `U_m`.
- **Step 3 (smallest prime).**
  - Suppose `K ≠ 1`, and let `p = min P`. Then `p` is odd.
  - Conjugation gives a homomorphism `ψ : K_b → Aut(K/U_p) = (Z/p)^×`. Its
    kernel is `{ k : k a k^-1 a^-1 ∈ U_p }`.
  - By Step 2 the commutator lies in `K`, and `U_p` is open in `K`. So the
    kernel is open, and `ψ` is continuous.
  - `ψ(b) = 2`, and `<b>` is dense, so the image is `<2 mod p>`, of order
    `o = ord_p(2) ≥ 2`.
  - So `K_b ≅ K` has a continuous quotient `Z/o`, and every prime `q | o` lies
    in `P`.
  - But `o | p - 1`, so `q < p`, contradicting minimality. Hence `K = 1`. ∎

**Remarks.**
- Taking `X` finite recovers "every finite image of `BG` kills `a`"
  (c6d492eb1, §1).
- Zero-dimensionality is used only to make `K` profinite.
  `baumslag-gersten-odometer-pieces-force-fixed-points` handles minimal
  equicontinuous `a` on arbitrary compact metrizable spaces.
- Without `t`, the statement fails. In the affine ternary model of `BS(1,2)`,
  `K = Z_3` and `K_b = Z_3^×`, and these have different prime sets.

## 6. The Baumslag--Gersten obstruction

**Corollary 6.1 (C2).** Every homomorphism `φ : BG → A_{d,r}` has
`φ(a) = 1`, so it factors through `BG/<<a>> = Z`. Hence `BG` embeds in none of
the following:
- any Röver--Nekrashevych group `V_{d,r}(G)`, for any self-similar
  `G ≤ Aut(T_d)`, contracting or not;
- any Higman--Thompson group `V_{d,r}`;
- `V`, `T` or `F`;
- any other subgroup of `A_{d,r}`.

*Proof.* Let `g = φ(a)` and `h = φ(b)`. Then `h g h^-1 = g^2`, so by
Theorem 4.2 `<g>` is equicontinuous on the Cantor space `X_{d,r}`. Now
Theorem 5.1, applied to the action through `φ`, gives `g = 1`. ∎

**Consequence for the host table of c6d492eb1.**
- "Röver--Nekrashevych hosts (open)" becomes **dead**.
- "Thompson-like groups `V`, `V_{n,r}`" become **dead**.
- Some groups act on a full shift by maps that are eventually similarities with
  tree-automorphism sections. These lie in `A_{d,r}`, so they are dead too.
- Not covered: the eventually-similar groups of
  `fw-subgroups-of-eventually-similar-groups-virtually-embed` over shifts of
  finite type with several cone types, and those with non-isometric local
  groupoids.

## 7. What is not covered

- **Every Cantor-space host.** By Theorem 5.1, any embedding of `BG` into a
  group of homeomorphisms of a Cantor space sends `a` to a non-equicontinuous
  element.
- **Brin--Thompson `nV`.**
  - *What still holds.* The cocycle `δ` takes values in `Z^n`, one coordinate
    per factor, and Lemma 2.1 holds verbatim. So in any embedding
    `BG → nV`, every periodic orbit of `φ(a)` has exponent vector `0`, and
    `φ(a)` is not equicontinuous.
  - *What still holds of the pumping argument.* Lemma 3.1 holds
    coordinatewise, because a cube whose sides all have at least `L` digits
    lies in a table cube.
  - *Where the proof breaks.* The pigeonhole in Lemma 3.2 fails.
    - Along the record times of one coordinate, the Birkhoff sum of another
      coordinate can fall without bound. The baker's map
      `(x w_1, w_2) ↦ (w_1, x w_2)` does this.
    - The prefixes that must agree in that coordinate then grow without bound.
  - *Status.* No construction of `BS(1,2)` in `2V` was found. Whether `BG`
    embeds in some `nV` is **OPEN**.
- **Twisted Brin--Thompson `SV_G` (type (A) hosts).** Same restrictions as for
  `nV`. **OPEN.**
- **Rational similarity groups (BBMZ).** Sections are rational homeomorphisms,
  not isometries. So the contraction step of Lemma 3.2 and the Lipschitz step
  of Proposition 4.1 both fail. **OPEN.**
- **Stein--Higman--Thompson groups with several arities.** Not treated.

## 8. Graph status

`baumslag-gersten-group-satisfies-boone-higman` stays **OPEN**. This lane
removes one host class and adds three established claims:
- `almost-automorphism-conjugate-to-proper-power-is-equicontinuous` (T1 with C1);
- `baumslag-gersten-equicontinuous-generator-acts-trivially` (T2);
- `baumslag-gersten-embeds-in-no-rover-nekrashevych-group` (C2).

`boone-higman-conjecture` is untouched.

## 9. Sources checked

- **C. Bleak, H. Bowman, A. Gordon, G. Graham, J. Hughes, F. Matucci,
  J. Sapir, "Centralizers in R. Thompson's group V_n", arXiv:1107.0672.**
  - *What the source says.* The arXiv abstract page was fetched on MSI on
    2026-09-12. The abstract says it uses "revealing tree pairs as developed by
    Brin and Salazar". It also says: "we give a short argument using revealing
    tree pairs which shows that cyclic groups are undistorted in V_n."
  - *Why C1 follows for `V_n`.* In `BS(k,l)` with `|k| ≠ |l|`, the element
    `s^{l^j} = u^j s^{k^j} u^-j` has length at most `2j + |k|^j`. So `<s>` is
    distorted, and an injective image in the finitely generated group `V_n`
    would be distorted too.
  - *Why C1 follows for `V_{n,r}`.* `V_{n,r}` is isomorphic to `V_{n,s}` for
    some `s` with `1 ≤ s ≤ n-1`. That group embeds in `V_{n,1}`: act on `s`
    disjoint level-1 cones, and by the identity elsewhere.
  - *What is not in the abstract.* The finite-order conclusion of
    Proposition 4.1(c), and the extension to tree-automorphism sections that
    C2 needs.
- **arXiv searches on MSI.** The export API returned HTTP 429, and the HTML
  search pages gave no parsable hits. No source was found that states T2 or C2.
  No novelty is claimed for any item.
