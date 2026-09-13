# Infinite simple Kazhdan groups and hyperlinearity: inventory, and an independent check of the subshift answer to Pestov 9.1

Lane `isk-hyperlinear-kazhdan`, 2026-09-12. Read at main `3c481f496`.

## 0. Outcome

- **Main already has the answer.** `S = EL_3(LC(X,F_q) ⋊ Z)/Z(G)` is an infinite simple Kazhdan
  group that is LEF, hence sofic and hyperlinear. The nodes are
  `simple-kazhdan-lef-group-from-minimal-subshift` and its ingredients, from lane
  `ex-kazhdan-simple-hyperlinear` (commits f375478c7, 56bdeb8d3, 41e82567c). The EX review passed
  them at 0efeac410.
- **This lane reached the same group independently.** It derived the construction and both main
  steps before reading Part 1 of that lane's artifact.
  - The LEF proof here uses a different mechanism (§3): `G` is a marked limit of residually finite
    groups `EL_n(LC(Y_L,F_q) ⋊ Z)` over periodic closures of `X`. Part 1 instead embeds the ring
    unitally in a matrix ultraproduct.
  - The simplicity proof (§4) is a separate write-up of root detection by tower localization.
  - Both agree with Part 1 §1–§4 and with the review. No gap was found in Part 1 §1–§4.
- **Graph status: the root is still OPEN.** The route
  `simple-kazhdan-hyperlinear-from-subshift-elementary-group` requires
  `simple-kazhdan-lef-group-from-minimal-subshift`. That claim has no proof route yet; this is the
  "combining route" the review says may now be landed. Section 7 records `cairn why`.
- **The fp root is untouched.** `hyperlinear-fp-infinite-simple-group` cannot be answered by `S`,
  or through any LEF mechanism (§6).

## 1. Inventory of infinite simple Kazhdan groups

| Family | Finitely presented | Sofic / hyperlinear | Nodes in main |
|---|---|---|---|
| Centre-free Kac–Moody lattices over large finite fields (Caprace–Rémy simplicity, Dymara–Januszkiewicz (T)) | yes | Unknown. Proved dichotomy: non-hyperlinear, or the full C*-algebra fails LLP | `simple-kazhdan-kac-moody-lattices-exist`, `kac-moody-lattice-is-non-hyperlinear-or-llp-failure` |
| Infinite simple quotients of hyperbolic Kazhdan groups | not tracked | Unknown; no approximation mechanism is known | None. `caprace-kassabov-hyperbolic-kazhdan-alternating-quotients` covers alternating quotients only |
| The binary Leavitt unit group `Q`, identified with `EL_n(L_(F_2)(1,2))` by `leavitt-gl-equals-el-and-perfect-unit-group` | not needed here | Nonsofic; hyperlinear is OPEN | `binary-leavitt-elementary-group-is-simple`, `openai-leavitt-unit-nonsofic`, `binary-leavitt-unit-group-hyperlinear` |
| `S = EL_3(LC(X,F_q) ⋊ Z)/Z(G)` | no (§6) | LEF, so sofic and hyperlinear | `simple-kazhdan-lef-group-from-minimal-subshift` and ingredients |

Notes on the rows:

- **Hyperbolic quotients.** Quotients of Kazhdan groups are Kazhdan, so any infinite simple quotient
  of a hyperbolic Kazhdan group qualifies. Such quotients are obtained by small cancellation over
  hyperbolic groups. This lane did not re-read a source for them.
- **EJZ hypotheses** (Ershov–Jaikin-Zapirain, Theorem 1.1): `R` is an associative ring with 1, finitely
  generated as a ring, and `n ≥ 3`. Then `EL_n(R)` has (T). EJZ says nothing about simplicity, which
  has to be proved ring by ring.
  - For the subshift ring, a generating set is `u`, `u^(-1)`, the letter cylinders, and a generator
    of `F_q` over `F_p` (§2 (F2)). The last is needed when `q = p^e` with `e > 1`; this is the
    review's wording note.

**Does main contain an infinite simple Kazhdan group?** Yes, three: the Kac–Moody lattices (an
import), the Leavitt elementary group, and `S`.

**Best candidate for 9.1: `S`.** It is the only one with a known finite approximation. The other two
are blocked:

- A Kac–Moody lattice is finitely presented, so it is never LEF: f.p. plus LEF gives residual
  finiteness, which an infinite simple group lacks.
- The Leavitt group is closed to every ring-level matrix approximation (§5, Remark).

## 2. The group and the ring facts used

Setup:

- `A` is a finite alphabet, `X ⊆ A^Z` an infinite minimal subshift, and `T` the shift.
- `R = LC(X,F_q) ⋊ Z` consists of finite sums `sum_j f_j u^j`, with `u f u^(-1) = f∘T^(-1)`.
- `G = EL_n(R)` with `n ≥ 3`, `Z(G)` its centre, and `S = G/Z(G)`.

The ring facts:

- **(F1) Freeness and long returns.** A periodic orbit is closed and invariant, so it would equal `X`,
  which is infinite. So `T` is free. Given `M`, every point has a clopen neighbourhood `W` with
  `T^k W ∩ W = ∅` for `0 < |k| ≤ M`. Every clopen set is a finite disjoint union of such `W`.
- **(F2) Generation.** `u^i χ_[a] u^(-i) = χ_[a]∘T^(-i)`. Products of these give every cylinder, and
  sums with `F_q` coefficients give every locally constant function.
- **(F3) `R` is simple and `Z(R) = F_q`.**
  - *Simplicity.* Let `r = sum_{|j|≤D} f_j u^j` be a nonzero element of an ideal `I`, with
    `f_j(x) ≠ 0`. Choose `W ∋ x` with return time `> 2D`, on which `f_j` equals a constant `a ≠ 0`.
    Then `χ_W r χ_(T^(-j)W) = a χ_W u^j`, so `χ_W ∈ I`, and hence every `χ_(T^k W) ∈ I`.
    By minimality and compactness, finitely many `T^k W` cover `X`. Inclusion–exclusion
    (`χ_(A∪B) = χ_A + χ_B − χ_A χ_B`) then puts `1` in `I`.
  - *Centre.* A central `sum f_i u^i` commutes with every `χ_V`, which forces `f_i = 0` for `i ≠ 0`
    by freeness. It commutes with `u`, which forces `f_0` to be `T`-invariant, hence constant by
    minimality.
- **(F4) Generators of `EL_n(R)`.** It is generated by `e_ij(s)` for `i ≠ j` and `s` in a ring
  generating set. The set `{r : e_ij(r) ∈ H for all i ≠ j}` is closed under `+`, and under `·` by
  `[e_ij(r), e_jk(s)] = e_ik(rs)`.
- **(F5) The centre of `G`.** If `g` commutes with every `e_ij(r)`, then comparing entries gives
  `g_(ki) = 0` for `k ≠ i` and `g_ii r = r g_jj`. So `g = zI` with `z ∈ Z(R)^× = F_q^×`, and
  `Z(G) = G ∩ F_q^× I = ΛI` for a finite group `Λ`.

## 3. LEF by periodic truncation

This is the mechanism of Grigorchuk–Medynets for topological full groups, lifted to rings. The
credit note is in review §1.7.

**Lemma 3.1 (periodic closure).** Let `X_L ⊆ A^Z` be the subshift of finite type of points whose
`L`-windows all lie in `L_L(X)`, and `Y_L` the closure of the periodic points of `X_L`. Then:

- `X ⊆ Y_L`;
- `L_ℓ(Y_L) = L_ℓ(X)` for `ℓ ≤ L`.

*Proof.*
- *Containment.* Take `x ∈ X` and a window `x_[−N,N]`. By uniform recurrence the `L`-word
  `x_[−N,−N+L−1]` recurs at some position `b > N`. The periodic point with period block `x_[−N,b−1]`
  has every `L`-window inside `x_[−N,b+L−1]`, so it lies in `X_L`. It agrees with `x` on
  `[−N,N]`.
- *Languages.* The inclusion `⊇` follows from the containment. For `⊆`, every point of `X_L` has all
  its `L`-windows, and hence all shorter windows, in the language of `X`. ∎

**Lemma 3.2 (residually finite approximants).** `R_L := LC(Y_L,F_q) ⋊ Z` is a residually finite ring.
Hence `GL_n(R_L)` and `G_L := EL_n(R_L)` are residually finite, and so is `G_L/(G_L ∩ ΛI)`.

*Proof.* Let `y ∈ Y_L` be periodic with period `p`, and let `N ≥ 1`. Define
`π_(y,N) : R_L → End(F_q^(Z/pN)) = M_pN(F_q)` by `(fφ)(k) = f(T^k y)φ(k)` and
`(uφ)(k) = φ(k−1)`.

- *Ring homomorphism.* Both sides of `u f = (f∘T^(-1)) u` send `φ` to `k ↦ f(T^(k−1)y)φ(k−1)`.
- *Separation.* Let `r = sum_{|j|≤m} f_j u^j` have `f_j ≠ 0`. The open set `{f_j ≠ 0}` contains a
  periodic `y`, because periodic points are dense in `Y_L`. Take `pN > 2m`. The value of
  `π(r)δ_(−j)` at `0` is `f_j(y) ≠ 0`.
- *Why the cyclic cover.* `Y_L` can have isolated points of small period. At a fixed point `y`, the
  element `χ_{y}(1−u)` is nonzero but dies on the orbit itself. The cover `Z/pN` separates it.
- *Groups.* A finite product of such maps keeps any finite set of nonzero ring elements nonzero.
  - For `g ≠ I`, keep an entry of `g − I`.
  - Modulo the finite central group `ΛI`, keep `g − λI` for every `λ ∈ Λ`. ∎

**Lemma 3.3 (marked convergence).** Let `R_L` and `R` carry the same generators: `u`, `u^(-1)`,
`χ_[a]`, and a generator of `F_q`. Restriction `f ↦ f|_X` is a ring homomorphism `R_L → R` that
fixes the generators, so it induces marked epimorphisms `G_L → G` and `S_L → S`, where
`S_L := G_L/(G_L ∩ ΛI)`. If `L ≥ 2ℓ+1`, a word of length `ℓ` in the generators is trivial in `G`
exactly when it is trivial in `G_L`. The same holds for "equals `λI`".

*Proof.* Every entry of `w − I` has the form `sum_{|j|≤ℓ} F_j u^j`. Each `F_j` is a fixed polynomial
in the functions `χ_[a]∘T^t` with `|t| ≤ ℓ`, the same over `X` and over `Y_L`. So `F_j` depends only
on the window `y_[−ℓ,ℓ]`. It vanishes on `X` iff it vanishes on `L_(2ℓ+1)(X)`, and that equals
`L_(2ℓ+1)(Y_L)` by Lemma 3.1. ∎

**Theorem 3.4.** `G` and `S` are LEF.

*Proof.* A marked limit of residually finite groups is a marked limit of finite groups. Given a
radius, pick `L` by Lemma 3.3, then a finite quotient of `G_L` (or `S_L`) that is injective on a
larger ball. LEF for finitely generated groups is exactly being such a limit. ∎

**Comparison with Part 1 §3.** Part 1 builds one finite representation `R → M_(N_k)(F_q)` per `k`,
from a periodic word `w_k` whose cyclic windows are exactly `L_(2k+1)(X)`, and gets a unital
ultraproduct embedding. Here the approximants are the infinite residually finite rings `R_L`. Both
give LEF.

This lane did not re-derive the marked-limit-of-`PSL_(3N_k)(F_q)` clause of the claim (Part 2
§8.1). That clause needs the representations to generate all of `M_(N_k)(F_q)`.

## 4. Simplicity modulo the centre, by tower localization

Let `N ⊴ G` be noncentral. Pick a noncentral `g ∈ N`, and let `K` bound the `u`-degrees of the
entries of `g` and `g^(-1)`.

**Step 1: a localized root that does not commute with `g`.** The set of `r` for which `g` commutes
with every `e_ij(r)` is closed under `+` and `·` (F4). Suppose it contained `λχ_W u^ε` for every
`λ ∈ F_q`, `ε ∈ {−1,0,1}` and clopen `W` with return time `> 4K+5`. By (F1) and (F2) it would be all
of `R`, and `g` would be central. So some `h = e_ij(s)` with `s = λχ_W u^ε` gives
`c = [g,h] ∈ N`, `c ≠ 1`.

**Step 2: `c` lives in a tower.** Set `Ω = ⋃_{|k|≤K+1} T^k W` and `p = χ_Ω`.

- The entries of `ghg^(-1) − I` are `g_(ai) s (g^(-1))_(jb)`. Their terms `f u^t` satisfy
  `supp f ⊆ Ω ∩ T^t Ω`. The same holds for the entries of `h^(-1) − I` and for products, so every
  entry of `c − I` lies in `pRp` and has `u`-degree `≤ 2K+3`.
- For such a term, `χ_(T^k W) f u^t χ_(T^l W) = 0` unless `k = l + t`, since
  `|k − l − t| ≤ 4K+5` is below the return time.
- Put `m = 2K+3` and define `J : M_m(LC(W,F_q)) → pRp` by `J(φ) = sum_{k,l} u^k φ_kl u^(−l)`, with
  `k, l ∈ [−K−1, K+1]`. It is an injective unital ring homomorphism, because
  `χ_W u^t χ_W = 0` for `0 < |t| ≤ 2K+2`.
- Hence `c = I + J_n(Φ − I)` for a locally constant `Φ : W → GL_(nm)(F_q)`. Invertibility holds
  because `c^(-1) = [h,g]` has the same form.

**Step 3: local copies of `SL`.** For clopen `V ⊆ W`, the map `J_V(A) = I + J_n((A − I)χ_V)` is an
injective homomorphism `SL_(nm)(F_q) → G`.

- An elementary matrix between different colours goes to `e_ij(λ u^k χ_V u^(−l))`.
- One within a colour is a commutator through another colour.

**Step 4: root detection.** Pick `V ⊆ W` on which `Φ ≡ A ≠ I`. Then
`[J_V(B), c] = J_V([B,A]) ∈ N` for every `B`.

- **(a) `A` is not scalar.** Suppose every `[B,A]` were central. Then `A B A^(-1) = λ(B) B` for a
  homomorphism `λ : SL_(nm)(F_q) → F_q^×`. Perfectness kills `λ`, so `A` would centralize
  `SL_(nm)(F_q)` and be scalar. So `N ∩ J_V(SL_(nm)(F_q))` contains a noncentral element and is
  normal in `J_V(SL_(nm)(F_q))`. Since `nm ≥ 3`, `PSL_(nm)(F_q)` is simple and `SL_(nm)(F_q)` is
  perfect, so the intersection is everything. In particular
  `e_12(χ_V) = J_V(I + E_((1,0),(2,0))) ∈ N`.
- **(b) Every value of `Φ` is scalar.** Take `V` with `Φ|_V ≡ μI`, `μ ≠ 1`, and put
  `x = χ_V u^(2K+3)`.
  - Its right support is `T^(−2K−3)V`, which is disjoint from `Ω`: every level shift `2K+3+k`, for
    `|k| ≤ K+1`, is nonzero and below the return time.
  - Its left support is `V` at level 0.
  - So `J(ψ)x = sum_k u^k ψ_k0 χ_V u^(2K+3)`, which gives `c(x e_12) = μ x e_12` and
    `(x e_12)c^(-1) = x e_12`.
  - Therefore `[c, e_12(x)] = e_12((μ−1)x) ∈ N`, and `(μ−1)x ≠ 0`.

**Step 5: the level ideal.** `I(N) = {r : e_12(r) ∈ N}` is a two-sided ideal:

- `[e_12(r), e_23(s)] = e_13(rs)` and `[e_13(rs), e_32(1)] = e_12(rs)`;
- `[e_31(s), e_12(r)] = e_32(sr)` and `[e_13(1), e_32(sr)] = e_12(sr)`.

By Step 4 it is nonzero, so `I(N) = R` by (F3). The same identities give every `e_ij(R) ⊆ N`, so
`N = G`.

**Conclusion.** Every normal subgroup of `G` is central or `G`. So `S` is simple. It is infinite,
because `e_12(R)` meets `ΛI` trivially. `G` has no nontrivial finite quotient, since a finite-index
normal subgroup is noncentral. With EJZ (§1), `S` is an infinite simple Kazhdan LEF group.

This matches Part 1 §4: the tower subrings `B_m(U)`, Cases 1 and 2, and the level ideal. Step 4(b)
is Part 1's scalar case. Here the column leaves the tower on the right, where Part 1 uses
`χ_(T^(m'+1)W)u`. Both are valid.

## 5. Relation to the non-hyperlinear chain

- **What the chain is about.** The chain in main (5c0603721, 1d9a1ceda, 44267adad) is about the
  binary Leavitt unit group `Q`. Its nodes:
  - `kun-thom-wreath-embeds-in-leavitt-unit-group` and
    `leavitt-nonhyperlinear-via-kun-thom-wreath-embedding`;
  - `leavitt-pair-vertex-rounding-is-nonhyperlinearity`, which says vertex rounding for the
    nine-leaf Leavitt pair is exactly nonhyperlinearity of `Q`;
  - `theorem-e-congruence-projections-vanish-at-regular-trace`;
  - the `K_i` results over `F_q[x_1..x_d]`: `mixed-level-root-group-is-kazhdan-in-rank-at-least-five`
    and `mixed-level-root-group-is-not-kazhdan-in-rank-four`.
- **`S` is disjoint from it.** `S` is sofic, and subgroups of sofic groups are sofic, so neither `Q`
  nor any nonsofic group embeds in `S`. `S` gets (T) directly from EJZ and does not use the `K_i`
  results. No node of the chain bears on `S`, and `S` bears on none of them.
- **What each outcome would mean.** Nonhyperlinearity of `Q` would show that not every infinite
  simple Kazhdan group is hyperlinear. It would not change the answer to 9.1, which asks for one.
  Hyperlinearity of `Q` would give a second answer, through
  `simple-kazhdan-hyperlinear-from-leavitt-unit-group`.

**Remark (a ring-level obstruction for `Q`).** `L_K(1,2)` has no unital homomorphism into any ring
with a Sylvester rank function normalized by `rk(1) = 1`. In particular it has none into
`prod_ω M_N(F)` with normalized rank.

*Proof.* The Leavitt relations give `y_i x_j = δ_ij` and `x_1 y_1 + x_2 y_2 = 1`. Put `e_i = x_i y_i`,
orthogonal idempotents with `e_1 + e_2 = 1`. Then `rk(1) = rk(e_1) + rk(e_2)`. Also
`1 = y_i x_i y_i x_i`, so `rk(1) ≤ rk(e_i) ≤ rk(1)`. This gives `1 = 2`. ∎

So neither §3 nor Part 1 §3 can reach `Q`. Hyperlinearity of `Q` needs a mechanism that is not
exactly multiplicative at the ring level.

## 6. What stays open

- **Root `infinite-simple-kazhdan-hyperlinear-group`.** Answered by `S`. The review passed at
  0efeac410, and this lane's derivation agrees. Lane `ex-kazhdan-simple-hyperlinear` landed the
  combining route `simple-kazhdan-lef-group-from-minimal-subshift-proof` at 8b65f0932. That route
  should establish the claim, and through `simple-kazhdan-hyperlinear-from-subshift-elementary-group`
  the root (§7).
- **Fp root `hyperlinear-fp-infinite-simple-group`.** `S` is not finitely presented, since f.p. plus
  LEF gives residual finiteness and infinite simple groups are not residually finite. The same
  argument rules out every route that makes a finitely presented group a marked limit of finite
  groups. An answer needs a hyperlinear, non-LEF, finitely presented infinite simple group. The
  Kac–Moody lattices are the Kazhdan candidates in main, and only the dichotomy node constrains
  them.
- **`simple-kazhdan-groups-have-full-mf-radical` (SKM1).** `S` is an infinite simple Kazhdan group
  that is operator MF, by `lef-implies-operator-mf`. 8b65f0932 adds
  `refuted_by: [simple-kazhdan-lef-group-from-minimal-subshift]` to SKM1, so SKM1 becomes REFUTED
  once the claim is established.
- **Hyperlinearity of `Q`.** OPEN, and outside every finite-ring mechanism by the Remark in §5.

## 7. Cairn status

**At main 3c481f496, before 8b65f0932.** MSI job `cairn-a` ran `check` (rc 0, 0 errors) and `why`.

- Both roots were OPEN.
- `simple-kazhdan-lef-group-from-minimal-subshift` was OPEN, with no live routes into it. `why`
  reported: "if established: completes simple-kazhdan-hyperlinear-from-subshift-elementary-group ->
  infinite-simple-kazhdan-hyperlinear-group".
- ESTABLISHED: `subshift-elementary-group-is-simple-modulo-centre`,
  `minimal-subshift-algebra-is-simple-lef-ring`, `elementary-groups-over-fg-rings-have-property-t`
  (citation route), `sofic-implies-hyperlinear`, `lef-implies-operator-mf` and
  `weak-qd-kazhdan-quotientless-group-is-trivial`.
- `simple-kazhdan-groups-have-full-mf-radical` was OPEN. Its only route is invalidated by
  `mf-to-weak-qd-citation-has-unproved-lifting-step`.
- The fp root had two OPEN routes:
  - The Titz–Witzel kernel route waits on `titz-witzel-kernel-sofic`. That claim's
    elementary-permanence route is invalidated by `titz-witzel-kernel-not-elementary-sofic`.
  - The other is `hyperlinear-fp-simple-via-amenable-edge-splitting`.

**The combining route.** This lane drafted a route with the same id. 8b65f0932 landed its own route
first, so the draft was not landed. The landed route requires
`subshift-elementary-group-is-simple-modulo-centre`, `minimal-subshift-algebra-is-simple-lef-ring`
and `elementary-groups-over-fg-rings-have-property-t`, all ESTABLISHED at 3c481f496. Checked
against §3–§4:

- Its item 3 passes to `S` correctly. `Ψ` is injective and `F_q`-linear, and `Λ` is finite, so
  `Ψ(g) ∈ ΛI` forces `g ∈ Z(G)`.
- It does not require `lef-implies-operator-mf` or the weak-qd import. The claim body's operator-MF
  and not-weakly-quasidiagonal sentences are not in the claim's title, so they do not affect the
  root.
- The body of `simple-kazhdan-hyperlinear-from-subshift-elementary-group` still says "That claim is
  OPEN and under independent" review. That text is stale; the route's `requires:` is correct.

**At main f2d0166f7, after 8b65f0932.** Pending: MSI job `cairn-b`. Its results go in the next
commit.
