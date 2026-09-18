# gq-referee-b: `leavitt-refinement-identifies-unstable-k2-levels` (citation and hypothesis lens)

Node and route as landed at 414f75d29 (lane gq-infinite-primes). Lens: every cited theorem read at its source, and
every hypothesis checked against its use. Items 2–4 were passed by gq-referee-a (proof-gap lens, 2d373a8ea).

**Verdict: PASS.** Voronetsky's Proposition 1 is now read at source, and it holds as used. It needs only a unital
ring with a complete family of at least four orthogonal, pairwise Morita equivalent idempotents. It has no stable-rank,
commutativity or finiteness hypothesis. Applied to `M_(r+1)(R)` with the coarse family transported by `α_r`, it gives
exactly the node's `D_r`, for any unital ring with a Leavitt pair. Khanh's padded-centrality lemma and the two
classical facts are pinned. One wording change is suggested (W1).

## 1. Voronetsky, arXiv:2004.08551v2 (J. Pure Appl. Algebra 225 (2021)), read at source

**The setting, §2, p. 3.**
- "From now on fix a unital ring `R`. We think about `R` as a matrix ring."
- "We say that an idempotent `e ∈ R` Morita dominates an idempotent `ẽ` if `ẽ ∈ ReR`. ... Idempotents `e` and `ẽ`
  are called Morita equivalent if they Morita dominate each other."
- "If `e` and `ẽ` are orthogonal and Morita equivalent, then they are Morita equivalent to `e + ẽ`."
- "From now on fix a complete family `e_1, …, e_n` of Morita equivalent orthogonal idempotents in `R` for some
  `n ≥ 1`."

**Matrix rings, p. 4.** "If `R = M(n, A)` is the matrix algebra and `e_i` are the matrix units, then the groups defined
so far coincide with the usual `GL(n,A)`, `St(n,A)`, `E(n,A)`, ..., `K_2(n,A)`."

**The coarsening map, §2, p. 5.** With `α = e_n − e_(n−1)` and `e_∞ = e_(n−1) + e_n`, "There is a well-defined map
`F_α : St(R, Φ/α) → St(R, Φ)` given by":
- `x_ij(a) ↦ x_ij(a)` for `i, j < n−1`;
- `x_(i∞)(a) ↦ x_(i,n−1)(a e_(n−1)) x_(in)(a e_n)` for `i < n−1`;
- `x_(∞j)(a) ↦ x_(n−1,j)(e_(n−1) a) x_(nj)(e_n a)` for `j < n−1`.

**The pro-group frame, §3, p. 7.** "suppose that `R` is a `K`-algebra for some commutative unital ring `K` and fix a
multiplicative subset `S ≤ K•`." Take `K = Z` and `S = {1}`. This is available for every ring.

**The statement, §4, p. 9, immediately before Lemma 5.**

> "We are ready to prove that `F_α` is an epimorphism for `n ≥ 3` and an isomorphism for `n ≥ 4` in Pro(Grp). If
> `S = {1}`, then this means that `F_α : St(R, Φ/α) → St(R, Φ)` is a surjection for `n ≥ 3` and a bijection for
> `n ≥ 4`. The proof also shows that the group `St(R, Φ)` is perfect for `n ≥ 3`."

Proposition 1, p. 10: "If `n ≥ 4` and `α ∈ Φ` is a root, then `F_α` is an isomorphism in Pro(Grp)."

**What the proof uses (pp. 7–11).**
- Morita equivalence, through Lemma 2: `e_i = Σ_p x_p y_p` with `x_p ∈ R_ij` and `y_p ∈ R_ji`.
- The commutator identities.
- A fourth index `j ∉ {i, n−1, n}`: "such a `j` exists since `n ≥ 4`".

It uses no stable rank. The stable-rank conditions appear only in the main theorem, through §§5–6. So Khanh's phrase
"requires no hypothesis on stable rank, quasi-finiteness, or centrality of the kernel" (khanh.tex l.553) is accurate.

**The node's application checked.**
- **Full family.** In `M_(r+1)(R)` the matrix units `E_11, …, E_(r+1,r+1)` form a complete orthogonal family, and it is
  Morita equivalent, since `E_aa = E_ab E_bb E_ba`. The fine family has `n = r + 1 >= 4` members exactly when
  `r >= 3`. ✓
- **The coarse family is transported by `α_r`.**
  - `α_r(E_ii) = E_ii` for `i < r`.
  - `α_r(E_rr) = T_r E_rr U_r = E_rr + E_(r+1,r+1) = e_∞`: on `(…, y, z)` it gives `(0, …, e*(ey + fz), f*(ey + fz)) =
    (0, …, y, z)`.
  - So `α_r` is a ring isomorphism carrying `(M_r(R), standard family)` to `(M_(r+1)(R), e_1, …, e_(r−1), e_∞)`.
  - Voronetsky's `St` is defined from the pair (ring, family), through `R_ij = e_i R e_j`. So `St_r(R) ≅ St(M_(r+1)(R),
    Φ/α)` through `α_r`. ✓
- **The generators.** `D_r = F_α ∘ α_r` on generators:
  - `α_r(a E_ir) = (ae) E_ir + (af) E_(i,r+1)`, so `D_r X_ir(a) = X_ir(ae) X_(i,r+1)(af)`;
  - `α_r(a E_rj) = (e*a) E_rj + (f*a) E_(r+1,j)`, so `D_r X_rj(a) = X_rj(e*a) X_(r+1,j)(f*a)`.
  - These are the node's formulas. ✓
- **Compatibility.** `φ_(r+1) D_r = α_r φ_r`, because `st(x_ij(a)) = t_ij(a) = 1 + a` (p. 4) and the two factors of
  `F_α(x_(i∞)(a))` multiply to `1 + a e_(n−1) + a e_n = 1 + a`. ✓
- **Which rings.** The Leavitt pair enters only through `α_r`, via `U_r T_r = I_r` and `T_r U_r = I_(r+1)`. So item 1
  holds for every unital ring with a Leavitt pair, as the node says. For `R_L` take `(e, f, e*, f*) = (s_1, s_2, t_1,
  t_2)`. ✓

## 2. Khanh, arXiv:2609.08428, `gq/src/on/2609.08428/khanh.tex`

- **Padded centrality**, `lem:padded-centrality`, l.498–508: "For any unital ring `B` and `m ≥ 3`, `j_m(N_m(B))` is
  central in `St_(m+1)(B)`." Here `N_m = ker φ_m = K_2(m, B)`.
  - The proof is the Weibel III 5.2.1 extra-index argument, and I checked it. Elements of `j_m(N_m)` act on the column
    and row subgroups `u(a)`, `v(b)` through their matrix image `1`.
  - The remaining generators are `X_ij(c) = [X_(i,m+1)(c), X_(m+1,j)(1)]`. ✓ Stated for any unital ring and `m ≥ 3`,
    as the request asks.
  - (The request located it at l.512–525. That range is `lem:elementary-generation`, which is specific to
    `L_(F_2)(1,2)` and is not used by the node.)
- **The refinement paragraph**, l.549–556, is quoted correctly in the route. Its bibliography entry (l.747–748) points
  to `2004.08551v2`, the version read here.
- **Perfectness of `St_r`, `r >= 3`**, used in items 2 and 4: Khanh l.533 ("each generator is a commutator using a
  third index"), and Voronetsky p. 9 as quoted above. ✓

## 3. The classical facts in item 2

C. Weibel, *The K-book*, Ch. III, read at source.
- **Theorem 5.5** (Kervaire, Steinberg), p. 38: "The Steinberg group `St(R)` is the universal central extension of
  `E(R)`. Hence `K_2(R) ≅ H_2(E(R); Z)`."
  - So conjugation by `g ∈ GL(R)`, an automorphism of the perfect normal subgroup `E(R)`, lifts uniquely to `St(R)`.
    This is the action "(Milnor)" in the route.
- **Triviality on `K_2`**, p. 39, proof of Proposition 5.6: "`GL(R)` acts trivially upon the homology of
  `E(R) = [GL(R), GL(R)]` by Ex. 1.13. By Theorem 5.5 this implies that `H'_2(GL(R)) = H_2(E(R); Z) = K_2(R)`."
  - So `GL(R)` acts trivially on `K_2(R) = H_2(E(R); Z)`, which is the route's second "(Milnor)". ✓
- Milnor's book itself was not re-read. Weibel's statements suffice.

## 4. Other citations in the node

- "What remains" describes Khanh's `thm:raw-criterion` inputs as used at l.527–545: `G_2 = E_2`, `G_3 = E_3`,
  `j_3(N_3) = 1` and a simply connected `X_4`. ✓
- Both claimed failures for `R_L` are right:
  - `K_1(R_L) = Z ≠ 0`, so `GL_n(R_L) ≠ E_n(R_L)` for every `n`.
  - `K_2(n, R_L) -> K_2(R_L) = Q^x` is onto, so `j(K_2(n−1)) ≠ 1`. (This uses the refereed
    `leavitt-resolvent-k-theory-is-shifted-rational-k-theory`.)

## Warnings

- **W1 (status line).** "Voronetsky's proposition itself was read only through Khanh's account" can now read:
  "Voronetsky, arXiv:2004.08551v2, §2 (definitions, p. 3; `F_α`, p. 5), §4 (text before Lemma 5, p. 9; Proposition 1,
  p. 10), read at source by gq-referee-b; for `S = {1}` the map `F_α` is a bijection for `n ≥ 4`."
