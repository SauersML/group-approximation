# Review: are the sixty-relator and eighteen-relator presentations complete?

Lane `ex-verify-presentation`, 2026-09-12. Adversarial review of lane `ex-free-objects`, landings
`0f2758222e` (`leavitt-unit-group-steinberg-weyl-presentation`, artifact §2) and `14a3ca5645`
(`thompson-steinberg-presentation-of-leavitt-unit-group`, `explicit-eighteen-relator-nonsofic-group`,
artifact §2). Soundness (every relator holds in `L^x`) was already verified. This review checks
**completeness**: is the presented group `L^x` itself, and not a proper cover or central extension?

`L = L_(F_2)(1,2)`, `G = L^x`, `[x,y] = x y x^-1 y^-1`. `P` = the sixty-relator group, `Q` = the
eighteen-relator group.

## 0. Verdict

| claim | verdict | conditional on |
|---|---|---|
| `P -> L^x` is an isomorphism | **PASS** | `atlas-steinberg-spare-index-independence` (in repo, re-derived here); Khanh arXiv:2609.08428v1 Theorem 5.4 at `r = 5` (statement read verbatim) |
| `Q -> L^x` is an isomorphism | **PASS** | `P = L^x`; Bleak--Quick Theorem 2.1; their KBMAG statement that (2.4) and (2.3) have the same normal closure (published, not reproduced) |
| both presented groups are simple and nonsofic | **PASS** | `openai-leavitt-unit-nonsofic`, `binary-leavitt-unit-group-is-simple` |

No FAIL was found. There is no mathematical GAP. There are two exposition gaps in the eighteen-relator
artifact, both closed in §3 with one more commutation each. One observation shrinks the trust surface:
the rank-five case of Khanh's Theorem 5.4 follows from his criterion Theorem 5.1 directly, with no use of
Voronetsky's refinement theorem (§2.3).

What the computations can and cannot do: every check in §4 evaluates in `L^x`, where all Steinberg
identities hold. A central extension of `L^x` satisfies the same relators. So no evaluation in `L^x` can
tell `P` from a cover. The completeness verdicts rest on the arguments in §1-§3. The computations only
guard conventions, transcriptions and the Weyl block.

## 1. The sixty-relator presentation `P`

**Step 1 (Weyl block presents `S_5`). PASS.** My own Todd--Coxeter enumeration closes at 120 cosets with a
consistent table, and the control `<x,y | x^2, y^3, (xy)^5>` closes at 60. The permutations `(12345)`,
`(12)` satisfy (W) and generate `S_5`. So `<c,t | W> = S_5`.

**Step 2 (symmetry lemma). PASS.** `c^2 t c^-2 = (c^2(1) c^2(2)) = (34)` and `c^-2 t c^2 = (45)` generate
`Sym{3,4,5}`. Two permutations with the same values at 1 and 2 differ on the right by an element of that
subgroup, so `X_ij(a)` is well defined. The composition convention, right-to-left, matches
`Theta(P_sigma) Theta(E_12) Theta(P_sigma)^-1 = Theta(E_sigma(1)sigma(2))`. All 120 Weyl words in
`c, c^-1, t` equal `Theta(P_sigma)`, and all 600 conjugates equal `Theta(E_ij(a))` (§4). I also checked the
seven abbreviations by hand. For example, `c^-1 t c^-1 t` sends `1 -> 1` and `2 -> 4`, which is `X14`.

**Step 3 (families at every root). PASS.** Transport through `S_5` is valid for relations in at most five
index variables, since `S_5` is transitive on injective assignments. The (B) multisets give both ordered
pairs, by `rho = (13)(24)` and inversion. In (P), the pointwise stabilizer `Sym{2,4,5}` of the root `(1,3)` is
transitive on ordered pairs of distinct spares. So the one imposed pair `(2,4)` gives all six.
The letter counts check: 13 reducing pairs (five `(1,b)`, four `(a,1)`, `Ee, Ff -> 1`, `Ef, Fe -> 0`) plus 12
irreducible pairs make 25.

**Step 4 (remaining commutations). PASS.** Items 1-7 were re-derived one by one, each from "`x` commutes with
`y` and `z`, hence with `[y,z]`". The side condition for each use, disjoint or same-source or same-target,
holds with a fifth index `m`. The case split is complete: if `j != k` and `l != i`, then two roots are
equal, same-source, same-target or index-disjoint.

**Step 5 (involutivity). PASS.** `[ab,c] = a[b,c]a^-1[a,c]` with `a = b = alpha`, and `delta` commutes with
`alpha` (same source, Step 4). This gives `[alpha^2, beta] = delta^2`.

**Step 6 (`St_5(L) = G_0 -> P`). PASS.** Read from `research/artifacts/steinberg-spare-index-2026-08-15.md`
§2, the relators of `G_0` are these.
- (A) root commutativity and (B′) all (St2) instances with `j != k`, `l != i`.
- (C) (St3) anchored: `[X_ij(a), X_jk(b)] = C_ik(a,b)`, the same word for all three `j`. For reducible
  pairs `C_ik(a,b)` is the generator `X_ik(ab)` or `1`. Corollary C2 of that artifact needs exactly this.
- The five context-free Cuntz--Krieger relators: `e*e -> 1`, `f*f -> 1`, `e*f -> 0`, `f*e -> 0`, partition.
- The 100 squares `X_ij(a)^2`.

`P` implies each of them.
- (A) and (B′) come from Step 4, and the squares from Step 5.
- The reducing (C) relators, including `cuntz` and `zero`, are the 13 (C) relators transported to every root.
- For irreducible pairs, take `C_ik(a,b)` = the chain through the least spare. Then (C) is (P).
- Partition is (Q), transported.

The spare-index proof was re-derived:
- Lemma K: its five side conditions, (I2) and (I2′).
- The length bookkeeping `1+|u_2|, |u_2 v|, |v| <= t-1`.
- The three-spare shuffle in `(P_t)`. With spares `k_A, k_B, k_C`: `E^(k_A) = V_(k_B) = V_(k_C)` and
  `E^(k_B) = V_(k_A)`, so all `V_m` agree.
- The order `(P_t) < (R_t) < (Q_t) < (Q′_t)`.

It uses (C) only through the three-chain agreement `(P_2)`, as trap 4 there says. So any fixed chain as
right-hand side gives the same group.

The additive half, which the route cites only as "context absorption plus bilinearity", I re-derived:
- Bilinearity. `[E_il(u), E_lj(w1)E_lj(w2)] = E_ij(uw1) E_lj(w1) E_ij(uw2) E_lj(w1)^-1`, and `E_lj(w1)`
  commutes with `E_ij(uw2)` (same target).
- Context absorption. Partition at `(l,m)` plus `(R)` gives `E_lj(ee*v) E_lj(ff*v) = E_lj(v)`, then once
  more on the left.
- The additive extension. By (Q′) all `E_ij(m)`, `m` monomials, commute. By the propagated squares they are
  involutions. So `E_ij` is a homomorphism from the contracted monoid algebra `F_2[M]_0`. Its kernel contains
  every `u(ee*+ff*-1)v`, so it factors through `L`.

(St1)-(St3) then extend factorwise and bilinearly. The two composites are the identity on generators, so
`G_0 = St_5(L)` with `X_ij(a) <-> x_ij(a)`.

**Step 7 (isomorphism). PASS.**
- Surjectivity. `(t y_1)^3 = 1` and `t^2 = 1` give `y_1 t y_1 t^-1 y_1 = t`, so `X_12(1)X_21(1)X_12(1) = t`.
  By (EQ), every transposition is in the image, and `c = p_(12)p_(23)p_(34)p_(45)`. All 20 Weyl links and
  the product for `c` were checked in `L^x`.
- Injectivity. `phi o psi` agrees on the letter generators with `Theta o phi_5`, where `phi_5` is the
  canonical map. The letter generators generate `St_5(L)`: monomials come from nested commutators
  through a spare index, and sums from (St1). `Theta` is a unital ring isomorphism
  (`T[d_j]S[d_k] = delta_jk`, `sum S[d_i]T[d_i] = 1`), so it restricts to units.
- `Theta o phi_5` is bijective by Khanh Theorem 5.4. Hence `psi` is injective.

## 2. The cited inputs, read from source

**2.1 Khanh, arXiv:2609.08428v1, TeX source fetched on MSI 2026-09-12.** Section 5 defines `St_m(B)` for
`m >= 3` by generators `X_ij(a)`, `a in B`, and the relations `X_ij(a)X_ij(b) = X_ij(a+b)`,
`[X_ij(a),X_kl(b)] = 1` for `i != l`, `j != k`, and `[X_ij(a),X_jk(b)] = X_ik(ab)` for distinct `i,j,k`,
"Here `[x,y]=xyx^{-1}y^{-1}`". `phi_m` sends `X_ij(a)` to `t_ij(a) = I + aE_ij`, and `N_m(B) = ker phi_m`.
This is the convention of §1, including the order `ab`.

> **Theorem 5.4** (`thm:steinberg-isomorphism`). For `R=L_{F_2}(1,2)` and every `r>=3`, the canonical map
> `phi_r : St_r(R) -> GL_r(R)` is an isomorphism.

This kills both obstructions at once:
- the Steinberg kernel `N_5 = K_2(5,L)`, the proper-cover risk;
- the cokernel `GL_5/E_5`, which is Lemma 5.3: "one has `GL_m(R)=E_m(R)` for every `m>=2`".

Lemma 5.3 is also independently Proposition `prop:Kone-binary` of Khanh--Thanh (below).

**2.2 Khanh--Thanh, arXiv:2607.10351, TeX source.**
- Proposition `prop:Kone-binary`: "`K_1(L)=0`. Consequently, `L^×` is perfect and `GL_n(L)=E_n(L)` for
  every `n>=2`".
- Corollary `cor:fixed-corner-generation`: `L^× = Theta_C(E_n(L))` for every ordered leaf set of size
  `n >= 2`. At `n = 4` this is `R^x = EL_4(R)`, and at `n = 5` it is the surjectivity used in Step 7.
- Corollary `cor:Ftwo-finite-presentation` identifies `K_2(n,L_d)` with `H_2(L_d^x, Z)` for `n >= 5`,
  citing Weibel for the universal central extension. With Khanh Theorem 4.4 that would be a third route to
  `K_2(5,L) = 0`. I did not check the Weibel citation, and nothing here uses it.

**2.3 Rank five without Voronetsky.** Khanh proves Theorem 5.4 in two steps. Rank four comes from the
criterion Theorem 5.1, and the other ranks from Voronetsky's refinement isomorphism, which
`leavitt-steinberg-map-iso-from-rank-three-citation` records as not re-read. The criterion also applies at
`n = 5` directly:
1. `GL_4 = E_4` and `GL_3 = E_3` (Lemma 5.3).
2. `j_4(N_4) = 1` in `St_5`, because `N_4 = 1` already (the rank-four case).
3. `|X_5(R)|` is simply connected. The fan argument in the proof of Theorem 5.4 uses Proposition 4.2
   (`prop:frame-cone`) only for vertices and edges. At `r = 5` these have at most `2 <= r-2` frame vectors,
   within the proposition's hypothesis.

So the rank-five input here rests on Theorem 5.1, Lemma 5.2, Lemma 5.3, Proposition 4.2 and Theorem 4.4 (for
`H_2(GL_3) = 0`). None of them uses Voronetsky.

**2.4 Bleak--Quick, arXiv:1511.02123v2 (GGD 11 (2017)), TeX `PresentationForV-FinalVersion.tex`.**
- Theorem 1.2: "R. Thompson's group V has a finite presentation with three generators `(00 01)`,
  `(01 10 11)` and `(1 00)` and eight relations".
- Section 2: "`a` corresponds to the map `t_{00,01}`, ... `b` corresponds to the product
  `t_{01,10} t_{01,11}` (inducing a 3-cycle of the sets `01C`, `10C` and `11C`), and `c` corresponds to
  `t_{1,00}`", with maps acting on the right (`x t_{alpha,beta}`).
- Theorem 2.1 (`thm:mainWithWords`) lists (2.3).
- The paragraph after it: the systems KBMAG constructs "are not confluent, but nevertheless enable us to
  replace each `r_i` by a Tietze-equivalent (in the group `Q_i`) shorter relation ... As a consequence, the
  normal closure, in the free group on `{a,b,c}`, of the following eight relations is identical to that of
  our original list", which is (2.4).

Continued in `research/artifacts/ex-review-presentations-2026-09-12-part2.md`:
- §3, the eighteen-relator group `Q`, step by step;
- §4, the computation record;
- §5, the trust surface;
- §6, traps;
- §7, the node changes.
