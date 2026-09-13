# Review of the presentations, part 2: the eighteen-relator group, computations, trust surface

Continuation of `research/artifacts/ex-review-presentations-2026-09-12.md` (§0 verdict, §1 `P`, §2 sources).
Lane `ex-verify-presentation`, 2026-09-12.

## 3. The eighteen-relator presentation `Q`

**Step 0 (the `V` part). PASS.**
- **Generation matters, not only injectivity.** An injective `rho : V -> L^x` has image isomorphic to `V`.
  But `V` contains proper copies of itself, such as `iota_1(V)`. Step 1 needs more:
  - every Thompson unit `g` must have a preimage `ĝ`;
  - the units supported on the cone `1` must be words in the three (H) elements.
- Both hold because Bleak--Quick's generators are the maps `t_(00,01)`, `t_(01,10) t_(01,11)`, `t_(1,00)`, which
  generate `V` (Theorem 1.2). I built `b` as that product under their right action, with
  `psi(g) = U_g^-1`. It equals the authoring lane's reading `U_(01 10 11)^-1`. The three (H) conjugates evaluate
  to `psi` of `t_(100,101)`, `t_(101,110) t_(101,111)` and `t_(11,100)`.
- **Transcription.** My parse of (2.4) from the TeX equals the JSON (V) block word for word. All eight (2.3)
  relators hold under the images.
- **Trust.**
  - `(2.4) ⊆ ncl(2.3)` holds, because the (2.4) words hold in `V` (evaluated).
  - The converse is Bleak--Quick's KBMAG statement. If it failed, `<a,b,c | (2.4)>` would be a proper cover
    of `V`. Step 0's transfer of `V`-identities into `Q` would then break, and `Q = L^x` would be unproved.
  - GAP/KBMAG is not installed on MSI (checked), so the statement was not reproduced. It is in the
    published, refereed paper. Its method replaces each `r_i` by a relation equal to it in the group of the
    other seven, and that preserves the normal closure.
  - The variant with (2.3) in place of (2.4) has the same proof and rests on Theorem 2.1 alone.

**Step 1 (leaf transvections well defined). PASS.**
- `h = g^-1 g'` has `h S[00] = S[00]` and `h S[01] = S[01]`. So `h` is a Thompson unit fixing both cones
  pointwise, supported on the cone `1`, and it lies in `psi(iota_1(V))`.
- By Step 0, `ĥ` is a word in the (H) elements.
- `phi(T(al,be)) = 1 + S[al]T[be]` uses `g^-1 = g*` for Thompson units.

**Step 2 (transport). PASS.** The hypothesis "pairwise disjoint, with nonempty complement" is needed, since
otherwise `v` does not exist. Every instance used satisfies it:
- Step 3 instances leave `al(1-d)` or `be(1-d)` uncovered;
- Step 4 instances use subcones of three or four chart leaves, which leaves a fifth leaf free;
- Step 5 instances use at most three chart leaves.

When the complement is empty, as in `T(00,01)` against `T(10,11)`, the relation follows after one (Q)
split. No step needs that case, and it holds in `L^x`.

**Step 3 (derived laws). PASS, with an exposition gap closed here.**
- **C1d, `d = 1`.** Put `y = T(al0,be0)`, `z = T(al1,be1)`, `w = T(be1,ga)`. The identity
  `[yz,w] = y[z,w]y^-1[y,w]` leaves `y T(al1,ga) y^-1`, not `T(al1,ga)`. The artifact stops at "C11 for
  `e = d`". One more B-dis, on the cones `al0, be0, al1, ga` (complement contains `be1`), removes the
  conjugation.
- **CEd, `d = 1`.** `[w,yz] = [w,y] . y[w,z]y^-1` leaves `y T(al,ga1) y^-1` with `y = T(be0,ga0)`.
  B-dis on `al, ga1, be0, ga0` (complement contains `be1`) removes it.

Both commutations hold in `L^x` on 300 random configurations (`C1d-conjugation`).

**Step 4 (`beta : P -> Q`). PASS.** Every family was re-derived.
- (W) are `V`-identities. For (K), `Theta(P_(34))` and `Theta(P_(45))` fix `00` and `01` pointwise. (L)
  and (D) are (X2) and (X1).
- (B): B-dis on four subcones of `d_1..d_4`. B-src and B-tgt are the base triple `(00,01,10)` itself.
- (C), 13 relators:
  - C11: `(1,1), (1,E), (1,F), (e,1), (f,1), (E,e), (F,f)`;
  - C1d: `(1,e), (1,f)`;
  - CEd: `(E,1), (F,1)`;
  - B-dis: `(E,f), (F,e)`.
- (P), 12 relators. Use C1d on `{e,f}^2`, C11 on `{e,f} x {E,F}`, and CEd on `{E,F}^2` with `ga = d_3 m_t`.
  The last gives `T(d_1, d_3 m_t l_t) = 1 + S[d_1] t_l t_m T[d_3]`.
  - Checked in `L^x` for all 25 letter pairs: the spare-2 chain, the spare-4 chain and `1 + S[d_1] l m T[d_3]`
    agree.
- (Q): C11 twice, then (Q).
- `beta(X_ij(l)) = T(d_i l_s, d_j l_t)` needs `Theta(P_sigma)` to act by prefix replacement on the chart
  leaves, which it does.

**Step 5 (`beta` is onto). PASS.**
1. The suffix formulas `T(d_i g d, d_j de) = [T(d_i g, d_k), T(d_k d, d_j de)]` and
   `T(d_i g, d_j de d) = [T(d_i g, d_k d), T(d_k, d_j de)]` hold, and so does the same-leaf routing through a
   third leaf (300 random instances).
2. `N` is normal. A Thompson unit acts by prefix replacement on fine enough cones, and its images of disjoint
   cones with nonempty complement are again such.
3. `Q/N` is a quotient of `V`, by Step 0. In it `a = 1`, by `(ax)^3 = 1`, `x in N` and `a^2 = 1`. Since
   `a != 1` in `V` and `V` is simple, `Q/N = 1`.

**Nonsoficity and simplicity of `P` and `Q`. PASS.** Both are isomorphism invariants.
- `openai-leavitt-unit-nonsofic` concerns the same algebra: the same five relations.
- The Lean endpoint `universalLeavittUnits_not_isSofic` is over `ZMod 2`.
- `binary-leavitt-unit-group-is-simple` is the same group, through `Theta` for `{0,10,11}`.

## 4. Computation record

Script: `experiments/nonsofic-certificates/presentations/review_presentation_consequences.py`, written for
this review and independent of the authoring lane's scripts. Only the shared `leavitt.py` arithmetic is common
(VERSION `2e9a9873`). It ran on MSI acn with `/usr/bin/python3.11` in 0.9 s, verdict PASS. Output:
`review-presentation-consequences.json`. Dual mode was on for parts A-D.

- **A.** My own HLT Todd--Coxeter enumeration.
  - `<c,t | W>` closes at **120** cosets, with a consistent table and every relator closing at every coset.
  - Control: `<x,y | x^2, y^3, (xy)^5>` closes at **60**.
- **B.** The literal JSON words were evaluated under images built here.
  - `P`: 60 relators, 0 failing, total length 1,007, max 38, sha256 matches.
  - `Q`: 18 relators, 0 failing, total length 322, max 37, sha256 matches.
  - Bleak--Quick's `b`, built as `t_(01,10) t_(01,11)`, equals the lane's reading.
- **C.** (2.4) from the TeX equals the JSON (V) block (8/8). The (2.3) relators hold (8/8). The three (H)
  conjugates equal their `iota_1` images, and the six conjugator words give their named transvections.
- **D.** Both abelianizations are trivial: the integer row lattices have triangular bases with all diagonal
  entries `1`, for `P` on 7 generators and for `Q` on 4.
- **E1.** The sixty-relator proof, through words in `c, c^-1, t`:
  - 120 Weyl words equal `Theta(P_sigma)`;
  - 600 conjugates `p_sigma y_a p_sigma^-1` equal `Theta(E_ij(a))`;
  - (B′), 6,500 instances;
  - both unit-letter splittings `X_ij(a) = [X_im(1),X_mj(a)] = [X_im(a),X_mj(1)]` and the squares, at every
    spare;
  - (St3) at all 25 letter pairs and all spares;
  - partition at every root and spare;
  - all 20 Weyl links `X_ij(1)X_ji(1)X_ij(1) = p_(ij)`;
  - `c = p_(12)p_(23)p_(34)p_(45)`.

  No failures.
- **E2.** The eighteen-relator proof, on 300 random cone configurations (codes of 5 to 9 leaves, depth up to
  5): B-dis, B-src, B-tgt, C11, (Q), (X1), C1d and CEd at a random `d`, the C1d conjugation, transport by a
  random Thompson unit, the suffix formulas and same-leaf routing. Also the empty-complement B-dis case and all
  25 letter pairs of the (P) family. No failures.

All of A-E are sanity checks. None of them distinguishes `P` or `Q` from a central extension of `L^x`.

## 5. Trust surface after review

1. `atlas-steinberg-spare-index-independence`: in repo, adversarially verified 2026-08-15, and re-derived
   here (§1 Step 6), including the additive assembly that its route cites in one line.
2. Khanh arXiv:2609.08428v1 Theorem 5.4 at `r = 5`: v1 preprint, statement verbatim. The rank-five case is
   reachable through Theorem 5.1 without Voronetsky (§2.3).
3. Bleak--Quick Theorem 2.1, published. For the eighteen-relator list only, also their KBMAG normal-closure
   statement for (2.4).
4. Simplicity of `V` (Cannon--Floyd--Parry).

## 6. Traps

1. Evaluations in `L^x` confirm soundness and conventions only. Do not cite §4, or the authoring lane's
   control families, as evidence of completeness.
2. Step 0 of the eighteen-relator proof needs `rho(V)` to be *all* Thompson units. That comes from the named
   Bleak--Quick generators, not from the simplicity of `V`.
3. For reducible pairs, `G_0`'s anchored (St3) must have the generator `X_ik(ab)`, or `1`, as its right-hand
   side, because Corollary C2 of the spare-index artifact consumes it. `P`'s thirteen (C) relators supply
   exactly this. A relator list that only equated chains for reducible pairs would not be covered by that
   theorem.
4. The eighteen-relator count with (2.4) inherits a computer-derived normal-closure statement. The same
   proof with (2.3) does not, at larger total length.

## 7. Graph changes made with this review

- The status lines of `leavitt-unit-group-steinberg-weyl-presentation`,
  `thompson-steinberg-presentation-of-leavitt-unit-group`, `explicit-sixty-relator-nonsofic-group` and
  `explicit-eighteen-relator-nonsofic-group` now say "reviewed 2026-09-12 by `ex-verify-presentation`: PASS"
  with the conditions above, and they cite this artifact.
- `leavitt-steinberg-map-iso-from-rank-three` records the Voronetsky-free rank-five path.
