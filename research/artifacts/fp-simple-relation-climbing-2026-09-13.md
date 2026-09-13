# Relation climbing for Labbé's derived full group: the Grigorchuk–Medynets anatomy and exact ball-legality data

Lane `ex-fp-simple-relation-climbing`, 2026-09-13. Unreviewed. Positive side of
`labbe-shift-derived-full-group-is-finitely-presented`. Nodes backed here:
- `zd-subshift-derived-full-group-local-presentation` (open);
- `labbe-full-group-local-relations-climb` (open, the crux);
- route `labbe-fp-via-local-relation-climbing`;
- `labbe-shift-ball-legality-is-pairwise-at-radii-two-to-seven` (established by exact computation).

**Verdict.** Undecided. This part fixes the framework, locates where the one-dimensional proof of
infinite presentation lives inside the known infinite presentation, and computes the first
combinatorial layer of the climbing step for `Omega_U` exactly.

## 1. Sources (TeX on MSI, `/scratch.global/sauer354/fpsa/src/`, `/scratch.global/sauer354/fpsz2/src/`)

- **Grigorchuk–Medynets, arXiv:1508.04454** (`RelationsFullGroupsUber.tex`), "Presentations of
  Topological Full Groups by Generators and Relations".
  - Theorem `TheoremIntroMain` (lines 75–96): for a minimal subshift `(Omega, T)` there is
    `n >= 3` such that `G_T'` has generators `x_(w,k)`, `w ∈ L(Omega)`, `|w| >= n`, `k ∈ Z`, and
    relations, for every cylinder partition `C` of `(w,i)`:
    (R1) `x_(w,i)^3 = 1`; (R2) `(x_(w,i) x_(w,i+1))^2 = 1`;
    (R3) `x_(w,i+1) = x_(w,i+2) x_(w,i)^(-1) x_(w,i+2)^(-1) x_(w,i)`;
    (R4) `x_(w,i) = prod_((s,k) ∈ C) x_(s,k)`; (R5) `[x_(w,i), x_(v,j)] = 1` whenever the six
    cylinders `(w,i..i+2)`, `(v,j..j+2)` are mutually disjoint.
  - Proof of Theorem `TheoremMain` (lines 505–690). Lemma `LemmaGTW_presentation` (line 557)
    presents the locally finite group `G'_(T,omega)` of permutations inside Kakutani–Rokhlin
    towers, using the Vershik–Vsemirov presentation of `Alt(n)` (Lemma, line 537) and simplicity.
    Theorem `TheoremPermutationProduct` (line 304) gives `G_T' = G'_(T,omega) G'_(T,omega')` for
    two orbits. The final rewriting lemma uses only (R4) and (R5).
  - Lemma `LemmaMatui` (line 346): if `U, TU, T^2U ∪ V, TV, T^2V` are mutually disjoint then
    `sigma_U * sigma_V = sigma_(T(U) ∩ T^(-1)(V))`, with `r * s = s r^(-1) s^(-1) r`.
- **Chornyi–Juschenko–Nekrashevych, arXiv:1602.04255** (`IET_copy.tex`).
  - Lemma `lem:incompatible` (line 126).
  - Corollary `cor:patchesunion` (line 160): if `pi_1, pi_1+g_1, pi_1+g_2, pi_2, pi_2+h_1,
    pi_2+h_2` are pairwise incompatible except for the pair `pi_1, pi_2`, then
    `[[T_(pi_2,(0,h_1,h_2))^(-1), T_(pi_1,(0,g_1,g_2))^(-1)], [T_(pi_2,(0,h_1,h_2)), T_(pi_1,(0,g_1,g_2))]] = T_(pi_1 ∪ pi_2,(0,g_1,g_2))`.
  - Line 166: `R_1` such that `(B(R_1), w|B(R_1))` is incompatible with its translates by every
    `g` with `|g|_1 <= 3`. Proposition (line 171): if `R >= R_1 + 2`, `<𝒯_R>` contains `𝒯_(R+1)`,
    where `𝒯_R = {T_(pi,(0,e_i,-e_i)) : pi legal on B(R)}` (`ℓ_1` balls).
- **Labbé, arXiv:1802.03265** (`article1.tex`, `for_article1.sage`).
  - Theorem `thm:main` (line 295): `Omega_U` is self-similar, aperiodic and minimal.
  - Proposition `prop:pre-main` (line 2269): `omega = alpha∘beta∘gamma` is expansive,
    recognizable in `Omega_U`, and `Omega_U = omega(Omega_U) ∪ sigma^(e_1) omega(Omega_U) ∪
    sigma^(e_2) omega(Omega_U) ∪ sigma^(e_1+e_2) omega(Omega_U)`.
  - Tile list `tilesU` and the tables `alpha`, `beta`, `gamma` (sage script lines 50–85). Tiles are
    strings (right, top, left, bottom); images are lists of columns, each bottom to top.

## 2. Where infinite presentation lives in one dimension

**Remark 2.1 (argument sketch; the conclusion is Matui's theorem, proved differently by
Grigorchuk–Medynets).** Let `X` be an infinite minimal subshift and `X_N` the `N`-step Markov
approximation (all words of length `<= N` legal).
1. On any `Z`-set with a colouring all of whose `N`-windows are words of `X`, define the Matui
   3-cycles `sigma_(w,i)` by reading windows. Condition (†) (no repeated letter in a legal 5-word)
   is read inside windows, so (R1)–(R3) hold for every cylinder, legal or not.
2. (R4) and (R5) for cylinders of length `<= n` hold once `N >= n + 5`. A failure of (R4) needs
   an occurrence of an extension of `w` of length `<= N` not in `L(X)`. A failure of (R5) needs
   occurrences of `w` and `v` within distance 2, which is an illegal word of length `<= N`.
3. `X_N` is a nonempty one-dimensional SFT, so it has periodic points. Their finite orbits carry
   finite marked groups in which every relator of scale `<= n` of the G–M presentation holds.
   By Theorem `TheoremIntroMain` every relator of `G_T'` is a consequence of relators of some
   finite scale, so a finite presentation would force all of them to hold there.

**What the remark isolates.** Only (R4) and (R5) ever fail in these models, and only above the
Markov scale. In one dimension, relation climbing fails because (R4) and (R5) at length `n+1`
detect words whose two length-`n` subwords are legal but which are illegal, and such words exist
at every length (a minimal infinite subshift is not of finite type).

## 3. The two-dimensional climbing step

Fix `R >= R_1 + 2`. For a pattern `p` on `B(r+1)` (not assumed legal) put
`rho_h = p|(B(r)+h)` for `h ∈ H_5 = {0, ±e_1, ±e_2}`. ChJN's step writes
`T_(p,(0,g,-g))` by four applications of Corollary `cor:patchesunion`, adding one `rho_h` at a
time. Call `p` **hidden illegal at radius `r+1`** if every `rho_h` is legal but `p` is not. Its
**order** is the least `k` such that the restriction of `p` to a union of `k` of the five balls
is illegal.

**Lemma 3.1 (order-2 collapse).** Let `r >= R_1 + 2`, `p` hidden illegal on `B(r+1)` and
`rho_0 ∪ rho_h` illegal for some `h ≠ 0`. Then `T_1 = T_(rho_0,(0,g,-g))` and
`T_2 = T_(rho_h,(0,h,2h))` have disjoint supports, and the ChJN word
`[[T_2^(-1), T_1^(-1)], [T_2, T_1]]` equals `1`. In any group where `[T_1, T_2] = 1` holds, the
word is trivial.

*Proof.* The six sets are `W_(rho_0)`, `W_(rho_0) ± g`, `W_(rho_h)`, `W_(rho_h) + h`,
`W_(rho_h) + 2h`.
1. Every `rho_h` contains `pi = p|B(R_1)`, since `B(r) + h ⊇ B(R_1)`.
2. Every pair other than `(W_(rho_0), W_(rho_h))` meets only if `pi` is compatible with `pi + u`
   for some `u` with `0 < |u|_1 <= 3`, which the choice of `R_1` excludes.
3. `W_(rho_0) ∩ W_(rho_h) = W_(rho_0 ∪ rho_h) = ∅`, because the union is illegal.
4. So the supports are disjoint, `T_1` and `T_2` commute, and both inner commutators are `1`. ∎

When the illegal pair is `(rho_h, rho_(h'))` with `h, h' ≠ 0`, it appears only after
`rho_0 ∪ rho_h` has been added. Triviality then follows from the relations of the finite group
`<T_(rho_0,·), T_(rho_h,·), T_(rho_(h'),·)>`: three generators of radius `r`.

**Where the naive induction dies.** Say `K_k(r)` holds in a group `H` if every relation of `G`
among at most `k` elements of `𝒯_r` holds among the corresponding climbed words. Then
`K_(5k)(r)` implies `K_k(r+1)`, since each element of `𝒯_(r+1)` is a word in five of `𝒯_r`. To
iterate, `K_k(r+1)` must upgrade to `K_(5k)(r+1)`. That needs each group generated by `5k`
elements of `𝒯_(r+1)` to be the colimit of its subgroups on `k` generators.
- That fails in general: families whose supports overlap cyclically in different local
  configurations give infinite colimits of finite groups.
- The one-dimensional calibration shows it must fail there at infinitely many scales, or
  Remark 2.1 would be contradicted.

## 4. Exact computations for `Omega_U`

**Scripts.** `experiments/fp-simple-relation-climbing/labbe_lang.py` and `labbe_orders.py`, run
on MSI with `/usr/bin/python3.11` in `/scratch.global/sauer354/ex/ex-fp-simple-relation-climbing/`.
Each run takes under 2 seconds.

**Completeness of the language (proof).**
- Every patch `omega^k(Q)` of a legal patch `Q` is legal, since `omega(Omega_U) ⊆ Omega_U`.
- Minimal supertile sides of `omega^j` by level `j = 0..7` are `1, 1, 2, 3, 5, 8, 13, 21`.
- Every legal `B(r)`-pattern lies in a `2 x 2` block of level-`j` supertiles once the minimal side
  is `>= 2r + 1` (Proposition `prop:pre-main` with recognizability gives a supertile
  decomposition of every tiling). So `L_(B(r)) = ∪_Q patterns of omega^j(Q)`, `Q` running over
  legal `2 x 2` patterns, with `j = 7` for `r <= 7`.
- The legal `2 x 2` patterns are closed under taking `2 x 2` factors of `omega`-images. Seeding the
  closure from `omega^7(0)` (21 x 21) and from `omega^9(0)` (55 x 55) gives the same 50 patterns.
- Consistency checks: all images pass the Wang edge test, and every legal `B(r+1)`-pattern is
  found among the candidates below.

**Results.**

| radius `r` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| `|L_(B(r))|` | 19 | 69 | 152 | 267 | 413 | 592 | 804 | 1047 |
| candidates on `B(r)` with legal sub-balls | – | – | 206 | 301 | 472 | 606 | 890 | 1062 |
| hidden illegal on `B(r)` | – | – | 54 | 34 | 59 | 14 | 86 | 15 |
| of order 2 | – | – | 54 | 34 | 59 | 14 | 86 | 15 |

- **Incompatibility radius.** Some legal `B(R)`-pattern is compatible with a translate by `g`,
  `|g|_1 <= 3`:
  - for `R = 0`, at 10 vectors;
  - for `R = 1`, at `(±3, 0)` and `(0, ±3)`;
  - for `R = 2`, at `(0, ±3)`;
  - for `R = 3` and `R = 4`, at none.

  So ChJN's `R_1 = 3`. Their finite generating set `𝒯_5` has `2 · 592 = 1184` elements.
- **Hidden illegality at every computed radius.** `Omega_U` is not ball-Markov at any radius from
  2 to 7. Every climbing step meets patterns whose climbed 3-cycle is trivial in `G` for a reason
  invisible to single sub-balls.
- **All of it has order 2.** At radii 2 to 7, a pattern on `B(r+1)` is legal iff the restrictions
  to all ten unions of two of its five sub-balls are legal. Lemma 3.1 and the remark after it
  make every such triviality a consequence of relations among at most three radius-`r`
  generators.
- **Minimal illegal unions** include center–neighbour pairs such as `(0, e_1)` and
  neighbour–neighbour pairs such as `(e_1, e_2)`. The even radii 2, 4, 6, which have more hidden
  illegal patterns, show both kinds; the odd radii 3, 5, 7 show only neighbour–neighbour pairs.

## 5. The crux and the next tests

**The claim to decide** (`labbe-full-group-local-relations-climb`). There are `k` and `r_0` such
that, in every group generated by `𝒯_(r_0)` with climbed words for finer generators, `K_k(r_0)`
implies `K_k(r)` for all `r >= r_0`. Together with a local presentation theorem in the G–M form
for `Z^2` (`zd-subshift-derived-full-group-local-presentation`), this gives finite presentation.

**Why order 2 is not yet enough.** Relations between two radius-`(r+1)` generators whose patterns
are at offset `<= 2` involve ten radius-`r` sub-balls at offsets up to 4.
- In one dimension the failing triviality always pairs the first subword of one word with the
  last subword of the other, at the largest offset. Its union is the whole illegal word.
- The Section 4 table tests ball patterns of diameter `2r + 2` against pairs of diameter
  `2r + 2`. The diameter gap that kills one dimension is not tested there.

**Next tests.**
- (T1) For `U = B(r+1) ∪ (B(r+1) + delta)`, `|delta|_1 <= 2`, count illegal patterns whose two
  big balls and all pairs of sub-balls at offset `<= 2` are legal.
- (T2) Compute the finite groups generated by the ten sub-ball generators of such pairs, and test
  whether their pairwise subgroups present them (coset enumeration).
- (T3) Record the supertile-corner endomorphism of `D([[Omega_U]])` given by recognizability
  (next part), the tool for climbing by self-similarity instead of by one radius at a time.
