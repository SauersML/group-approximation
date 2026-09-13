---
rg: 2
id: subshift-elementary-group-simple-constant-tower-proof
kind: route
title: Make the coefficients constant on the tower levels, so one commutator lands in a single finite GL_d
target: subshift-elementary-group-is-simple-modulo-centre
requires: [minimal-subshift-algebra-is-simple-lef-ring]
artifacts:
  - research/artifacts/sk-simplicity-short-a-proposal-2026-09-13-part1.md
  - research/artifacts/sk-simplicity-short-a-proposal-2026-09-13-part2.md
---

A second derivation of the target, shorter than `subshift-elementary-group-is-simple-modulo-centre-proof`.
UNREVIEWED; it is queued with sk-referee-1 (2026-09-13).
- Full derivation: part 2 §2 (all q) and §1 (q = 2, sentence by sentence).
- Proposed text for the note: part 1.

Setting: `R = LC(X,F_q) ⋊ Z`, `G = EL_3(R)`, `u f u^(-1) = f∘T^(-1)`, and `e_U` is the indicator of a clopen set `U`. The only input is that `R` is simple (item 2 of `minimal-subshift-algebra-is-simple-lef-ring`).

1. **Centre and a noncommuting root.** Let `g ∈ N` have propagation `w`, and let `C` run over the atoms of a partition with disjoint levels `T^aC`, `|a| <= w+2`.
   - Suppose `g` commutes with every `e_ij(e_C)` and `e_ij(e_C u)`.
   - Then `g = cI_3`, and the `u^j`-coefficients of `c` vanish for `j != 0`.
   - `cu = uc` makes `c` invariant, hence constant.
   - So `Z(G) ⊆ F_q^x I_3`, and a noncentral `g` fails to commute with some `h = e_ij(s)`, `s ∈ {e_C, e_C u}`.
2. **Constant tower.** Refine the partition so that every coefficient of every entry of `g^(±1)` is constant on `T^aC`, `|a| <= w+1`.
   - Put `m = w+1`, `ε_ab = e_(T^aC) u^(a-b)` for `|a|,|b| <= m`, and `B = span ε_ab ≅ M_(2m+1)(F_q)`.
   - Product formula: `f u^i ε_(0b) f' u^j = f(T^iC) f'(T^bC) ε_(i,b-j)`.
   - So `y = g sE_ij g^(-1) - sE_ij ∈ M_3(B)`, with `k = [g,h] ∈ N \ {1}`, `k - I = y h^(-1)` and `k^(-1) - I = -h y`.
   - Hence `k ∈ H = (1-e)I_3 + GL_3(B) ≅ GL_d(F_q)`, with `d = 3(2w+3)`.
3. **SL_d inside G.** The transvections `I + λ ε_ab E_pq` of `S ≅ SL_d(F_q) ⊆ H` lie in `G`.
   - For `p != q` they are roots.
   - For `p = q` they are commutators `[I + λ ε_aa E_pr, I + ε_ab E_rp]` with `r != p`.
4. **k not scalar in H.** `[k,S] ⊆ N ∩ S`. If `N ∩ S` were central, `s ↦ [k,s]` would be a homomorphism into `Z(S)`. It is trivial because `S` is perfect, so `k` would centralize `S` and be scalar, a contradiction. So `S ⊆ N` (`PSL_d(F_q)` is simple, `d >= 9`), and `e_pq(e_C) ∈ N` for all `p != q`.
5. **k scalar in H.** Then `k = cI_3` with `c = 1 + (λ_0 - 1)e` and `λ_0 != 1`. Put `r = e_(T^mC) u^(-1)`. Then `crc^(-1) = λ_0 r`, because `T^(m+1)C` lies off the tower. So `[k, e_pq(r)] = e_pq((λ_0 - 1) r) ∈ N` for all `p != q`.
6. **Level ideal.** `J = {r : e_pq(r) ∈ N for all p != q}` is a two-sided ideal: `e_pq(sr) = [e_pl(s), e_lq(r)]` and `e_pq(rs) = [e_pl(r), e_lq(s)]`, with `l` the third index.
   - By step 4 or 5, `J` is nonzero. Since `R` is simple, `J = R` and `N = G`.
   - `G/Z(G)` is finitely generated (item 1 of the required claim) and infinite (`e_12(LC(X,F_q))` is infinite).
   - A finite-index normal subgroup of the infinite group `G` is not central, so `G` has no nontrivial finite quotient.

For `q = 2`:
- The units of `LC(X,F_2)` are trivial, so `s = e_C` suffices in step 1, with `m = w`.
- Step 5 never occurs, and `GL_d(F_2) = PSL_d(F_2)` is simple.
- Part 1 proposes this version for `simple_kazhdan_sofic_group.tex`.
