# sk-verify-16 part 4: wave-11 queue lines 71–73, sk-algebraic-putnam part 2 (2026-09-13)

Lane sk-verify-16, an independent verifier serving `sk/queue/sk-verify-13.txt` lines 71–73. Every step below was re-derived by hand from `research/artifacts/sk-algebraic-putnam-2026-09-13-part2.md` and the claim and route nodes on main at tip b3556e93e0.

## 0. Verdicts
| line | claim | verdict |
|---|---|---|
| 71 | `cantor-crossed-product-idempotents-similar-to-clopen-ones` | **PASS** |
| 72 | `minimal-cantor-crossed-products-have-internal-cancellation` | **PASS** (conditional on the Gottschalk–Hedlund import) |
| 73 | `cantor-crossed-product-idempotent-pairs-are-stable` | **PASS** (item 3 conditional on the Camillo–Yu import) |

No FAIL, no GAP.

## 1. Line 71: Theorem DP
**One cut.**
- **Directness of Σ** from E ∩ E′ = 0 and V_− ∩ V_+ = 0.
- **Coordinates outside the window lie in Σ.** For t < c − w both eδ_t and (1−e)δ_t lie in V_−.
- **Local complements.** window_− → V_−/Σ_− is onto with kernel window_− ∩ Σ_−. So a coordinate complement M_− exists, and likewise M_+, with V = Σ ⊕ M and dim M ≤ 2w.
- **Locality.** P_−m ∈ E_− ⊕ E′_− iff eP_−m ∈ V_−, since then eP_−m ∈ E ∩ V_− and (1−e)P_−m = P_−m − eP_−m ∈ E′ ∩ V_−.
- **M = Ĩ ⊕ Ĩ′.** If ξ − η ∈ Σ with ξ ∈ E, η ∈ E′, write ξ − η = σ + σ′ (σ ∈ E_±, σ′ ∈ E′_±). Then ξ − σ = η + σ′ ∈ E ∩ E′ = 0, so [ξ] = 0.
- **Laplace step.** [pr′(B); pr(B)] is the matrix of id_M from the coordinate basis B to (basis of Ĩ) ∪ (basis of Ĩ′), hence invertible. Expanding along the first p rows gives T with both minors nonzero. So S ∩ Ĩ′ = S ∩ ker pr′ = 0 (pr′|_S is an isomorphism), S ⊕ Ĩ′ = M, S′ ⊕ Ĩ = M, and S and S′ split along M_− ⊕ M_+. Valid over any field.
- **Split idempotent.** e_c agrees with e on Σ and splits along V_− ⊕ V_+. On M = S ⊕ S′, e_c m is the S-component, so Δ_c = e_c − e is supported in a window [c−2w, c+2w) with local entries.
- **Intertwiner.** e_ce + (1−e_c)(1−e) = 1 − e − e_c + 2e_ce = 1 + Δ_c(2e−1), using e² = e.
  - h_ce = e_ce = e_ch_c.
  - On E, h_c = e_c. It is the identity on E_±, and modulo E_± it is [ξ] ↦ (S-component), bijective from Ĩ to S since S′ ∩ Ĩ = 0 and dim S = p. Injectivity also uses Σ ∩ E = E_− ⊕ E_+.
  - On E′, h_c = 1 − e_c maps onto ker e_c, since S ∩ Ĩ′ = 0.
  - Δ_c(2e−1)δ_t = 0 unless |t−c| < w, because (2e−1)δ_t ∈ Σ for |t−c| ≥ w. So h_c = identity ⊕ (finite window matrix), with a local inverse.

**All cuts.**
- Heights > 4w + 2 make the windows disjoint, so Δ_cΔ_{c′} = 0. The one-cut identity eΔ_c + Δ_ce + Δ_c² = Δ_c comes from e_c² = e_c, and gives e″² = e″.
- Each Δ_{c′} lies on one side of c, so e″ splits at every cut and lies in A_𝒫 after refining atoms.
- h = 1 + Σ_cΔ_c(2e−1) is the identity plus disjoint invertible window blocks, so h ∈ R^× and e″ = heh⁻¹.
- In ∏M_{h_a}(F), rank-k_a idempotents are similar to coordinate idempotents, which gives e_W. The M_n(R) version on V^n gives diag(e_{W_1},…,e_{W_n}).

**Model test.** (e_V + e_Vu)² = e_V + e_Vu since e_Vue_V = e_{V∩TV}u = 0, and (1+e_Vu)e_V(1+e_Vu) = e_V + e_Vu. Checked.

## 2. Line 72: internal cancellation
- **Bounded sums.** x ∈ e_WRe_{W′} of propagation w maps V_{W′} ∩ span{δ_t : t ∈ [m+w, m′−w)} injectively into V_W ∩ span{δ_t : t ∈ [m,m′)}. So |Σ_{t∈J}(1_W − 1_{W′})(T^tx_0)| ≤ 2w for every interval J.
- **Coboundary.** Gottschalk–Hedlund on the minimal system gives f = g∘T − g with g continuous. Birkhoff sums are integers, so g − g(x_0) ∈ C(X,Z) by density and continuity.
- **Level matching.** Over a clopen Z on which g is constant, first-return towers refining {W,W′} have Σ_{j<h}f(T^jz) = g(T^hz) − g(z) = 0. So there are equally many W- and W′-levels, and equally many complement levels.
- **Units.** For γ = T^k on U_k, w_γ = Σ_k e_{γU_k}u^k = Σ_k u^k e_{U_k}, with inverse Σ_k e_{U_k}u^{−k} (w_γw_γ⁻¹ = Σ_k e_{T^kU_k} = 1). So w_γe_Vw_γ⁻¹ = Σ_k e_{T^k(U_k∩V)} = e_{γV}, and e_{X∖W} is similar to e_{X∖W′}.
- **Cancellation** for general idempotents via line 71. Similarity comes from v = x″ + s″.
- **Wording (optional).** In the artifact §4 and the route, `x` denotes both the base point and the equivalence element. Rename the point `x_0`.

## 3. Line 73: idempotent pairs, unit-regularity, conditional sr 1
**1. Idempotent pairs.**
- αr = (1−e)(1−es) = 1−e.
- π = rα is idempotent via (1−e)α = α, and απ = α.
- π ~ 1−e by α·πr(1−e) = 1−e and πr(1−e)·α = π.
- Internal cancellation gives z ∈ eR(1−π), z′ ∈ (1−π)Re with zz′ = e, z′z = 1−π.
- g = α + z = a + e(z−a).
- (α+z)(r(1−e)+z′e) = (1−e) + 0 + 0 + e, using αz′ = α(1−π)z′ = 0 and zr = z(1−π)r = z(r − r(1−e)) = zre.
- (r(1−e)+z′e)(α+z) = π + 0 + 0 + (1−π), using (1−e)z = 0 and eα = 0.

**2. Unit-regularity (Ehrlich).**
- With x = xax, p = ax and q = xa: a = paq and x = qxp.
- Internal cancellation gives s ∈ (1−q)R(1−p), t ∈ (1−p)R(1−q), with st = 1−q and ts = 1−p.
- xt = xp(1−p)t = 0, sa = s(1−p)pa = 0, as = aq(1−q)s = 0, tx = t(1−q)qx = 0. So v = x + s has inverse a + t, and ava = a.

**3. Conditional.** If R is an exchange ring, then sr(R) = 1 by Camillo–Yu (secondary quotation, arXiv:1402.4706) together with item 2.

## 4. Not checked
- Gottschalk–Hedlund and Camillo–Yu at primary source (both secondary quotations).
- Novelty beyond the lane's bounded search. The C*-analogues (Putnam) are norm-approximation results and do not subsume these ring statements.
