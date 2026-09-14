# SK review 3, part 7: the density patch for the tower argument over topologically free actions

Lane `sk-verify-3`, 2026-09-13. Queue item 16 (sk-universal-embedding-b). Main read at tip `48b2ed608a`.
Artifact: `research/artifacts/sk-universal-embedding-b-proposal-2026-09-13.md`, §(a) LaTeX and §(e).

## Verdict

- **GAP**, with a repair. The sketch in §(e) does not work as written. The repaired argument is correct.
- The Cairn route `lef-groups-embed-in-simple-kazhdan-lef-groups-proof` does not use the patch. It goes through the Steinberg criterion and PASSED in part 6.
- The proposal's LaTeX needs about four more sentences before it is a complete proof.

## 1. The gap

**What freeness is used for.** The note's tower proof uses freeness twice.
- (i) It needs a clopen partition with C ∩ γC = ∅ for γ in a ball. That lets the non-commuting root h = e_ij(s) be taken with s in a B_1-tower.
- (ii) That tower must be disjoint, so that k = [g,h] lies in M_3(B_m(U)).
- (ii) only needs C to be "small": disjoint from its translates by nontrivial elements of B_(2w+2). Small sets exist near points whose stabilizer meets that ball trivially.

**The sketch in §(e).** It says a small clopen C contains the finitely many points that the coefficients of F(s) = g sE_ij − sE_ij g read at x.
- For s = e_V u_t, the coefficient of F(s) at u_η and x is Σ_(γt=η) a_γ(x)1_V(γ^(−1)x) − Σ_(tγ=η) 1_V(x) b_γ(t^(−1)x), where the a_γ and b_γ are the coefficients of g's entries.
- So the read points are x and the translates γ^(−1)x, γ ∈ B_w. These are distinct translates of x.
- A set containing x and γ^(−1)x meets its γ^(−1)-translate, so it is not small.
- Hence "agrees near x with the expression for e_(V∩C)u_t" is not available with C small.

## 2. Repair

- **Free points.** Let x have trivial stabilizer in B_(4w+2). Then each read point p = γ^(−1)x (γ ∈ B_w) has trivial stabilizer in B_(2w+2), because ηp = p gives γηγ^(−1) ∈ Stab(x) ∩ B_(4w+2). The set of such x is a finite intersection of complements of the closed sets Fix(η) with empty interior, so it is dense and open.
- **Splitting V.** Choose pairwise disjoint small clopen neighborhoods N_p of the read points, and put N = ⋃N_p. Then e_V u_t = e_(V∖N)u_t + Σ_p e_(V∩N_p)u_t, and F is additive.
  - F(e_(V∖N)u_t) has zero coefficients at x, because 1_(V∖N) vanishes at every read point.
  - Each V ∩ N_p is small. So if g commutes with every e_ij(e_C u_t) for small C, then F(e_(V∩N_p)u_t) = 0.
  - Hence the coefficients of F(e_V u_t) vanish at x.
- **Conclusion.** The coefficients are locally constant and vanish on a dense open set, so they vanish everywhere. Taking V = X and t ∈ S^(±1) ∪ {a}, and t = e with every V, the coefficient subring contains the generators of R, so g is central.
- **The rest.** A non-commuting h = e_ij(e_C u_t) with C small exists. Each such s = e_C u_t = E_(e,t^(−1))(C) lies in the B_1-tower over U = C. The rest of the tower argument (the corner function κ, H_W ≅ GL_d(F_2), the level ideal) uses only smallness of C, and it goes through verbatim, as in part 3 §A5.

## 3. Proposal LaTeX, further UNCLEAR points (no errors found)

1. **Topological freeness.** The case δ = e is omitted. There x ↦ x + f with f ≠ 0 has no fixed point.
2. **"As in Section 1, this is multiplicative".** The lamplighter models are not the note's periodic words. The reader needs the affine formula σ_ℓ(c,q) = (c + Σ_(h∈supp f) 1_(qφ_n(δ^(−1))φ_n(h)), qφ_n(δ^(−1))) and its partial multiplicativity (artifact Lemma 3). One sentence suffices.
3. **Embedding.** The identity gives diag(1, [a^(−1),b^(−1)]). The move to diag(c,1,1) needs conjugation by the permutation matrix w(1)w(−1)… or equivalently "by a coordinate swap in E_2". Half a sentence.
4. **Whitehead (b).** diag(c,c^(−1)) = e_12(c)e_21(−c^(−1))e_12(c)·e_12(−1)e_21(1)e_12(−1). I checked this product: w(c)w(−1) = diag(c, c^(−1)).

## 4. Suggested replacement for the simplicity sentence (reader-facing, same length class)

```latex
For the last step call a clopen set small if it is disjoint from its translates by the
nontrivial elements of a large ball. If $g$ commutes with every $e_{ij}(e_Cu_t)$ with $C$ small,
the coefficients of $ge_Vu_tE_{ij}-e_Vu_tE_{ij}g$ at a point $x$ depend on $1_V$ only at
finitely many translates of $x$. For $x$ with trivial stabilizer in a larger ball, cut $V$ along
small disjoint neighborhoods of these translates; linearity shows that the coefficients vanish
at $x$. Such points form a dense open set, so $g$ commutes with every $e_{ij}(e_Vu_t)$ and is
central.
```
