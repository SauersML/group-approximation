# Referee report (citation/hypothesis lens): `gl-n-q-hosts-cannot-act-on-one-manifolds` and `sl-n-z-circle-actions-factor-through-finite-groups`

Referee: lane gq-referee-b, 2026-09-17. Reviewed as landed at 5a140f21e:
- the claim and its `-proof`;
- the Witte import `sl-n-z-circle-actions-factor-through-finite-groups` and its `-citation` route.

## Verdict

**PASS.**
- The mathematics is correct.
- The Witte statement is verified at the secondary source the node names.
- The primary source (PAMS 122 (1994) 333–340) is still unread, and the node already says so. It is a named trust
  surface, and a standard theorem.

## Citation

**Verified at source.** K. Parwani, *Actions of SL(n,ℤ) on homology spheres*, arXiv:math/0504189v1, arXiv HTML,
**Theorem 1.2**, verbatim: "If Γ is a subgroup of finite index in SL(n,ℤ) with n≥3, then every continuous action
of Γ on the circle factors through a finite group action."

Parwani's reference entry reads: "[Wi] D. Witte, Arithmetic groups of higher Q-rank cannot act on 1-manifolds,
Proc. Amer. Math. Soc. 122 (1994), no. 2, 333–340."

**Not read.**
- Witte's paper: there is no arXiv version and the AMS page returned 403.
- Fisher's survey arXiv:0809.4849v2. It mentions Witte Morris but did not yield a quotable statement.

**Hypothesis match.** "Continuous action on the circle" means a homomorphism to `Homeo(S^1)`, with no regularity
assumed. That is exactly what Step 0 of the proof produces.

**Wording fix.** Record "Parwani Thm 1.2" in the citation route.

## Mathematics

- **Step 0.** `Homeo(C) ↪ Homeo(int C) ↪ Homeo(S^1)` for every connected one-manifold `C` that is not a circle:
  - `int C ≅ R` is dense;
  - a homeomorphism of `R` extends to the one-point compactification.
- **Step 1.**
  - The permutation of the finitely many components has a finite-index kernel `Γ_0`.
  - Each component gives a circle action of `Γ_0` with finite image (Witte).
  - Faithfulness gives `⋂K_i = 1`, so `Γ_0` would be finite. That is a contradiction, since finite-index
    subgroups of `SL_3(Z)` are infinite.
  - `SL_3(Z) ↪ SL_n(Z), GL_n(Z), SL_n(Q), GL_n(Q)` for `n >= 3`.
  - **Correct.**
- **Step 2.**
  - A finite-order increasing homeomorphism of `R` is the identity.
  - A decreasing one squares to the identity.
  - `A = [[0,−1],[1,−1]]`: `A^2 = [[−1,1],[−1,0]]` and `A^3 = I`. I computed both.
  - **Correct.**
- **"Not excluded."** `SL_2(Q)` acts faithfully on the circle of rays in `R^2`; `−I` is the antipodal map. So `n = 2`
  circle hosts are genuinely not excluded.
