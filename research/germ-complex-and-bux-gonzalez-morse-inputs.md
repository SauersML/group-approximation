---
rg: 2
id: germ-complex-and-bux-gonzalez-morse-inputs
kind: claim
title: Imported inputs for Morse theory on germ complexes, from Belk–Hyde–Matucci and from Bux–Gonzalez as quoted by Witzel–Zaremsky
distinct_from:
  rover-nekrashevych-finite-presentation-criteria: that imports finite presentation, simplicity and abelianization of V_d(H); this imports the germ complex of a finite germ extension, its cell stabilizers and cocompactness, the F_infty inputs for bounded automata groups, and the Bux–Gonzalez criterion with the Morse Lemma.
---

**ESTABLISHED by citation (route `germ-complex-and-bux-gonzalez-morse-inputs-citation`; unreviewed).** This node imports
statements only. The exact sources, labels and quotations are in the route.

**(FGE) Finite germ extensions.** `B <= G <= Homeo(X)` with `X` Hausdorff, and `sing(h)` is the set of points where `h`
agrees with no element of `B` on any neighbourhood. `G` is a *finite germ extension* of `B` when:

1. every `g in G` has finite `sing(g)`;
2. `B` is exactly the set of elements of `G` without singular points;
3. for `g in G` and `p in sing(g)` there is `h in G` with `sing(h) = {p}` agreeing with `g` near `p`.

`sing(G)` is the union of the `sing(g)`. Also `sing(kh) ⊆ h^{-1} sing(k) ∪ sing(h)`.

**(K) The germ complex.**

- `(g)_p` is the germ of `g` at `p`, and `(Bg)_p = {(bg)_p : b in B}` is its `B`-germ. `Bgerm(G,p)` is the set of `B`-germs at `p`.
  - `(G)_p = Stab_G(p)/RStab_G(p)` is the group of germs.
  - Composition of germs is `(g)_{h(p)} (h)_p = (gh)_p`.
- `T_p` is the star with centre `*` and one leaf for every element of `Bgerm(G,p)`, based at `(B)_p`.
- `K` is the restricted product of the `T_p` over `p in sing(G)`. Its vertices are the partial portraits: finitely many
  nontrivial germs and finitely many `*`, the *hidden points*.
- `G` acts on the left by `g·(Bh)_p = (Bhg^{-1})_{g(p)}` and `(g·γ)(p) = g·γ(g^{-1}p)`.
- `μ(γ)` is the number of hidden points, and `K_{<=n}` is the union of the cubes on which `μ <= n`.

**(Stab)** Every cube stabilizer in `K` has a finite-index subgroup conjugate to
`SingFix_G(M,M') = {g : sing(g) ⊆ M, g|_{M'} = id}`, where `|M'|` is the largest number of `*` at a vertex of the cube.
If `|(G)_p : (B)_p| < ∞` for every `p in M`, then `Fix_B(M')` has finite index in `SingFix_G(M,M')`.

**(Orb)** `G` has finitely many orbits of cubes in `K_{<=n}` iff `B` has finitely many orbits on `sing(G)^n`.

**(Conn)** `K_{<=n}` is `(n-1)`-connected for `n >= 1`.

**(Fin)** If `B` has finitely many orbits on `sing(G)^n`, `Fix_B(M)` has type `F_n` for all `|M| <= n`, and
`|(G)_p:(B)_p| < ∞` for all `p in sing(G)`, then `G` has type `F_n`.

**(RN) Bounded automata groups.** Let `G <= Aut(T_d)` be a bounded automata group and `r >= 1`. Then:

- `V_{d,r}G` is a finite germ extension of `V_{d,r}`;
- `|(V_{d,r}G)_p : (V_{d,r})_p| < ∞` for all `p in sing(V_{d,r}G)`;
- `Stab_{V_{d,r}}(M)`, and hence `Fix_{V_{d,r}}(M)`, has type `F_∞` for every finite `M ⊆ sing(V_{d,r}G)`;
- `V_{d,r}` has finitely many orbits on `sing(V_{d,r}G)^n` for every `n`;
- `V_{d,r}G` has type `F_∞`.

**(BG) Bux–Gonzalez criterion (working definition).** Let `G` be of type `F_m` and act cellularly on an
`(m-1)`-connected CW complex `Y`. Suppose `k`-cell stabilizers have type `F_{m-k}` and `G` acts cocompactly on `Y^{(m)}`.
Let `χ` be a nonzero character and `h: Y -> R` continuous with `h(gy) = χ(g) + h(y)`. Then `[χ] in Σ^m(G)` iff the
filtration `(Y_{t<=h})_{t in R}` of full subcomplexes is essentially `(m-1)`-connected.

**(ML) Morse Lemma.** Let `Y` be an affine cell complex and `(h,s)` a Morse function: both affine on cells, `s` finitely
valued on vertices, and for some `ε > 0` adjacent vertices satisfy `|h(v)-h(w)| >= ε`, or else `h(v) = h(w)` and
`s(v) != s(w)`. Let `p <= q <= r` lie in `R ∪ {±∞}`. Suppose every vertex of `Y_{p<=h<q}` has `(k-1)`-connected ascending
link in `Y_{h<=r}`. Then the pair `(Y_{p<=h<=r}, Y_{q<=h<=r})` is `k`-connected. Ascending links are full subcomplexes.

## Attempts

- Imported to prove `germ-extension-base-trivial-characters-lie-in-sigma`.
