---
rg: 2
id: matui-transformation-and-reduction-citation
kind: route
title: Import of Matui 2012, Proposition 3.5 and Theorem 3.6, plus the chain-level check that transformation groupoid homology is group homology
target: matui-groupoid-homology-transformation-and-reduction
requires: []
artifacts:
  - research/artifacts/cantor-configuration-modules-v-acyclic-germ-groupoid-2026-09-16.md
---

**Source.** H. Matui, *Homology and topological full groups of étale groupoids on totally
disconnected spaces*, Proc. London Math. Soc. 104 (2012), arXiv:0909.1624.

**How it was read.** On 2026-09-16 the arXiv e-print TeX source was fetched and gunzipped
into the session scratchpad as `matui/m12.tex`. The quotes below come from that file.
The e-print's own filename is `htfgeg.tex`. On 2026-09-16 the referee fetched it
independently and confirmed the quotes and line numbers below.

**Numbering.** The file declares `\newtheorem{thm}{Theorem}[section]`, and `lem`, `prop`,
`cor`, `df` and `rem` share its counter. Counting environments in Section 3 gives the
following:
- Definition 3.1, label `homology`, l.421;
- Remark 3.2, l.433;
- Definition 3.4, label `similarity`, l.569;
- Proposition 3.5, label `homosim`, l.588;
- Theorem 3.6, label `reduction`, l.626.

The transformation groupoid is defined in Definition 2.1 (l.266).

**Verbatim.**
- Convention (l.221–223): "by an \'etale groupoid we mean a locally compact Hausdorff
  groupoid such that the range map is \'etale."
- Fullness and reduction (l.229–237): "A subset $F\subset G^{(0)}$ is said to be $G$-full,
  if $r^{-1}(x)\cap s^{-1}(F)$ is not empty for any $x\in G^{(0)}$. [...] For an open
  subset $F\subset G^{(0)}$, the reduction of $G$ to $F$ is $r^{-1}(F)\cap s^{-1}(F)$ and
  denoted by $G|F$."
- Definition 2.1 (l.266–277): "We let $G_\phi=\Gamma\times X$ and define the following
  groupoid structure: $(\gamma,x)$ and $(\gamma',x')$ are composable if and only if
  $x=\phi^{\gamma'}(x')$, $(\gamma,\phi^{\gamma'}(x'))\cdot(\gamma',x')=(\gamma\gamma',x')$
  and $(\gamma,x)^{-1}=(\gamma^{-1},\phi^\gamma(x))$."
- After Remark 3.2 (l.443–450): "Let $\phi:\Gamma\curvearrowright X$ be an action of a
  discrete group $\Gamma$ on a locally compact Hausdorff space $X$ by homeomorphisms. With
  pointwise addition $C_c(X,A)$ is an abelian group, and $\Gamma$ acts on it by
  translation. One can check that $H_n(G_\phi,A)$ is canonically isomorphic to
  $H_n(\Gamma,C_c(X,A))$, the homology of $\Gamma$ with coefficients in $C_c(X,A)$."
- Proposition 3.5(2) (l.588–597): "If $G$ and $H$ are homologically similar, then they
  have isomorphic homology with constant coefficients $A$."
- Theorem 3.6 (l.626–637): "Let $G$ be an \'etale groupoid and let $F\subset G^{(0)}$ be an
  open $G$-full subset. [...] (2) Suppose that $G^{(0)}$ is $\sigma$-compact and totally
  disconnected. Then $G$ is homologically similar to $G|F$."

**Check of item 1 (the "One can check").** The source and range of `(γ, x)` are `x` and
`φ^γ(x)`, and the face maps are those of Matui's Section 3.1 (l.387–400).

1. A composable string `((γ_1, x_1), ..., (γ_n, x_n))` has `x_i = φ^{γ_{i+1}}(x_{i+1})`.
   So it is determined by `(γ_1, ..., γ_n, x_n)`, and `G_φ^(n) ≅ Γ^n × X` as spaces.
2. `Γ` is discrete, so a compactly supported function on `Γ^n × X` meets only finitely
   many sheets `{γ} × X`. Hence
   `C_c(G_φ^(n), A) = ⊕_{Γ^n} C_c(X, A) = Z[Γ^n] ⊗ M`, where `M = C_c(X, A)`. The string
   `[γ_1|...|γ_n] ⊗ m` corresponds to `m` placed on the sheet `(γ_1, ..., γ_n)`.
3. The face maps act as follows.
   - `d_0` forgets `γ_1` and fixes `x_n`, so `d_{0*}` sends `[γ_1|...|γ_n] ⊗ m` to
     `[γ_2|...|γ_n] ⊗ m`.
   - For `1 ≤ i ≤ n−1`, `d_i` multiplies `γ_i γ_{i+1}` and fixes `x_n`, so `d_{i*}` sends
     the string to `[...|γ_iγ_{i+1}|...] ⊗ m`.
   - `d_n` forgets `γ_n` and replaces the base point by `x_{n−1} = φ^{γ_n}(x_n)`. So
     `(d_{n*} f)(γ_1..γ_{n−1}, y) = Σ_{γ_n} f(γ_1..γ_n, φ^{γ_n^{−1}}(y))`, and `d_{n*}`
     sends the string to `[γ_1|...|γ_{n−1}] ⊗ γ_n·m`. Here `(γ·m)(y) = m(φ^{γ^{−1}}(y))`
     is translation.
   - `δ_1 = s_* − r_*` sends `[γ] ⊗ m` to `m − γ·m`.
4. These are the differentials of the standard inhomogeneous bar complex computing
   `Tor^{ZΓ}_*(Z, M) = H_*(Γ; M)`, up to the overall sign of `δ_1`, which does not change
   homology.

Every identification is natural, so the isomorphism is canonical. The chain-level check
itself uses neither countability of `Γ` nor total disconnectedness of `X`. Matui's
Definition 2.1 (l.268) does state the transformation groupoid for "a countable discrete
group". That hypothesis holds here, because `V` is countable.
