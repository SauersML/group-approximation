# Permutational Boone--Higman beyond the binary Leavitt unit group (2026-09-13)

Lane `solve-leavitt-pbh-general`. It extends 19108f02e, which established
`binary-leavitt-unit-group-satisfies-pbh`. Nothing here has been independently reviewed.

## Results

| Node | Status | Content |
|---|---|---|
| `countable-graph-leavitt-path-algebras-embed-in-binary-leavitt` | ESTABLISHED (import) | Brownlowe–Sørensen Theorem 4.1 |
| `char-two-leavitt-path-unit-groups-satisfy-pbh` | ESTABLISHED | every `L_F(E)^x`, `F` finite of characteristic two, `E` countable with `E^0` finite |
| `char-two-curve-linear-groups-satisfy-permutational-boone-higman` | ESTABLISHED | characteristic-two curve and free-algebra linear inputs lie in `B_A` |
| `mixed-characteristic-linear-products-satisfy-pbh` | ESTABLISHED | `G_0 × G_2` with char-0 and char-2 linear factors, e.g. `SL_3(Z) × SL_3(F_2[t])` |
| `higman-thompson-cantor-module-products-are-fp` | ESTABLISHED | `Map_0(C_n, A) ⋊ V_(n,1)` of type `F_∞` for every `n >= 2` and finite abelian `A` |
| `prime-field-leavitt-unit-groups-satisfy-pbh` | OPEN for odd `p` | through route `prime-field-leavitt-pbh-via-covered-module-amalgam` |
| `odd-prime-leavitt-unit-groups-are-fp-and-covered` | OPEN | the one missing premise for odd `p` |

## Source pins

### Brownlowe–Sørensen, arXiv:1503.08705v3

The PDF was fetched on MSI (`/scratch.global/sauer354/lpg/bs.pdf`) and converted with
`pdftotext -layout` (`bs.txt`). The extraction puts subscripts on separate lines; they are
restored in brackets below.

- l.4–5 (abstract): "For a commutative ring R with unit we show that the Leavitt path algebra
  LR(E) of a graph E embeds into L2,R precisely when E is countable."
- l.22–27: "the Cuntz algebras O[n] are natural C∗-algebraic analogues of the Leavitt algebras
  LK(1,n) — they are universal for the same deﬁning relations (in each their category) and
  L[C](1,n) is dense in O[n]. Partly for this reason we denote L[K](1,n) by L[n,K] from here on
  out."
- l.396–401, **Theorem 4.1**: "Let R be a commutative ring with unit and let E be a directed
  graph. If E is countable, then there is a ∗-algebraic embedding of the Leavitt path algebra
  L[R](E) into L[2,R], and if E0 is ﬁnite, then this embedding can be chosen to be unital. If E
  is uncountable then there is no embedding of LR(E) into L2,R as R-modules."

### Martínez-Pérez–Matucci–Nucinkis, arXiv:1309.7858v2

The e-print was fetched on MSI (`/scratch.global/sauer354/lpg/mmn.tar`, gzip of
`2014-10-01-F-infty.tex`) and read from the TeX (`mmn.tex`).

- l.376: "we say that $\Sigma$ is {\sl valid} if for any admissible $Y\subseteq W_\Omega(X)$, we
  have $|Y|=|\overline Y|$, where $\overline Y$ is the image of $Y$ under the epimorphism
  $W_\Omega(X) \twoheadrightarrow U_r(\Sigma).$"
- l.422: "We say that $U_r(\Sigma)$ is {\sl bounded} [...] if for all admissible subsets $Y$ and
  $Z$ such that there is some admissible $A\leq Y,Z$, there is a unique least upper bound of $Y$
  and $Z$."
- l.458–464, Example 2.7(ii): "Furthermore one can also consider $s$ colours, all of arity
  $n_i=n\in \N,$ for all $1\leq i\leq s.$ Let $$\Sigma_2:=\{\alpha_i^l\alpha_j^t=\alpha_j^t\alpha_i^l
  \mid 1\leq i \not= j\leq s; 1\leq l,t\leq n \}.$$ Here $V_r(\Sigma)=sV_n$ is Brin's group of
  arity $n.$ It was shown in \cite[Example 2.9]{britaconcha} that in this case $U_r(\Sigma)$ is
  valid and bounded."
- l.637–641, Definition 2.14: "Using the notation of Definition \ref{sigmadef}, suppose that for
  all $i\neq i'$, $i,i' \in S$ we have that $\Sigma_2^{i,i'} \neq \emptyset$ and that $f(j)=i'$ for
  all $j=1,...,n_i$ and $f'(j')=i$ for all $j'=1,...,n_{i'}$. Then we say that $\Sigma$ (or
  equivalently $U_r(\Sigma)$) is {\sl complete}."
- l.847–849, Remark 4.3: "In \cite{matuccietc}, where the ordinary Higman-Thompson group
  $V_r(\Sigma)=V_{n,r}$ is considered, the subgroups $K_i$ are described as
  $\text{Map}^0(\mathfrak{C},L)$, where $\mathfrak{C}$ denotes the Cantor set, and $\text{Map}^0$
  the set of continuous maps. Here the Cantor set is viewed as the set of right infinite words in
  the descending operations."
- l.1029–1031, Corollary 4.11: "Suppose $U_r(\Sigma)$ is valid, bounded and complete. Then
  $V_r(\Sigma)$ is of type quasi-$\F_\infty$. In particular, centralisers of finite groups are of
  type $\F_\infty$."

**Reading used.** One colour (`s = 1`) of arity `n` with `r` roots gives `V_(n,r)`. For one colour
`Σ_2` is empty and completeness is vacuous.

## The steps

1. **Graphs.** Brownlowe–Sørensen give unital injective `L_F(E) -> L_F(1,2)`. Step (b) of
   `leavitt-unit-groups-over-finite-fields-mutually-embed-proof` gives `L_(F_(2^k))(1,2)^x ->
   L_(F_2)(1,2)^x`. Composing with the binary type (A) actor gives the permutational property.
2. **Linear inputs.** The Boone--Higman nodes for characteristic-two curve and free-algebra
   linear groups already embed them in `L_(F_2)(1,2)^x`. So they lie in `B_A`. Products with
   characteristic-zero linear groups follow from permanence of `B_A`.
3. **All arities.** `Map_0(C_n, A) ⋊ V_(n,1)` is the centralizer in `V_(n,|A|)` of `A` permuting
   the `|A|` roots freely. This is a direct coordinate computation, and Corollary 4.11 applies.
4. **Odd characteristic.** With step 3 for `A = F_p`, the covering subgroups `c(h, k)` of
   elementary transvections and diagonal units, and `amalgamated-module-extensions-are-fp`,
   permutational Boone--Higman for `L_(F_p)(1,2)^x` reduces to finite presentation plus a covered
   generating set.

## Not done

- **Odd `p`.** No finite presentation of `L_(F_p)(1,2)^x` and no covered generating set were
  found or proved. Khanh's criteria, as quoted on main, are stated in characteristic two.
- **Q3.4.** The only finitely presented simple member on main is `L_(F_2)(1,2)^x`. Whether other
  unit groups `L_(F_(2^k))(E)^x`, or their commutator subgroups, are finitely presented and simple
  was not settled. Topological full groups of graph groupoids sit inside `L_F(E)^x` as monomial
  units, but that embedding was not written down here.
- **Novelty.** No literature search beyond the sources above.
