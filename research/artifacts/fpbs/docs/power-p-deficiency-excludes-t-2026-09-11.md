# Power p-deficiency excludes property (T)

Lane `fixed-price-2`, 2026-09-11. A written deduction from four cited theorems;
not a formal verification.

## Statement

Let `p` be a prime. For a presentation `(X,R)` with `X` finite, put

    def_p(X,R) = |X| - 1 - sum_(r in R) p^(-nu_p(r)),

where `nu_p(r)` is the largest `k>=0` with `r` a `p^k`-th power in `F(X)`.

**Theorem.** If some presentation `(X,R)` of `Gamma` has `def_p(X,R) > 0`, then
`Gamma` does not have property (T). This holds with `R` infinite and `Gamma`
torsion.

## Inputs (read from the sources, 2026-09-11)

- **[SP]** Schlage-Puchta (arXiv:1105.1631), as stated in Ershov, *Golod-Shafarevich
  groups: a survey* (IJAC 2012), Theorem 9.1:
  1. `d_p(G) >= def_p(G)+1`;
  2. for subnormal `H` of `p`-power index, `def_p(H) >= def_p(G)[G:H]`, so
     `(d_p(H)-1)/[G:H] >= def_p(G)`.

  Here `d_p(H) = dim_(F_p) H_1(H;F_p)`.
- **[La]** Lackenby, *Detecting large groups* (arXiv:math/0702571), Theorem 1.12: if
  `G` is finitely presented and its derived `p`-series has linear growth of mod `p`
  homology, i.e. `inf_i d_p(D_i)/[G:D_i] > 0`, then `G` is `p`-large.
- **[Sh]** Shalom, Invent. Math. 141 (2000); openness restated in Stalder,
  arXiv:0803.2592, abstract: property (T) is an open subset of the space of marked
  finitely generated groups.
- **[BdlHV]** Groups with (T) have finite abelianization, and (T) passes to finite
  index subgroups.

## Proof

1. Enumerate `R = {r_1, r_2, ...}` and put `G_k = <X | r_1..r_k>`. The normal
   closures increase to `<<R>>`, so `G_k -> Gamma` in the space of `X`-marked
   groups.
2. Suppose `Gamma` has (T). By [Sh], `G_k` has (T) for all large `k`. Concretely,
   Shalom gives a finite `S` in `<<R>>` with `F(X)/<<S>>` Kazhdan. `S` lies in
   `<<r_1..r_k>>` for large `k`, and quotients of Kazhdan groups are Kazhdan.
3. Dropping relators only increases the deficiency:
   `def_p(G_k) >= def_p(X,{r_1..r_k}) >= def_p(X,R) =: c > 0`.
4. The derived `p`-series `D_i` of `G_k` consists of normal subgroups of `p`-power
   index. By [SP](ii), `d_p(D_i) > c[G_k:D_i]`, so the series has linear growth of
   mod `p` homology. It is strictly descending, since `d_p(D_i) > 0`.
5. `G_k` is finitely presented, so [La] makes `G_k` `p`-large: some finite index
   subgroup maps onto a nonabelian free group, hence onto `Z`.
6. That subgroup has (T) by [BdlHV] and infinite abelianization, a contradiction. QED

## Consequence for `fpbs-kazhdan-positive-rank-gradient`

- **The implication that dies.** Positive power `p`-deficiency implies positive
  `p`-gradient. The image `Gamma'` of `Gamma` in its pro-`p` completion has
  derived `p`-series `D_i(Gamma')`: normal, trivial intersection, so Farber. It
  also has `d_p(D_i(Gamma')) = d_p(D_i(Gamma))`, because the kernel lies in
  `D_(i+1)`. So a Kazhdan group of positive power `p`-deficiency would supply the
  certificate of `creative-branches.md` Section 4. The theorem says no such group
  exists.
- **What this removes.** Schlage-Puchta's `p`-groups and Osin's constructions,
  the known sources of positive `p`-gradient in infinitely presented and torsion
  groups, cannot supply the Kazhdan certificate.
- **The sharp line.** Weighted (Golod-Shafarevich) deficiency is compatible with
  (T): Ershov-Jaikin-Zapirain's `G_(p,d)` is Golod-Shafarevich and Kazhdan for
  `p > (d-1)^2`. Power deficiency, the variant that bounds ordinary `p`-gradient
  from below, is not compatible with (T).
- **What survives.** A residually-`p` Kazhdan group whose mod-`p` homology grows
  linearly along a `p`-chain with trivial intersection. The argument above gives
  nothing there: its finitely presented Kazhdan covers carry the pulled-back
  chain, and Lackenby's (tau) dichotomy (arXiv:math/0509036) allows linear growth
  when (tau) holds along the chain, which (T) guarantees.
