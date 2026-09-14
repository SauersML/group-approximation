# Permutational wreath products are surjunctive exactly when the stabilizer products are

Lane `gk-n-ff`, 2026-09-12. Supports `wreath-surjunctivity-reduces-to-stabilizer-products`.
[W] below is `research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md`, whose
conventions are used throughout.

## Theorem

Let `G` be a group, `X` a left `G`-set, and `A` any group. Put `N = (+)_(x in X) A`
and `W = A wr_X G = N x| G`, with `(g.n)(x) = n(g^-1 x)`. For finite `U` in `X`,
let `G_U` be the pointwise stabilizer of `U` (so `G_(empty) = G`), and write `A^U`
for the functions `U -> A`. Then

```text
W is surjunctive   <=>   A^U x G_U is surjunctive for every finite U in X.
```

No finiteness, residual finiteness or soficity of `A` is assumed.

## Only if

`A^U` embeds in `N` as the functions supported in `U`. An element `h` of `G_U`
fixes `U` pointwise, so `h.n = n` for every such `n`. Hence `A^U` and `G_U`
commute inside `W` and meet trivially, so `A^U x G_U <= W`. Subgroups of surjunctive
groups are surjunctive (`surjunctivity-passes-to-subgroups`).

## If

Assume every `A^U x G_U` is surjunctive, and let `tau` be an injective cellular
automaton over `W` with memory `M`, rule `mu` and finite alphabet `B`. The proof
is [W]'s marked-site peeling with the lamp values kept as group coordinates
rather than folded into the alphabet. Only the changes are written out.

**1. Separating family.** For finite `S` in `X`, put
`H_S = { (n,1) : n(s) = 1 for s in S }`. [W, Lemma 1.2] applies to the family of all
`H_S`. Take distinct `w, w'` in a finite `F`. Either `w' w^-1` lies outside `N`, or
it equals `(n' n^-1, 1)` with `n' n^-1 != 1`. Taking `S` to contain the supports of
these finitely many elements makes every `w' w^-1` lie outside `H_S`. No finite
quotient of `A` is used.

**2. Coordinates.** `H_S(n,g) = H_S(n',g')` iff `g = g'` and `n|_S = n'|_S`. So
`Omega_S = H_S\W` is identified with `A^S x G`, with right action

```text
(a,g).(n_1,g_1) = ( a . nu_(n_1)(g),  g g_1 ),        nu_(n_1)(g)(s) = n_1(g^-1 s),
```

where `a . nu` is the pointwise product in `A^S`.

**3. The transplanted map lives on a group.** Regard `Omega_U` as the group
`Lambda_U = A^U x G` (direct product). With `m = (n_m, g_m)`, the transplant of
[W, Lemma 1.1] reads

```text
tau_U(y)(lambda) = mu( ( y(lambda p_m(g)) )_(m in M) ),     lambda = (a,g),
p_m(g) = ( nu_(n_m)(g)|_U , g_m )  in Lambda_U.
```

Each `nu_(n_m)(g)|_U` takes values in the finite set of values of `n_m` together
with `1`. So `P_U = { p_m(g) : m in M, g in G } u {1}` is finite, and `tau_U` is a
finite-memory map on `B^(Lambda_U)`: its memory is `P_U`, and its rule at `lambda`
depends on `lambda`. [W, Conventions] defines finite-memory maps only on `C^G`,
over the base group with a finite alphabet `C`. Here the same definition is read
over the group `Lambda_U` with the finite alphabet `B`. This is forced: `A^U` may be
infinite, so folding it into the alphabet, as [W] does with `C = B^(Abar^U)`, is
not available. `tau_U` is injective by
[W, Lemma 1.1].

**4. Invariance.** Put `K_U = A^U x G_U`, a subgroup of `Lambda_U`. For
`k = (b,h)` in `K_U`, `p_m(hg) = p_m(g)`, because `(hg)^-1 s = g^-1 s` for `s` in
`U`, and `p_m` does not depend on the `A^U` coordinate. So the rules satisfy
`mu_(k lambda) = mu_lambda`, and `tau_U` commutes with left translation by `K_U`.

**5. Strata and slices.** `L = union supp(n_m)` and
`Z_s = { g : g^-1 s in L }` are as in [W, Lemma 2.2]. Off `Z_s`, `nu_(n_m)(g)(s) = 1`.
For `V` in `U` write `Lambda_U = A^V x A^(U\V) x G`. [W, Lemma 2.3] holds verbatim:
off every `Z_s` with `s` in `U\V`, `tau_U` acts slicewise over `A^(U\V)` as `tau_V`.
Nothing here uses finiteness of `A`.

**6. Peeling.** [W, Proposition 4.1] holds with `Lambda_U` in place of `Omega_U`, and
with (c) reading "commuting with left translations by `K_U`". The slicewise
extension of `rho_(U')^-1` commutes with `A^U x G_(U')`, which contains `K_U`: for
`k = ((c,d),h)` with `c in A^(U')`, `d in A^(U\U')` and `h in G_(U')`, one has
`(k.y)_lambda = (c,h).y_(d^-1 lambda)`, and `rho_(U')^-1` commutes with
`A^(U') x G_(U')`. In the window argument for (b), the memories are finite subsets of
`Lambda_U`, and every condition used there (a point lying in some `Z_s` or in some
`Q_(U')`) concerns only the `G` coordinate. So `F_U` is built from the
`G`-projections of the memories `P_k`, and (b) reads `rho_U(y)(a,g) = y(a,g)` for
every `a` and every `g` not in `Q_U = intersection_(s in U) Z_s F_U^-1`. The
exceptional region is `A^U x Q_U`. If `Q_U = G_U h_1 u ... u G_U h_r`, then
`A^U x Q_U = K_U (1,h_1) u ... u K_U (1,h_r)` is a finite union of right cosets of
`K_U`.

**7. Coset-region lemma.** [W, Lemma 3.1] is stated for `K <= G` and finite-memory
maps on `C^G`. Its proof uses only that `K` is a subgroup of the ambient group and
that the alphabet is finite. So it holds verbatim for a subgroup `K` of any group
`Lambda` and finite-memory maps on `B^Lambda`. Apply it inside `Lambda_U` to `rho_U`,
with `K = K_U`, which is surjunctive by hypothesis, `R = A^U x Q_U`, and alphabet `B`.
The rules of `rho_U` are left-`K_U`-invariant on `R`. `rho_U` commutes with left
translations by `K_U` (step 6), and a finite-memory map `rho` commuting with left
translation by `k` satisfies `mu_(k lambda) = mu_lambda`, because the points
`lambda p`, `p in P`, are distinct and `y` is arbitrary. The map `Psi` of that lemma
is then a cellular automaton over `K_U` with alphabet `B^(r+q)`, and `rho_U` is bijective
with a finite-memory inverse commuting with `K_U`. For `U = empty`, `Lambda_empty = G`,
`K_empty = G`, and `tau_empty` is an injective automaton over `G`, which is
surjunctive by hypothesis.

**8. Conclusion.** As in [W, Section 5]: `rho_S = Sigma o tau_S` is bijective, so
`tau_S` is surjective for every finite `S`, and `tau` is surjective by
[W, Lemma 1.2]. QED

## Consequences

- **Standard wreath products.** When `X = G` with the regular action,
  `G_U = 1` for `U != empty`. So `A wr G` is surjunctive iff `G` and every finite
  power `A^n` are surjunctive.
- **Reduction of wreath closure to product closure.** If surjunctivity is closed
  under finite direct products, then `A wr_X G` is surjunctive whenever `A` and `G`
  are, for every `G`-set `X`. The stabilizers `G_U` are subgroups of `G` and hence
  surjunctive. Closure under finite direct products is open.
- **Sofic lamps.** If `A` and `G` are sofic, every `A^U x G_U` is sofic, hence
  surjunctive, so `A wr_X G` is surjunctive for every action, even when `W` is not
  sofic. The residually finite and LEF lamp theorems
  (`rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`,
  `lef-lamp-graph-wreaths-are-surjunctive`) need only a surjunctive base. This case
  allows sofic lamps that are not LEF but needs a sofic base. Neither statement
  contains the other.
- **Inside the Fournier--Facio group.** The simple wreath shift `S wr Z`
  (`fournier-facio-group-contains-simple-wreath-shift`) is surjunctive iff every
  finite power `S^n` is. `Z` is residually finite, and the regular action has
  trivial stabilizers.
- **Compatibility.** For LEF `A` and surjunctive `G`, every `A^U x G_U` is
  surjunctive by `products-with-lef-factors-preserve-surjunctivity` and heredity. So
  the present theorem reproves the permutational case of
  `lef-lamp-graph-wreaths-are-surjunctive` from that product theorem.
- **Closure.** Closure of surjunctivity under permutational wreath products is the
  open `permutational-wreaths-of-surjunctive-groups-are-surjunctive` (gk-p-products).
  By this theorem it is equivalent to closure under binary direct products.
