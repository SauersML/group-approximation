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
finite-memory map on `B^(Lambda_U)` in the sense of [W, Conventions]. Its memory
is `P_U` and its rule at `lambda` depends on `lambda`. `tau_U` is injective by
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
extension of `rho_(U')^-1` commutes with `A^U x G_(U')`, which contains `K_U`. The
exceptional region is `A^U x Q_U`. If `Q_U = G_U h_1 u ... u G_U h_r`, then
`A^U x Q_U = K_U (1,h_1) u ... u K_U (1,h_r)` is a finite union of right cosets of
`K_U`.

**7. Coset-region lemma.** Apply [W, Lemma 3.1] inside `Lambda_U` with `K = K_U`,
which is surjunctive by hypothesis, `R = A^U x Q_U`, alphabet `B` and memory `P_U`.
At `lambda = k (1,h_i)` with `k = (b,h)` in `K_U`, the `G` coordinate of `lambda` is
`h h_i`, and the memory elements selected are `p_m(h h_i) = p_m(h_i)`. By step 4
they depend only on `i`. So the map `Psi` of that lemma
is a cellular automaton over `K_U` with alphabet `B^(r+q)`, and `rho_U` is bijective
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
  sofic. This extends `rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive` from
  residually finite to sofic lamps over sofic bases. The residually finite theorem
  needs only a surjunctive base, so neither statement contains the other.
- **Inside the Fournier--Facio group.** The simple wreath shift `S wr Z`
  (`fournier-facio-group-contains-simple-wreath-shift`) is surjunctive iff every
  finite power `S^n` is. `Z` is residually finite, and the regular action has
  trivial stabilizers.
- **Compatibility.** The residually finite theorem together with the "only if"
  direction shows that `A^n x K` is surjunctive for residually finite `A` and every
  surjunctive `K` that is a stabilizer intersection. That is consistent with,
  though not implied by, the present proof.
