---
rg: 2
id: wreath-candidate-embeds-in-finitary-permutation-extension-proof
kind: route
title: Send each lamp to the transposition of its two copies and use ICC local finiteness
target: wreath-candidate-embeds-in-finitary-permutation-extension
requires:
  - wreath-not-sofic
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
---

**Item 1.**  For `x in X` let `tau_x = ((x,0) (x,1)) in Sym_fin(Y)`.  The
`tau_x` are commuting involutions with disjoint supports, so a finite product
`prod_(x in F) tau_x` is trivial only for `F` empty; hence
`x |-> tau_x` extends to an injective homomorphism `directSum_X C_2 -> Sym_fin(Y)`.
For `g in G`, conjugating the transposition `tau_x` by the permutation `g`
gives the transposition of the images, `g tau_x g^(-1) = tau_(gx)`.  So the
map `(a, g) |-> (prod_(x in a) tau_x, g)` is a homomorphism
`(directSum_X C_2) rtimes G -> Sym_fin(Y) rtimes G`; it is injective because
its kernel consists of pairs with `g = 1` and empty `a`.

**Item 2.**  `Sym_fin(Y)` is the increasing union of the finite groups
`Sym(F)`, `F` finite, so it is countable and locally finite.  It is ICC: for
a nonidentity `sigma`, choose `y` moved by `sigma`; for each `z` fixed by
`sigma`, the conjugate of `sigma` by `(y z)` moves `z`, so distinct `z` give
distinct conjugates, and there are infinitely many `z`.  The group von
Neumann algebra of a countable ICC group is a `II_1` factor with separable
predual, and for a locally finite group it is injective (an increasing union
of finite-dimensional algebras), hence isomorphic to `R` by Connes'
theorem.  The conjugation action of `G` on `Sym_fin(Y)` induces a
trace-preserving action `alpha` on `L(Sym_fin(Y))`, and
`L(Sym_fin(Y) rtimes G) = L(Sym_fin(Y)) rtimes_alpha G` because the
semidirect product is the group crossed product.

**Item 3.**  Subgroups of sofic groups are sofic, so item 1 and
`wreath-not-sofic` show `Sigma_2(X)` is not sofic; subgroups of hyperlinear
groups are hyperlinear, so hyperlinearity of `Sigma_2(X)` gives that of `W`,
which together with `wreath-not-sofic` is the Q3.4 separation.

**Item 4.**  Write `H = Sym_fin(Y)` and suppose `alpha_g = Ad(w)` on `L(H)`
with `w in U(L(H))`.  Then `w lambda_h = lambda_(g h g^(-1)) w` for all
`h in H`.  Expanding `w = sum_k c_k lambda_k` with `(c_k) in ell^2(H)` and
comparing coefficients gives `c_k = c_(g h g^(-1) k h^(-1))` for all `h, k`:
the coefficient function is constant on the orbits of the twisted action
`k |-> (g h g^(-1)) k h^(-1)` of `H`.  An `ell^2` function vanishes on infinite
orbits, so `w != 0` forces a finite orbit, i.e. a `k in H` whose twisted
stabilizer `{h : (g h g^(-1)) k = k h} = C_H(k^(-1) g)` has finite index in
`H`.  But `k^(-1) g` moves infinitely many points of `Y` (as `k` is finitary
and `g` is not), and conjugating it by transpositions `(y z)` with `y` moved
and `z` fixed produces infinitely many distinct conjugates, so its
centralizer in `H` has infinite index.  Hence `w = 0`, a contradiction, and
`alpha_g` is outer.
