# Deligne's triple cover: twisted group algebras in characteristic prime to three (lane w4-deligne-twisted, 2026-09-12)

Target: the linear residue left by lane w3-deligne (`deligne-triple-cover-surjunctivity-2026-09-12.md`,
Section 4). Notation as there:

```text
1 -> C_3 = <z> -> E_3 -> Gamma = Sp_4(Z) -> 1,
```

with a set section `s`, `s(1) = 1`, and `s(g)s(h) = z^(a(g,h)) s(gh)`. Fix a prime `p != 3` and a field `F`
of characteristic `p` containing a primitive cube root of unity `w`. For `j = 1, 2` the twisted group algebra
`A_j = F^(w^(j a))[Gamma]` is the central summand `e_j F[E_3]` (w3-deligne, Lemma 4.1).

Nothing here decides whether some `A_j` is stably finite. What is proved:
- Section 1: `A_j` has no nonzero finite-dimensional module.
- Section 2: `E_3` is `F_p`-linear sofic exactly when the Deligne multiplier has rank-approximate projective
  representations in characteristic `p`, with no separation condition (Theorem 2.1). Such representations
  make both twisted algebras stably finite; a one-sided pair in a twisted algebra would make `E_3` a
  non-linear-sofic group.
- Section 3: truncating a fixed monomial twisted module along coordinate Folner sets never works
  (Proposition 3.1, property (T)).
- Section 4: where it stops.

## 0. Conventions

For `X in M_d(K)` write `r(X) = rank(X)/d`. It is unchanged by extension of scalars and by restriction of
scalars along a finite extension. For invertible `X, Y`, `r(X^(-1) - Y^(-1)) = r(X^(-1)(Y - X)Y^(-1)) = r(X - Y)`,
and transposition keeps rank.

A countable group `G` is `K`-linear sofic (Arzhantseva--Paunescu, as recorded at
`binary-leavitt-unit-group-is-f2-linear-sofic`) if there is `delta > 0` such that for every finite `B' <= G`
and `eps > 0` there are `N` and `sigma : B' -> GL_N(K)` with
- `r(sigma(g)sigma(h) - sigma(gh)) <= eps` whenever `g, h, gh in B'`, and
- `r(sigma(g) - 1) >= delta` for `g in B' \ {1}`.

An `F_p`-model is an `F`-model for every field `F` of characteristic `p`, since rank does not change under
extension of scalars. So `F_p`-linear soficity gives `F`-linear soficity for all such `F`.

## 1. No finite-dimensional modules

**Lemma 1.1.** Let `K` be any field of characteristic `p != 3` containing `w`, and `j in {1, 2}`. Every
`A_j`-module of finite `K`-dimension is zero. So every `A_j`-module that is a union of finite-dimensional
submodules is zero.

*Proof.* A nonzero finite-dimensional `A_j`-module `V` is a `K[E_3]`-module on which `e_j` acts as `1`, so `z`
acts as `w^j`. This gives `rho : E_3 -> GL(V)` with `rho(z) = w^j I != I`. The image is a finitely generated
linear group, hence residually finite (`finitely-generated-linear-groups-are-residually-finite`). A finite
quotient of `rho(E_3)` separating `rho(z)` from `1` is a finite quotient of `E_3` not killing `z`, against
`deligne-triple-cover-finite-residual-is-center`.

So exact finite-dimensional models of the twisted algebras do not exist, every approximate model must have
growing dimension, and any exact module whose truncations are used must not be locally finite.

## 2. The rank sector equivalence

Say the multiplier `w^(j a)` has **rank-approximate projective representations in characteristic `p`** if for
every finite `B <= Gamma` and `eps > 0` there are a finite field `F` of characteristic `p` containing `w`,
`d >= 1`, and `rho : B -> GL_d(F)` with

```text
r( rho(g) rho(h) - w^(j a(g,h)) rho(gh) ) <= eps     whenever g, h, gh in B.     (RPA)
```

**Theorem 2.1** (`deligne-cover-linear-soficity-is-rank-projective-approximation`). For a prime `p != 3` the
following are equivalent:
1. `E_3` is `F_p`-linear sofic.
2. For some `j in {1, 2}`, `w^(j a)` has rank-approximate projective representations in characteristic `p`.
3. Both `w^a` and `w^(2a)` have them.

No separation condition appears in 2 and 3.

### 2.2 From projective models to linear soficity (2 => 1): tensor camouflage

Take `delta = 1/2`. Given a finite `B' <= E_3` and `eps in (0, 1/2)`, write each `e in B'` uniquely as
`e = s(g) z^i` and let `B` be the set of these `g`. If `e, e', ee' in B'` then `g, h, gh in B`.
- `Gamma` is residually finite (`finitely-generated-linear-groups-are-residually-finite`), so there is a
  finite-index normal `L <= Gamma` with `g notin L` for every `g in B \ {1}`. Let `pi` be the regular
  representation of `Q = Gamma/L` by `m x m` permutation matrices, composed with `Gamma -> Q`.
- Take `rho` as in (RPA) on `B` and put `sigma(s(g) z^i) = w^(j i) rho(g) (x) pi(g)` in `GL_(dm)(F)`.

*Defect.* For `e = s(g)z^i` and `e' = s(h)z^k` we have `ee' = s(gh) z^(a(g,h)+i+k)`, so

```text
sigma(e)sigma(e') - sigma(ee') = w^(j(i+k)) ( rho(g)rho(h) - w^(j a(g,h)) rho(gh) ) (x) pi(gh),
```

whose normalized rank is at most `eps`.

*Separation, `g != 1`.* `pi(g)` is a direct sum of `m/o` cyclic permutation blocks `C_o`, where `o >= 2` is the
order of `gL`. For any `X in GL_d(F)`, a vector `(v_0, ..., v_(o-1))` in the kernel of `X (x) C_o - 1` satisfies
`v_(i+1) = X v_i` and `X^o v_0 = v_0`, so the kernel has dimension at most `d`. Hence
`r(X (x) pi(g) - 1) >= 1 - 1/o >= 1/2`. Apply this with `X = w^(ji) rho(g)`.

*Separation, `g = 1`, `i != 0`.* (RPA) at `g = h = 1` (where `a(1,1) = 0`) gives `r(rho(1)^2 - rho(1)) <= eps`.
Since `rho(1)` is invertible, `r(rho(1) - 1) <= eps`. So `r(sigma(z^i) - 1) >= r((w^(ji) - 1) I) - eps = 1 - eps`.

Restricting scalars from `F` to `F_p` keeps all normalized ranks, so `E_3` is `F_p`-linear sofic.

### 2.3 From linear soficity to projective models (1 => 2): cutting into a sector

Let `sigma : B' -> GL_N(F_p)` be a model with defect `eps` and separation `delta`, on a finite symmetric `B'`
containing `1, z, z^2` and `s(g), s(g^(-1)), z s(g), s(g) z, z^2 s(gh), s(g)s(h)` for `g, h` in a finite symmetric
`B <= Gamma` containing `1` and closed enough that the products below lie in `B'`. Extend scalars to
`F = F_p(w)` and write `M = sigma(z)`, `X_g = sigma(s(g))`. All ranks below are in dimension `N`.

*(a) Rounding z.* As in 2.2, `r(sigma(1) - 1) <= eps`. Writing
`M^3 - 1 = (M^2 - sigma(z^2))M + (sigma(z^2)M - sigma(1)) + (sigma(1) - 1)` gives `r(M^3 - 1) <= 3 eps`.
`U = ker(M^3 - 1)` is `M`-invariant of codimension at most `3 eps N`. With a complement `W`, put
`Z = M|_U (+) 1_W`. Then `Z^3 = 1` and `r(Z - M) <= 3 eps`.

*(b) Almost central projections.* `P_j = (1/3) sum_(i=0..2) w^(-ij) Z^i` are idempotents with
`P_0 + P_1 + P_2 = 1` and `Z P_j = w^j P_j`; this uses `3 != 0` in `F`. Both `M X_g` and `X_g M` are within
`eps` of `sigma(z s(g)) = sigma(s(g) z)`, so `r([M, X_g]) <= 2 eps`. Hence:
- `r([Z, X_g]) <= 2 eps + 6 eps = 8 eps`;
- `r([Z^2, X_g]) <= 16 eps`, from `[Z^2, X] = Z[Z,X] + [Z,X]Z`;
- `r([P_j, X_g]) <= 24 eps`.

*(c) A heavy sector.* `Z - 1 = (w - 1)P_1 + (w^2 - 1)P_2`, so `r(Z - 1) = r(P_1) + r(P_2)`, and
`r(Z - 1) >= r(M - 1) - 3 eps >= delta - 3 eps`. Choose `j in {1, 2}` with `r(P_j) >= (delta - 3 eps)/2`.

*(d) Compression.* Let `V = P_j F^N`, `d = dim V`, and `rho(g) = P_j X_g |_V`. On `V`,
`P_j X_h v = X_h v + [P_j, X_h] v`, so `rho(g)rho(h) = P_j X_g X_h |_V + E_1` with `rank E_1 <= 24 eps N`. Next,
`X_g X_h` is within `eps` of `sigma(z^(a) s(gh))`, which is within `eps` of `sigma(z^a) X_gh`. Also `sigma(z^a)` is
within `eps` of `M^a` and within `7 eps` of `Z^a`. Finally `P_j Z^a = w^(ja) P_j`. So

```text
rank( rho(g) rho(h) - w^(j a(g,h)) rho(gh) ) <= 33 eps N <= (66 eps / (delta - 3 eps)) d.
```

*(e) Invertibility.* `rho(1) = P_j sigma(1)|_V` is within rank `eps N` of `1_V`. Applying (d) to `(g, g^(-1))`
shows that `rho(g)rho(g^(-1))` is within rank `34 eps N` of the invertible `w^(j a(g,g^(-1))) 1_V`, so `rho(g^(-1))`
has nullity at most `34 eps N`. Changing each `rho(g)` on a subspace of that dimension makes it invertible,
and the defects grow to at most `135 eps N`, that is, at most `(270 eps/(delta - 3 eps)) d` in dimension `d`.

*Uniform choice of j.* For each pair `(B, eps)` some `j` works, and a `j` that works at `(B, eps)` works at every
smaller pair. If `j = 1` failed at `(B_1, eps_1)` and `j = 2` failed at `(B_2, eps_2)`, then neither could work at
`(B_1 cup B_2, min eps_i)`. So one `j` works everywhere, which is 2.

### 2.4 Sector symmetry (2 <=> 3)

If `rho` satisfies (RPA) for `j`, then `rho^v(g) = (rho(g)^T)^(-1)` satisfies it for `3 - j`:

```text
rho^v(g) rho^v(h) = ((rho(g) rho(h))^T)^(-1),     w^(-j a(g,h)) rho^v(gh) = ((w^(j a(g,h)) rho(gh))^T)^(-1),
```

and `r(X^(-1) - Y^(-1)) = r(X - Y)` for invertible `X, Y`. This proves Theorem 2.1.

**Corollary 2.5 (linear automata on E_3).** Let `p != 3`.
- **Consequence.** If `w^a` has rank-approximate projective representations in characteristic `p`, then
  `F[E_3]` is stably finite for every field `F` of characteristic `p`. So both twisted algebras are stably
  finite, and `E_3` carries no strict `F`-linear automaton over finite `F` of characteristic `p`. This uses
  Theorem 2.1, Section 0, `linear-sofic-group-algebra-is-stably-finite`, and w3-deligne Remark 1.5.
- **Contrapositive.** A pair `ba = 1 != ab` in some `M_n(A_j)` over a finite field of characteristic `p`, padded
  by the unit of the other factors, is a one-sided pair in `M_n(F[E_3])`.
  - It gives a strict linear automaton on `E_3` (`stable-finiteness-failure-refutes-surjunctivity`).
  - It shows `E_3` is not `F`-linear sofic, hence not `F_p`-linear sofic, and not sofic
    (`sofic-implies-linear-sofic-over-every-field`).
  - That makes `E_3` a witness for `non-linear-sofic-group`.

**Remark 2.6 (the tracial version).** `deligne-sector-gap-is-exactly-nonhyperlinearity` is the same
camouflage-and-cut argument in normalized Hilbert--Schmidt norm, for unitary almost representations. Rank
defects over finite fields and HS defects over `C` are not comparable objects; neither theorem transfers to
the other.

**Remark 2.7 (characteristic three).** The cut in 2.3 needs `3` invertible. In characteristic `3`,
`F[E_3]` is stably finite unconditionally (w3-deligne, Theorem 2.1). Whether `E_3` is `F_3`-linear sofic is
not addressed here.

## 3. Monomial twisted modules have no Folner truncations

Call an `F[E_3]`-module `M` a **monomial twisted module** if `z` acts as `w^j` for some `j in {1, 2}` and `M` has
a basis `X` such that every element of `E_3` sends each basis vector to a nonzero multiple of a basis vector.
Then `E_3` permutes the lines `F x`, `z` acts trivially on them, and `Gamma` acts on `X`. A **Folner truncation**
is a sequence of finite nonempty `F_n <= X` with `|s F_n symdiff F_n| / |F_n| -> 0` for `s` in a finite generating
set of `Gamma`.

Truncating `M` to the span of `F_n`, and completing the partial monomial matrices to monomial matrices, would
give (RPA) models with defect `O(|s F_n symdiff F_n| / |F_n|)`.

**Proposition 3.1** (`deligne-monomial-twisted-modules-have-no-folner-truncations`). No monomial twisted module
has a Folner truncation.

*Proof.*
1. The unit vectors `1_(F_n) / |F_n|^(1/2)` in `l^2(X)` are almost invariant under `Gamma`.
2. `Gamma = Sp_4(Z)` has property (T) (a lattice in the higher-rank group `Sp_4(R)`), so `l^2(X)` has a nonzero
   invariant vector. Its level sets are finite invariant sets, so some `x in X` has a finite `Gamma`-orbit.
3. Let `Lbar` be the stabilizer of `x`, of finite index in `Gamma`, and `L` its preimage in `E_3`. Every element of
   `L` maps `x` to a multiple of `x`, which gives a character `chi : L -> F^x` with `chi(z) = w^j != 1`.
4. `E_3` has property (T), being a finite central extension of `Gamma`, so the finite-index subgroup `L` has (T)
   and finite abelianization. So `ker chi` has finite index in `L`, hence in `E_3`, and does not contain `z`.
5. Its normal core is a finite-index normal subgroup of `E_3` missing `z`, against
   `deligne-triple-cover-finite-residual-is-center`.

**Remark 3.2 (scope).**
- **What it excludes:** coordinate truncations of one fixed module, in particular twisted induced modules
  `Ind_L^(E_3) chi` over any subgroup.
- **What it does not exclude:** intrinsically varying monomial models, which are sofic approximations of `E_3`
  (`deligne-triple-cover-is-sofic`, open).
- **Non-monomial subspaces:** property (T) gives no rank rounding over finite fields
  (`kazhdan-group-rank-models-admit-no-expander-decomposition`: `EL_3(F_2[t])` has rank-Folner truncations of
  its polynomial module). So Proposition 3.1 has no automatic analogue for non-monomial subspace truncations.
  By Lemma 1.1 such a module could not be locally finite.
- **Relation to the tracial fence:** this is the characteristic-`p` coordinate analogue of
  `deligne-fixed-projective-representation-folner-compression-no-go`. That one is for HS compressions of
  unitary projective representations and goes through amenable traces.
