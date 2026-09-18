---
rg: 2
id: ckn-forces-nonsofic-incompressible-affine-coset-wreath-proof
kind: route
title: Put the compressor outside the Kazhdan envelope, move the root lamp, and split the lamp set into envelope orbits
target: ckn-forces-nonsofic-incompressible-affine-coset-wreath
requires:
  - elek-szabo-sofic-permanence
  - arithmetic-integral-subgroup-is-incompressible
  - affine-semidirect-sl3-source-has-property-t
---

Conventions. `[a,b] = a b a^-1 b^-1`. In `B^(X) semidirect H` the group `H` acts on the left on
`X` and on lamps by `h e_x(b) h^-1 = e_(hx)(b)`, where `e_x(b)` is the lamp with value `b` at
`x` and `1` elsewhere. Semidirect products `V semidirect S` of a module by a linear group use
`(v,A)(w,C) = (v + A w, A C)`, so `(v,A)^-1 = (-A^-1 v, A^-1)`.

## Step 1: (CK2), the hypotheses

`u L u^-1 = alpha(L) <= L`, so `u in Comp_(G_0)(L)`, and the same holds in `W'` because
`G_0 <= W'`. For every `n >= 0`, `u^-n L u^n = alpha^-n(L) <= M`, because `alpha` is an
automorphism of `M`. So the union lies in `M`, which is Kazhdan by hypothesis. `L` is Kazhdan by
hypothesis.

## Step 2: (CK3), the conclusion fails

The stabilizer of the coset `x_0 = L` in `G_0` is `L`. So `e_(x_0)(b)` commutes with every
`l in L`, and it commutes with every lamp. Hence `e_(x_0)(b) in C_(W')(L)`.

Conjugating by `u` gives `u e_(x_0)(b) u^-1 = e_(u x_0)(b)`. Pick `l in L \ alpha(L)`; it exists
because `alpha(L) < L` strictly. Then

```text
l e_(u x_0)(b) l^-1 = e_(l u x_0)(b),
l u x_0 = u x_0   iff   u^-1 l u in L   iff   l in u L u^-1 = alpha(L).
```

So `l u x_0 != u x_0`. Taking `b != 1`,
`[e_(u x_0)(b), l] = e_(u x_0)(b) e_(l u x_0)(b)^-1` is supported on two distinct points, hence
nontrivial. Therefore `u C_(W')(L) u^-1` is not contained in `C_(W')(L)`, and `u` does not
normalize `C_(W')(L)`. This is the defect generator of
`kun-thom-wreath-carries-rigid-defect`, with the compressor now outside the Kazhdan
envelope.

## Step 3: the orbit decomposition of `X`

Let `h: G_0 -> Z` be the height, with `h(M) = 0` and `h(u) = 1`. `M` is normal in `G_0`, and
`G_0 = M <u>` with `M ∩ <u> = 1`. Every coset has the form `m u^k L` with `m in M` and `k in Z`.
The integer `k` is the height of any representative, because `h(L) = 0`. So the `M`-orbits on
`X` are

```text
X_k = M u^k L   (k in Z),   pairwise disjoint,   Stab_M(u^k L) = M ∩ u^k L u^-k = alpha^k(L).
```

The last equality uses `alpha^k(L) <= M`.

For each `k` the map `beta_k: M/L -> X_k`, `m L -> alpha^k(m) u^k L`, is well defined and
bijective. Indeed, `alpha^k(m) u^k L = u^k m L`, so `beta_k(mL) = u^k (mL)`. It intertwines
`m'` with `alpha^k(m')`:
`beta_k(m' m L) = alpha^k(m') beta_k(m L)`. Hence

```text
Phi_k: W_M -> B^(X_k) semidirect M,    (f, m) -> (f o beta_k^-1, alpha^k(m)),        (CK11)
```

is an isomorphism of groups. It is the restriction of conjugation by `u^k` in `W'`.

## Step 4: (CK4), soficity transfer

All permanence facts used are Elek--Szabo Theorem 1 (`elek-szabo-sofic-permanence`): subgroups,
finite direct products, direct limits (increasing unions), and extensions with sofic kernel and
amenable quotient.

*Only if.* `B^(X_0) semidirect M <= W'`, and it is isomorphic to `W_M` by (CK11) with `k = 0`.

*If.* Assume `W_M` sofic.
- `M` preserves each `X_k`. So `N = B^(X) semidirect M` is the increasing union over `r` of
  `N_r = B^(X_(-r) ⊔ ... ⊔ X_r) semidirect M`.
- The map `N_r -> prod_(|k|<=r) (B^(X_k) semidirect M)`, `(f, m) -> ((f|X_k, m))_k`, is a
  homomorphism, because `M` preserves each `X_k`. It is injective, because `f` is determined
  by its restrictions.
- Each factor is isomorphic to `W_M` by (CK11). So `N_r` is sofic, and hence `N` is sofic.
- `N` is normal in `W'`, since `u` permutes the `X_k` and normalizes `M`, and `W'/N` is
  isomorphic to `G_0/M`, which is `Z`. By the amenable-extension clause `W'` is sofic.

This proves (CK4). Now (CK5) follows: if `W_M` were sofic, `W'` would be a sofic group
satisfying the CKN hypotheses (Step 1) but not its conclusion (Step 2).

## Step 5: (CK7), the affine triple

`D = Z[1/p]`. `alpha(v, A) = (p v, A)` is conjugation by `pI`, which is central in
`GL_3(D)`. It is an automorphism of `M_p` because `p` is a unit of `D`. Then
`alpha(L) = pZ^3 semidirect SL_3(Z)`, of index `p^3` in `L`; for example `(e_1, I)` is not in
it.

**`L` is Kazhdan.** `L = Z^3 semidirect SL_3(Z)` is exactly (AT1) of
`affine-semidirect-sl3-source-has-property-t`.

**`M_p` is Kazhdan.** This is the standard lattice argument.
- `D` is a cocompact lattice in `R x Q_p`, diagonally.
- `SL_3(D)` is a lattice in `SL_3(R) x SL_3(Q_p)` (Borel--Harish-Chandra; this is the
  S-arithmetic lattice with `S = {infinity, p}`).
- So `M_p = D^3 semidirect SL_3(D)` is a lattice in `H_R x H_p`, where
  `H_F = F^3 semidirect SL_3(F)`.
- For a local field `F`, `H_F` has property (T): `SL_3(F)` has (T), `(H_F, F^3)` has relative
  property (T), and an extension of a (T) quotient by a normal subgroup with relative (T) has (T).
- Products of (T) groups have (T), and lattices inherit (T).

The ring-theoretic route of `affine-semidirect-sl3-source-has-property-t` (Ershov--Jaikin-Zapirain
Theorem 1.1 at `R = D`, plus a relative (T) statement for the pair) would also work. Only the
lattice route is used here, because the relative (T) proposition was source-checked there only at
`R = Z`.

`M_p` does not need to be torsion-free or finitely presented here.

## Step 6: (CK8), incompressibility

Let `g = (v, A) in M_p` with `g L g^-1 <= L`.

*Linear part.* The projection `pi: M_p -> SL_3(D)` maps `L` onto `SL_3(Z)`. Hence
`A SL_3(Z) A^-1 <= SL_3(Z)`. By parts (1) and (2) of `arithmetic-integral-subgroup-is-incompressible`
(for `n = 3`, `g = A in GL_3(Q)`), `A in SL_3(Z) . Z(SL_3(D))`. The centre of `SL_3(D)` consists
of the scalars `lambda I` with `lambda^3 = 1` and `lambda in D`, a subring of `Q`, so `lambda = 1`.
Thus `A in SL_3(Z)`.

*Translation part.* Put `g' = g (0, A)^-1 = (v, I)`. Then `g'` also compresses `L`, because
`(0, A) in L`. For `C in SL_3(Z)`,

```text
(v, I)(0, C)(v, I)^-1 = (v, C)(-v, I) = (v - C v, C).
```

This lies in `L` only if `(I - C) v in Z^3`. Taking `C = I + E_ij` with `i != j` gives
`(I - C) v = -v_j e_i`, so `v_j in Z`. Since every `j` has some `i != j`, `v in Z^3`. So
`g' in L` and `g in L`.

Conversely `L <= Comp_(M_p)(L)`. Hence `Comp_(M_p)(L) = L`. The subgroup this generates is `L`,
not `M_p`, so `L` is not infranormal in `M_p`, and Kun--Thom Theorem 4.1 is silent on
`(M_p, L)`.

In `W'`, `M_p <= G_0 <= W'`, so `Comp_(W')(L) ∩ M_p = L`. Every compressor of `L` in `W'` that is
not already in `L` (for instance `u`) lies outside the Kazhdan envelope `M_p`.

## Step 7: (CK9), the summit embedding

Let `S = {(0, A) : A in SL_3(D)} <= M_p`. It is isomorphic to `SL_3(D)`. Let `Y = S . L` be the
`S`-orbit of the base coset in `M_p / L`. Its stabilizer is `S ∩ L = {(0, A) : A in SL_3(Z)}`. So
`Y` is isomorphic, as an `S`-set, to `SL_3(D) / SL_3(Z)`.

`Y` is `S`-invariant. So the finitely supported functions `Y -> C_2`, together with `S`, generate
the subgroup `C_2^(Y) semidirect S` of `W_aff,p`, and this subgroup is isomorphic to `W_p`.
Thus `W_p <= W_aff,p`, and by the subgroup clause of Elek--Szabo, `W_aff,p` sofic implies `W_p`
sofic.

## Step 8: (CK10), assembly

- Apply (CK5) to the triple of Step 5, with `B = C_2`. Then `W_M = W_aff,p`, so CKN implies
  `W_aff,p` is not sofic.
- By Step 7, `W_p` not sofic implies `W_aff,p` not sofic.
- The contrapositives of the two lines give the third line of (CK10).

Step 6 is not used in these implications. It records that `(M_p, L)` is outside the Kun--Thom
mechanism, so (CK10) is not a consequence of any known theorem.

## What was not shown

- Whether `W_aff,p` is sofic. This is open. It is at least as hard as `W_p` on the sofic side.
- Whether `W_aff,p` contains some other infranormal Kazhdan pair that would make it nonsofic by
  Kun--Thom. Step 6 excludes only the pair `(M_p, L)`.
- Anything about hyperlinearity. CKN is a soficity statement, and the transfer in Step 4 is
  used only for soficity.
- Whether CKN is true. This shows only that it is at least as strong as the nonsoficity of
  `W_aff,p`.
