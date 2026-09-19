---
rg: 2
id: swap-twist-centralizer-proof
kind: route
title: An elliptic element commuting with a hyperbolic one fixes its axis pointwise, and the axis meets three explicit stabilizers
target: swap-twist-centralizer-is-the-congruence-core
requires: []
---

Let `T` be the Bass--Serre tree of `E = Gamma *_Lambda (Lambda x <s>)`:
type-1 vertices `g Gamma`, type-2 vertices `g (Lambda x <s>)`, edges
`g Lambda`.  Write `v_0 = Gamma`, `u_0 = Lambda x <s>`, so `v_0` and
`u_0` are adjacent and `h u_0` is at distance `2` from `u_0` through
`v_0` (`h notin Lambda`).

**Fixed sets.**  `s` fixes `u_0`.  A neighbouring type-1 vertex `g v_0`,
`g in Lambda x <s>`, is fixed by `s` iff `g^(-1) s g in Gamma`; but
`Lambda x <s>` is a direct product, so `g^(-1) s g = s notin Gamma`.
Hence `Fix(s) = {u_0}` and likewise `Fix(h s h^(-1)) = {h u_0}`: two
elliptic involutions with disjoint one-point fixed trees at distance
`2`.

**Hyperbolicity and the dihedral group.**  The product of two elliptic
isometries of a tree whose fixed trees are disjoint is hyperbolic with
translation length twice the distance between the fixed trees, and its
axis contains the geodesic between them.  So `z = s (h s h^(-1))` is
hyperbolic with translation length `4` and axis `l` through
`u_0, v_0, h u_0`.  Since `Fix(s)` and `Fix(hsh^(-1))` are single points,
no alternating product of the two involutions can be trivial (each factor
strictly increases displacement off the other's fixed point), so
`<s, h s h^(-1)> ~= C_2 * C_2 = D_infinity`; alternatively this is the
amalgam normal form of `arithmetic-double-swap-extension-proof` for the
distinct cosets `Lambda != h Lambda`.

**The centralizer.**  `C_0 <= C_Gamma(z)`: for `c in C_0`,
`c s c^(-1) = s` (`c in Lambda`) and
`c (h s h^(-1)) c^(-1) = h (h^(-1) c h) s (h^(-1) c h)^(-1) h^(-1) =
h s h^(-1)` (`h^(-1) c h in Lambda` because `c in h Lambda h^(-1)`).

Conversely let `gamma in Gamma` commute with `z`.  `gamma` is elliptic
(it fixes `v_0`) and commutes with the hyperbolic `z`, so it preserves
the axis `l` and acts on `l ~= R` as an isometry commuting with the
translation by `4`; an isometry of `R` commuting with a nontrivial
translation is itself a translation, and an elliptic element acts on `l`
with a fixed point, so `gamma` translates by `0`: it fixes `l`
POINTWISE.  In particular it fixes `u_0` and `h u_0`, so

```text
gamma in Gamma cap (Lambda x <s>) cap h (Lambda x <s>) h^(-1)
      = Lambda cap h Lambda h^(-1) = C_0.
```

(`Gamma cap (Lambda x <s>) = Lambda` since the parity of `s` is killed
in `Gamma`.)  This proves `(ZC1)`.  The congruence description of `C_0`
for `h = diag(p, 1, 1/p)` is the entry computation
`(h g h^(-1))_(ij) = p^(a_i - a_j) g_(ij)`, `(a_1,a_2,a_3) = (1,0,-1)`:
integrality below the diagonal costs `p | g_21, p | g_32, p^2 | g_31`.
`C_0 supseteq Lambda(p^2)` is immediate, and co-density of `C_0` in
`Gamma` follows from strong approximation for `Lambda(p^2)` at levels
coprime to `p`.
