---
rg: 2
id: exact-levi-affine-relative-stability-fails
kind: claim
title: Exact-Levi relative flexible HS-stability of the affine group fails on the Weil--Heisenberg family
distinct_from:
  isw-corollary-b-uses-only-the-standard-area-cocycle: that records the Ioana--Spaas--Wiersma mechanism refuting the local lifting property of C*(Z^2 x| SL_2(Z)) by pointwise-trivial area cocycles; this uses the irreducible Schroedinger--Weil block of the same level-p family to refute a Hilbert--Schmidt stability statement relative to an EXACT Levi, by a Mackey orbit count, with no C*-algebra involved.
  tracial-to-uniform-lifting-for-sl-n-z: that is the open lifting claim for SL_N(Z); this fences one proof strategy for it (Steinberg column gluing over an exact Levi) by exhibiting column data that no exact rho-equivariant column can approximate, and says nothing about the lifting claim itself.
  direct-sum-weil-compressions-have-quadratic-padding: that is a padding ledger for compressed even Weil blocks as Iwahori boundary data on SL_2(Z[1/2]); this concerns the column Z^2 of the affine group Z^2 x| SL_2(Z) and the rigidity of its genuine extensions of a fixed Levi representation.
---

Let `G = Z^2 x| SL_2(Z)` (standard action), `p` an odd prime,
`zeta = exp(2 pi i / p)`.  On `C^p` let `X` be the clock
`X e_k = zeta^k e_k`, `Z` the shift `Z e_k = e_(k+1)`, so `Z X = zeta X Z`,
`rho(v) = X^(v_1) Z^(v_2)` for `v in Z^2`, and let
`W_p : SL_2(Z) -> U(p)` be the Weil representation through `SL_2(F_p)` (a
genuine representation for `p` odd; `W_p = W^+ (+) W^-` irreducible of
dimensions `(p+1)/2` and `(p-1)/2`), normalized so that

```text
W_p(g) rho(v) W_p(g)^(-1) = omega_g(v) rho(g v),   omega_g(v) in mu_p.  (EL1)
```

Put `phi_p(v, g) = rho(v) W_p(g)`.  This is the irreducible
Schroedinger--Weil block of the level-`p` Ioana--Spaas--Wiersma family
(`isw-corollary-b-uses-only-the-standard-area-cocycle`).

**THEOREM.**

(a) `phi_p` is an asymptotic representation of `G` in OPERATOR norm whose
restriction to the Levi `SL_2(Z)` is the exact representation `W_p`:
for `x, y` in the word ball of radius `m` of a fixed generating set,

```text
|| phi_p(x) phi_p(y) - phi_p(xy) ||_op <= 2 pi q(m) / p,              (EL2)
```

with `q(m) < infinity` depending only on `m` and the generating set, not on
`p`, because every defect is a scalar `zeta^(integer)` coming from
`rho(v) rho(w) = zeta^(v_2 w_1) rho(v + w)` and from `(EL1)`.

(b) Let `pi` be ANY unitary representation of `G` on `C^p (+) C^r` whose
Levi restriction is block diagonal, `pi|_(SL_2(Z)) = W_p (+) sigma`, with

```text
r < (p - 3) / 2.                                                      (EL3)
```

Then `pi(v)` acts as the identity on the block `C^p` for every `v in Z^2`.
Consequently, in normalized Hilbert--Schmidt norm on `C^(p+r)`,

```text
|| pi(e_1) - (X (+) 1_r) ||_2 >= sqrt(2p / (p + r)),                  (EL4)
```

and the same for `e_2` against `Z (+) 1_r`.

(c) Hence the relative form of flexible Hilbert--Schmidt stability in which
the Levi is held EXACT -- "an almost-representation of `G` that is a genuine
representation on `SL_2(Z)` is, after padding by `o(d)` dimensions on which
the Levi may act arbitrarily, close to a genuine representation of `G`
restricting to the same Levi representation on the original block" --
is FALSE with a uniform gap `sqrt 2 - o(1)`, in every norm (the defect in
`(EL2)` vanishes even in operator norm).

**What this fences.**  The Steinberg column-gluing residue recorded on
`tracial-to-uniform-lifting-for-sl-n-z` -- given an exact Levi representation
`rho` of `SL_(n-1)(Z)` and almost-column data, produce an exact
`rho`-equivariant column -- cannot be established for arbitrary column data:
the triple `(W_p, X, Z)` is admissible input (exact Levi, column defect
`O(1/p)` in operator norm) with no exact output nearby.  Any lift of
representations of `SL_N(Z)` through the column step must therefore use the
ambient relations (the opposite column/row and the Heisenberg commutators
`[x_(ij), x_(jk)] = x_(ik)`), or the property (T) of the ambient lattice, and
not only the affine subgroup's own almost-representation.

**What this does NOT say.**  Nothing is claimed when the Levi is merely
`||.||_2`-close to `W_p`: `SL_2(Z)` has no property (T), so a genuine
representation `2`-close to `W_p (+) sigma` on generators need not have
`W_p` as a subrepresentation, and the full flexible HS-stability question
for `Z^2 x| SL_2(Z)` (Dogon's central-extension theorem territory, and
`sln-z-flexibly-hs-stable` for the ambient lattice) is untouched.  Nor
does it refute `tracial-to-uniform-lifting-for-sl-n-z`: an
almost-representation of `SL_N(Z)` restricting to `(W_p, X, Z)` on an affine
subgroup would have to satisfy the opposite-column relations as well, and
no such object is exhibited here.
