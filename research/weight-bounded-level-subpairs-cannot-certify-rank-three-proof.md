---
rg: 2
id: weight-bounded-level-subpairs-cannot-certify-rank-three-proof
kind: route
title: Let B permute the Bruhat-Tits buildings of all monomial valuations; the level forces the bounded weights into the positive orthant, invariance pushes them into the dual of cone(H_B R_+^d), and the invariant core of (W2) then excludes every strictly positive weight
target: weight-bounded-level-subpairs-cannot-certify-rank-three
requires:
  - subring-level-subpairs-cannot-certify-rank-three-cone
  - nonneg-generated-kazhdan-groups-have-nonsalient-cones
  - level-subpair-line-sections-are-bounded-or-cofinite
---

Proof of [[weight-bounded-level-subpairs-cannot-certify-rank-three]].  Notation as there.

## Step 0: valuations, completions, buildings

- **(V1)** For `w ∈ R^d`, `v_w` is a valuation on `R`: the `w`-initial form of `fg` is the product of the
  initial forms, which is nonzero because the Laurent ring is a domain.  It extends to `Frac R`.  For
  `w ∈ Q^d \ {0}` with common denominator `N`, the value group is a nonzero subgroup of `(1/N) Z`, so `v_w` is
  discrete of rank one.  Let `K_w` be the completion, `O_w` its valuation ring, `π_w` a uniformiser.
- **(V2)** `X_w` is the Bruhat-Tits building of `SL_3(K_w)`: the simplicial complex of homothety classes of
  `O_w`-lattices in `K_w^3`, with its Euclidean metric.  It is a Euclidean building with finitely many shapes
  of simplices, hence a complete CAT(0) space (Bridson-Haefliger II.10A and II.6).  It is not locally finite,
  since the residue field of `v_w` is infinite; nothing below uses local finiteness.  `GL_3(K_w)` acts by
  isometries.
- **(V3)** *An element `g ∈ SL_3(K_w)` fixing a point `p ∈ X_w` has `tr g ∈ O_w`.*  `p` lies in the interior
  of a unique simplex `s`, with at most three vertices, and `g` permutes them, so `g^6` fixes a vertex `[L]`.
  Then `g^6 L = π_w^j L`, and `det g = 1` forces `j = 0`.  So `g^6 ∈ GL(L) ≅ GL_3(O_w)`, whose characteristic
  polynomial has coefficients in `O_w`.  Every eigenvalue `λ` of `g` (in an algebraic closure, with the unique
  extension of `v_w`) has `λ^6` integral over `O_w`, hence `λ` integral.  So `tr g`, a sum of eigenvalues,
  is integral over `O_w` and lies in `K_w`, so lies in `O_w` (valuation rings are integrally closed).
- **(V4)** *Transport.*  For `σ ∈ SL_d(Z)` let `σ̂` be the ring automorphism `x^m ↦ x^(σ m)` of `R`, applied to
  matrices entrywise.  It permutes monomials, so `v_w(σ̂ f) = min <w, σ m> = min <σ^T w, m> = v_(σ^T w)(f)`.
  So `σ̂ : (Frac R, v_(σ^T w)) → (Frac R, v_w)` is a valuation-preserving isomorphism.  It extends to an
  isomorphism `K_(σ^T w) → K_w` carrying `O_(σ^T w)` onto `O_w`.  Hence it maps `O`-lattices to `O`-lattices and
  induces an isometry `σ̂_* : X_(σ^T w) → X_w` with `σ̂_*(g · p) = σ̂(g) · σ̂_*(p)`.

## Step 1: negative weights (the level)

Let `w ∈ Q^d \ {0}` with `w_l < 0` for some `l`.  Take `n ≥ k` and `a = x_l^n`, so `v_w(a) = n w_l < 0`.  Both
`e_12(a)` and `e_21(a)` lie in `U_k ⊆ E_B`, so `g = e_12(a) e_21(a) ∈ E_B`.  Its upper-left block is
`[[1 + a^2, a], [a, 1]]`, so `tr g = 3 + a^2` and `v_w(tr g) = 2 n w_l < 0`.  By (V3), `g` fixes no point of `X_w`,
and neither does `E_B`.  Hence `W(E_B) ⊆ Q^d_(≥0) \ {0}`.

## Step 2: invariance

Let `w ∈ W(E_B)`, with `E_B` fixing `p ∈ X_w`, and let `σ ∈ H_B`.  Choose `t ∈ B` over `σ`.  In
`G = EL_3(R) x| SL_d(Z)` it has the form `t = u σ` with `u ∈ EL_3(R)`, and `t g t^-1 = u σ̂(g) u^-1` for
`g ∈ EL_3(R)`.  Since `E_B = B ∩ EL_3(R)` is normal in `B`, `u σ̂(E_B) u^-1 = E_B`, i.e.
`σ̂(E_B) = u^-1 E_B u`.  The group `u^-1 E_B u` fixes `u^-1 p ∈ X_w`, because `u ∈ SL_3(R) ≤ SL_3(K_w)`.  By
(V4), for `g ∈ E_B`,

```text
σ̂_*( g · σ̂_*^-1(u^-1 p) ) = σ̂(g) · u^-1 p = u^-1 p ,
```

so `E_B` fixes `σ̂_*^-1(u^-1 p) ∈ X_(σ^T w)`.  Thus `σ^T w ∈ W(E_B)`.  As `H_B` is a group, `W(E_B)` is
invariant under `σ ↦ σ^T` of all of `H_B`.

## Step 3: duality (Y1)

For `w ∈ W(E_B)`, `σ ∈ H_B` and a coordinate vector `e_i`, Steps 1 and 2 give `σ^T w ≥ 0`, so
`<w, σ e_i> = <σ^T w, e_i> ≥ 0`.  The vectors `σ e_i` span `K0 = cone(H_B · O)` as a convex cone, so
`w ∈ K0^∨`.  If `v` and `-v` are in `K0`, then `<w, v> = 0`.  This is (Y1).

## Step 4: (Y2)

Assume `C` infranormal, `B` Kazhdan, `H_B` infinite.  `H_B = B / E_B` is a quotient of a Kazhdan group, so it
is Kazhdan, hence character-free in the sense of the salience node.  By (X1) of
[[subring-level-subpairs-cannot-certify-rank-three-cone]], the nonnegative elements of `H_B` generate it.  By
(W2) of [[nonneg-generated-kazhdan-groups-have-nonsalient-cones]], `K0 ⊇ R^M` for a nonempty `H_B`-invariant
coordinate set `M`.  For `l ∈ M`, both `e_l` and `-e_l` lie in `K0`, so `w_l = 0` for all `w ∈ W(E_B)`.

## Step 5: (Y3)

Let `B ⊇ U_k` and `w ∈ W(E_B)` with `w ∈ Q^d_(>0)`.  Suppose `B` were a certificate.  Then `C` is infranormal and
not normal, and `B` is Kazhdan.

- If `H_B` is finite, (X2) of the subring node makes `C` normal in `B`: contradiction.
- If `H_B` is infinite, Step 4 gives `w_l = 0` for some `l`, against `w > 0`.

So `B` is not a certificate.  The special cases follow.  `E_w ≤ SL_3(O_w)`, the stabiliser of the base vertex
`[O_w^3]`.  A conjugate `g P g^-1` of a parahoric `P` fixes `g · p_P`.  A subgroup with a bounded orbit fixes the
circumcentre of that orbit in the complete CAT(0) space `X_w` (Bridson-Haefliger II.2.8).

## Step 6: the calibrations

- `B = G`.  For `w ≠ 0` pick `m ∈ Z^d` with `<w, m> < 0`.  The element `e_12(x^m) e_21(x^m)` has
  `v_w(tr) = 2 <w, m> < 0`, so `W(EL_3(R)) = ∅ = K0^∨ \ 0`.
- `B = Gamma x| S_d`.  `Gamma = SL_3(R_+) ≤ SL_3(O_w)` for every `w ≥ 0`, since `v_w ≥ 0` on `R_+`.  So
  `W(Gamma) = Q^d_(≥0) \ 0 = K0^∨ \ 0`, with `K0 = O`.  `H_B = S_d` is finite and `C = Gamma` is normal.
- `B = E_w x| Stab(w)`, `Stab(w) = { σ : σ^T w = w }`.  Then `<w, σ e_i> = w_i > 0`, so `K0` is salient.  Step 5
  says that this `B` is never a certificate.  Directly: if `B` is Kazhdan and `C` infranormal, (X1) and (W2)
  make `Stab(w) ∩ H_B` finite.

## Step 7: why this is not the line-section theorem

(L1) of [[level-subpair-line-sections-are-bounded-or-cofinite]] uses Howe-Moore in the locally compact group
`SL_3(F_q((t)))`, which is available only because `F_q[t^(±1)]` has finite residue field at `t = 0`.  The
buildings `X_w` for `d ≥ 2` have infinite residue fields, and no Howe-Moore argument is available there.
Steps 1-5 use only the fixed-point criterion (V3) and the transport (V4), so they work for every weight at once.
In exchange they give no finite-index conclusion, only a fixed-point exclusion.
