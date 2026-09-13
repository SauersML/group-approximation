---
rg: 2
id: rf-kazhdan-group-not-flexibly-hs-stable
kind: claim
title: The affine symplectic group Z^2g x| Sp_2g(Z), g >= 2, is a residually finite Kazhdan group that is not flexibly HS-stable
distinct_from:
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is Becker--Lubotzky's exclusion of strict same-dimension stability for every infinite hyperlinear Kazhdan group; this excludes flexible stability, with padding allowed, for one explicit residually finite Kazhdan group.
  isw-corollary-b-uses-only-the-standard-area-cocycle: that audits the Ioana--Spaas--Wiersma engine on the non-Kazhdan group Z^2 x| SL_2(Z); this runs the invariant symplectic form on a Kazhdan group and closes the argument with property (T) of the integral Heisenberg cover.
  isw-theorem-a-has-no-data-on-sp4-lattice: that proves Sp_4(Z) itself carries no cocycle data for ISW Theorem A; this shows the affine group Z^2g x| Sp_2g(Z) carries such data while having property (T).
  exact-levi-affine-relative-stability-fails: that refutes a relative stability statement with an exact Levi on Z^2 x| SL_2(Z); this refutes full flexible HS stability of a Kazhdan group.
  flexibly-but-not-strictly-hs-stable-group-exists: that is the open search for a group separating flexible from strict stability; this group is not flexibly stable, so it is not a candidate.
---

**ESTABLISHED (unreviewed).** Let `g >= 2` and `ω(x,y) = Σ_i (x_i y_(g+i) - x_(g+i) y_i)`
on `Z^(2g)`. Put

```text
Γ_g = Z^(2g) ⋊ Sp_(2g)(Z),        (v,A)(w,B) = (v + Aw, AB).
```

1. `Γ_g` is residually finite and has property (T).
2. `Γ_g` is not flexibly HS-stable in the sense of Dogon, arXiv:2211.10492, Definition 1.2.
   An explicit non-roundable asymptotic representation, for `k >= 3`, is `α_k = ρ~_k∘s`:
   - `Γ~_g` is the integral Heisenberg cover, with `(v,s,A)(w,t,B) = (v+Aw, s+t+ω(v,Aw), AB)`
     and central element `z = (0,1,1)`;
   - `ρ~_k` is the left regular representation of the finite group `Γ~_g mod k`, cut down to
     the subspace where `z` acts by `e^(2πi/k)`;
   - `s(v,A) = (v,0,A)`.

   Then `α_k(g)α_k(h) = e^(2πi ω(v,Aw)/k) α_k(gh)` for `g = (v,A)`, `h = (w,B)`. The defect is a
   scalar of size `O(1/k)` in operator norm, and `tr α_k -> δ_e`.
3. **Quantitative form.** There are `ε > 0` and a finite `F ⊂ Γ_g` such that, for all large
   `k`, no genuine representation `π : Γ_g -> U(D)` with `d_k <= D <= (1+ε)d_k` satisfies
   `max_(g∈F) ||α_k(g) - P π(g) P*||_(2,d_k) < ε`. Here `P` keeps the first `d_k` coordinates.

Derivation: `rf-kazhdan-group-not-flexibly-hs-stable-proof`.

**Reading.**
- **(T) is not enough.** Property (T), residual finiteness and a regular limit trace together
  do not force flexible rounding.
  - The witness is a hyperlinear approximation with limit trace `δ_e`, which is the regime of
    `hs-stable-vertex-rounding-for-every-model`.
  - So a stability proof for a Kazhdan group must use more than (T) and residual finiteness.
    Here the obstruction is a non-torsion class in `H^2(Γ_g, R)`, realized by
    finite-dimensional projective representations whose cocycles tend to 1.
- **Weak ucp.** `Γ_g` is residually finite, hence hyperlinear. By
  `kazhdan-weak-ucp-stability-is-flexible-stability`, it is therefore not weakly ucp-stable
  either.
- **Scope.** `Γ_g` is a lattice in `R^(2g) ⋊ Sp_(2g)(R)`, not in a semisimple group.
  Flexible stability of lattices in higher-rank simple groups, such as `SL_n(Z)` and
  `Sp_(2g)(Z)`, is untouched.

**Credit and novelty (bounded check, 2026-09-13).**
- **The engine is Ioana--Spaas--Wiersma's**, arXiv:2006.01874v2: Theorem A, plus the remark
  after their definition of HS-stability, "any group Γ satisfying the hypothesis of Theorem A
  (e.g., Γ=Z^2⋊SL_2(Z)) is not flexibly HS-stable". `Γ_g` satisfies Theorem A with `Λ` a
  symplectic plane and `c_k = exp(2πi ω(v,Aw)/k)` (proof §6).
- **Neither source states the Kazhdan instance.**
  - ISW's LaTeX source mentions symplectic groups only as examples of LP failure: lattices in
    `Sp_2n(R)`, and `Z[1/p]^4 ⋊ Sp_4(Z[1/p])` as an infinitely presented Kazhdan group.
  - Dogon arXiv:2211.10492v3 p. 3 lists `SL_2(Z) ⋉ Z^2` and `F_m × F_k` as the residually
    finite non-flexibly-stable groups, and names no Kazhdan example.
- **What is claimed.** The proof here does not use ISW's lifting machinery. It is not claimed
  as a new technique, only as the explicit Kazhdan instance, which the graph did not record.
