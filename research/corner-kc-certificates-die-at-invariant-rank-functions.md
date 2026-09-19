---
rg: 2
id: corner-kc-certificates-die-at-invariant-rank-functions
kind: claim
title: In linear mapping tori over a ring with a rank function, every corner certificate for the Kazhdan-centralizer criterion lives on a rank-null corner, and over simple subshift rings none exists
distinct_from:
  kazhdan-centralizer-commuting-conjugates-kill-derived-subgroup: that is the criterion (KC1) with its sofic vacuity (KC3), which needs a Kazhdan compressor; this is an algebraic vacuity for corner data in GL_n(R) ⋊ Z with no Kazhdan hypothesis on u, where (KC0) alone forces a rank inequality.
  invariant-size-collapse: that is the formal principle that an invariant size forbids strict compression; here the compression itself is allowed, and the rank is used at the commuting-conjugates step (KC0), which is where it bounds the lamp corner by the compression gap.
  sofic-groups-kill-rigid-compression-defects: that kills compression defects in sofic groups when the compressor group is Kazhdan; this needs no soficity and no Kazhdan compressor, only a Sylvester rank function on the coefficient ring.
  hilbert-hotel-model-full-mf-radical: that is the successful corner mechanism over the binary Leavitt algebra, which has no rank function; this proves that such a ring is compulsory for a corner certificate on a rank-positive corner.
  torsion-free-kazhdan-lamp-wreath-radical-has-kazhdan-subgroups: that is the lamp-wreath certificate, whose lamps live on disjoint sites of a permutational wreath; this is the matrix-over-a-ring form, where the lamp is an idempotent corner and must fit in the rank of the compression gap.
  torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical: that is the OPEN target; this kills the corner-certificate route to its (LK3) for every elementary or linear kernel over a simple rank-function ring, including the residual (L2) class.
artifacts:
  - research/kazhdan-centralizer-commuting-conjugates-kill-derived-subgroup.md
  - research/minimal-subshift-algebra-is-simple-lef-ring.md
---

**ESTABLISHED** by `corner-kc-certificates-die-at-invariant-rank-functions-proof`.

## Setting

- `R` is a unital ring, `σ ∈ Aut(R)`, `n ≥ 3`.
- The ambient group is `GL_n(R) ⋊_σ Z = GL_n(R) ⋊ <t>`, with `t A t^-1 = σ(A)` entrywise.
- For an idempotent `f`, write `U_f = GL_n(R) ∩ (I + M_n(fRf))`. It is a subgroup.
- `e_ij(r) = I + r E_ij` is the root element.

A **corner certificate** is data `(u, e, f, ℓ)` with:

- `e, f` idempotents of `R` with `ef = fe = 0`;
- `u = h t^m`, with `m ∈ Z`, `h = h_0 π`, `h_0 ∈ R^x` and `π` a permutation matrix;
  so `Ad(u)` is `M_n(τ)` followed by a permutation of coordinates, where `τ = Ad(h_0) ∘ σ^m`;
- a root `e_ab(f)` (`a ≠ b`) with `u e_ab(f) u^-1 ∈ U_f` (compression of the corner);
- `ℓ ∈ U_f`;
- roots `e_ik(e), e_kj(e)` (`i, k, j` distinct) such that
  `u e_ik(e) u^-1` commutes with `ℓ u e_kj(e) u^-1 ℓ^-1`.

**Why this is the corner form of (KC).** Take `L ≤ U_f` and `C ≤ U_e` with `e_ab(f) ∈ L`,
`e_ik(e), e_kj(e) ∈ C`, `uLu^-1 ≤ L` and (KC0) for `ℓ ∈ L`. Then `C ≤ C_G(L)` automatically, since
`M_n(eRe) M_n(fRf) = 0`. The natural choices are `L = EL_n(fRf)` and `C = EL_n(eRe)`. These are Kazhdan
for finitely generated corners, with `D = [C,C] = EL_n(eRe)` (perfect for `n ≥ 3`). This is the matrix form of the
lamp-wreath mechanism: `L` is the compressed Kazhdan block, and `C` is a lamp placed where the
compression has freed room. Every such `(L, C, u, ℓ)` contains a corner certificate. The statements
below use only the certificate, not property (T).

## Statement

A Sylvester matrix rank function on `R` is written `rk`. Let `(u, e, f, ℓ)` be a corner certificate.

- **(CR1) Gap inequality.** `f' := τ(f)` satisfies `f' ∈ fRf`, so `f - f'` is an idempotent. Moreover
  `τ(e) = τ(e)(f - f')(1 + w)` for some `w ∈ R`. Hence, for every rank function,

  ```text
  rk(τ e)  <=  rk(f) - rk(τ f).
  ```

  So the conjugated lamp must fit inside the compression gap `f - τ(f)`.
- **(CR2) One invariant rank function kills every certificate.** Suppose `R` has a Sylvester matrix
  rank function. Then it has a `σ`-invariant one `ρ`. Such a `ρ` is invariant under every `τ` as
  above, for all `m` and `h_0` at once. The set `I_ρ = { r : ρ(r) = 0 }` is a proper `σ`-invariant
  two-sided ideal. For every corner certificate, `e ∈ I_ρ`. Consequently:
  - for every `G ≤ GL_n(R) ⋊_σ Z` and every (KC) datum of corner form in `G`, `D ≤ C ≤ N_ρ`;
  - the normal closure of all these `D` lies in `G ∩ N_ρ`, where
    `N_ρ = ker(GL_n(R) → GL_n(R/I_ρ))` is normal in `GL_n(R) ⋊_σ Z`;
  - `N_ρ` contains no `e_12(r)` with `ρ(r) > 0`, and in particular it does not contain `EL_n(R)`.

  The same `ρ` descends to every `σ`-invariant quotient `R/J` with `J ⊆ I_ρ`. So repeating the
  argument over `R/J` never leaves `N_ρ`.
- **(CR3) Rigidity over simple rings.** Suppose there are ring homomorphisms `π_s : R → S_s` with the
  following properties:
  - they are jointly injective;
  - they intertwine `σ` with automorphisms `σ_s`;
  - each `S_s` is simple and has a Sylvester matrix rank function.

  Then every corner certificate has `e = 0`. So there is **no** nontrivial corner certificate in any
  subgroup of `GL_n(R) ⋊_σ Z`, for **any** such `σ`.
- **(CR4) The subshift rings.** Let `X` be an infinite minimal subshift. Then (CR3) applies, for
  **every** ring automorphism `σ`, to:
  - `R = LC(X,F_q) ⋊_T Z`, with `S = R`. This includes `σ` induced by an element `ψ ∈ Aut(X,T)` of
    infinite order modulo `<T>`.
  - `R_Z = LC(X,Z) ⋊_T Z`, using the reductions `R_Z → R_Z/pR_Z = LC(X,F_p) ⋊_T Z` over all primes `p`.
    Every ring automorphism preserves `pR_Z`.

## Consequences for the flagship

1. **The residual (L2) class is closed to corner certificates.** In
   `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`, Attempt 1 leaves one live form
   for elementary kernels: `EL_n(σ)` with `σ` of infinite order modulo inner automorphisms, for example
   `σ` induced by `ψ ∈ Aut(X,T)` of infinite order modulo `<T>`. By (CR4), no subgroup of
   `GL_n(R) ⋊_σ Z` over these rings contains a nontrivial corner certificate. This covers:
   - `EL_n(R)` itself;
   - every torsion-free Kazhdan subgroup of `GL_n(LC(X,Z) ⋊ Z)`, such as congruence-type subgroups.

   So (LK3) for these kernels cannot be proved by the corner form of
   `kazhdan-centralizer-commuting-conjugates-kill-derived-subgroup`, whatever the automorphism.
2. **The named obstruction.** The invariant is a `σ`-invariant Sylvester matrix rank function. Every
   member of the class dies at (KC0), which forces `ρ(e) ≤ ρ(f) - ρ(σ^m f) = 0`.
3. **What a corner certificate needs.** A nontrivial corner certificate needs a corner `e` that is
   null for every `σ`-invariant rank function. Over a simple ring, this means a ring with **no**
   Sylvester rank function at all: the Hilbert-hotel side of `hilbert-hotel-model-full-mf-radical`,
   with a halvable or paradoxical unit.

   Corner mechanisms do work on that side. But soficity of `EL_n(R)` over such rings is the hard open
   question: the Leavitt algebra has no unital rank model (`leavitt-algebra-has-no-unital-rank-model`),
   and the converse rung `linear-sofic-el-groups-force-rank-model` is OPEN.

   So for elementary and linear kernels, a corner-certificate proof of (LK3) must use a coefficient ring
   in which the lamp corner is null for every invariant rank function. Every simple ring with a rank
   function is excluded, and this includes every simple subshift ring used so far for (L1) and (L2).
4. **Scope, stated honestly.**
   - (CR1)–(CR3) assume that `Ad(u)` is entrywise up to a permutation (the monomial-scalar form above).
     This includes every power of the mapping-torus generator `t`, and every `u` in the base with
     scalar `h`.
   - A certificate whose compressor `u` mixes coordinates in a general way, or whose `C` centralizes `L`
     other than through orthogonal idempotent corners, is **not** covered.
   - The (KC) criterion itself is untouched and remains sound.

Route: `corner-kc-certificates-die-at-invariant-rank-functions-proof`.
