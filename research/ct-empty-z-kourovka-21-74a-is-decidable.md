---
rg: 2
id: ct-empty-z-kourovka-21-74a-is-decidable
kind: claim
title: "Kourovka 21.74(a) is decidable for every g in CT_∅(Z) ≅ V, with residue classes of arbitrary moduli: attractor-repeller maps ψ_n = C^(−n)R^n are K-free fibre symmetries whose distinct fixed points bound every odd modulus over the north-south part by a computable m*, and a finite box search finishes"
distinct_from:
  ct-empty-z-cone-partition-question-is-decidable: that decides the 2-power sub-case; this decides the full question for the same elements, with odd moduli.
  ct-empty-z-odd-moduli-split-only-at-defect-primes: that gives the mod-3 obstruction and a prime bound derived through K = |𝒫|!; this gives a K-free bound on primes and exponents together, and so full decidability.
  ct-z-residue-partition-certificates-live-on-s-adic-coordinates: that reduces certificates to S-adic coordinates plus trivial blocks; this closes the case S = {2}.
---

**ESTABLISHED** (lane proof, not reviewed). No priority claimed.
- **The problem, verbatim.** Kourovka Notebook, 21st issue, 21.74 (S. Kohl): "Is it
  algorithmically decidable whether a given element g ∈ CT(Z) (a) permutes a nontrivial partition
  of Z into residue classes? …"
- **What this settles.** (a) for every `g ∈ CT_∅(Z)`, the group of class transpositions with
  2-power moduli (≅ V; McDermott, recorded by Kohl, J. Group Theory 20 (2017), Remark 1.4). The
  classes may have any moduli.
- **What stays open.** (a) for elements involving odd primes.
- **Inputs.** The cone node (decomposition `Z_2 = U ⊔ V`, flow components `R_j`, Lemma A,
  computability, all refereed PASS); Theorem 1 (skew product) of the S-adic node; the obstruction
  of the odd-moduli node.

## Setting

- **The skew product.** `ĝ(x, y) = (g(x), β_x(y))` on `Ẑ = Z_2 × Ẑ_odd`. The block `β_x` is the
  affine formula of `g`'s piece at `x` (slope `2^c`, translation in `Z[1/2]`), acting on
  `Ẑ_odd`. Write `β^(N)_x` for the block of `ĝ^N` at `x`.
- **Boxes.** A class `r(2^e m)`, `m` odd, is the box `(cone) × (r + mẐ_odd)`, whose
  `ℓ`-component is the ball `r + ℓ^(v_ℓ(m)) Z_ℓ`.
- **The components.** `M` is a common period. Each `R_j` contains an attractor `a`, where
  `g^M = C`, `C(y) = a + 2^t(y − a)` (`t ≥ 1`), and a repeller `r`, where `g^M = R`,
  `R(y) = r + 2^(−s)(y − r)` (`s ≥ 1`). Here `a ≠ r` are rationals with odd denominators.

## Lemma B (fibre partitions and K-free symmetries)

Let `g` permute a box partition `𝒫` of `Ẑ`, and let `𝒫_j` be the set of parts `C` whose 2-adic
ball `C_2` meets `R_j`. Then:
1. every `C ∈ 𝒫_j` has `C_2 ⊇ R_j`;
2. `Π_j = {C_odd : C ∈ 𝒫_j}` is a partition of `Ẑ_odd` into boxes, namely the fibre partition over
   every `x ∈ R_j`;
3. for `x, x′ ∈ R_j` and `N ≥ 0`, the map `(β^(N)_(x′))^(−1) β^(N)_x` maps every box of `Π_j` onto
   itself.

*Proof.*
- **1.** With `K = |𝒫|!`, `ĝ^K(C) = C` projects to `g^K(C_2) = C_2`. So `C_2 ∩ R_j` is a nonempty
  `g^(MK)`-invariant clopen subset of `R_j`, hence all of `R_j` by Lemma A.
- **2.** By 1, the parts meeting the fibre over `x ∈ R_j` are exactly those in `𝒫_j`.
- **3.** `g` permutes `𝒫`, so `ĝ^N` sends each `C ∈ 𝒫_j` onto a part `C^N`, and
  `β^(N)_x(C_odd) ⊆ (C^N)_odd`.
  - Both `{β^(N)_x(C_odd)}` and the fibre partition over `g^N x` partition `Ẑ_odd`, and
    `C ↦ C^N` is injective. So `β^(N)_x(C_odd) = (C^N)_odd`, for every `x ∈ R_j`.
  - Compare `x` with `x′`. ∎

## Lemma C (the depth bound)

Fix `a`, `r` in `R_j`, and for `n ≥ 1` put `ψ_n = C^(−n) ∘ R^n`.
- **Symmetries.** By Lemma B.3 with `x = r`, `x′ = a` and `N = Mn` (the formulas of `g^(Mn)` at
  `r` and `a` are `R^n` and `C^n`), every `ψ_n` maps every box of `Π_j` onto itself.
- **Fixed points.** `ψ_n` has slope `λ_n = 2^(−(t+s)n) ≠ 1` and a unique fixed point `p_n ∈ Q`.
- **Distinctness.** Two of `p_1, p_2, p_3` are distinct.
  - `R^n(p) = C^n(p)` reads `(p − r)Y_n − (p − a)X_n = a − r`, with `X_n = 2^(tn)` and
    `Y_n = 2^(−sn)`.
  - A common `p` for `n = 1, 2, 3` would give a nontrivial kernel vector of the matrix with rows
    `(Y_n, X_n, 1)`.
  - That matrix is a generalized Vandermonde matrix in the distinct nonzero numbers
    `2^(−s), 2^t, 1`, so it is invertible, forcing `p − r = p − a = a − r = 0`. This is
    impossible.
- **The bound.** Choose `n ≠ n′` with `p_n ≠ p_(n′)`. If a box of `Π_j` has `ℓ`-component
  `c + ℓ^e Z_ℓ` (`e ≥ 1`), then `ψ(c) − c = (λ − 1)(c − p)` for both maps. Hence
  `v_ℓ(c − p_n), v_ℓ(c − p_(n′)) ≥ e − μ` with `μ = max(v_ℓ(λ_n − 1), v_ℓ(λ_(n′) − 1))`, and
  therefore

      e ≤ E_j(ℓ) := v_ℓ(p_n − p_(n′)) + μ.

- **The modulus `m_j`.** `E_j(ℓ) ≥ 1` only for the finitely many `ℓ` dividing the numerators of
  `p_n − p_(n′)`, `2^((t+s)n) − 1` and `2^((t+s)n′) − 1`. So every odd modulus in `Π_j` divides
  the computable odd number `m_j = ∏_ℓ ℓ^(max(0, E_j(ℓ)))`.

## Theorem (decidability)

Let `m* = lcm_j m_j`. A *candidate* is a box `[w] × (class mod m′)` with `w` a prefix of some
`u_j` and `m′ | m*`. There are finitely many candidates.

`g` permutes a nontrivial residue-class partition iff there is a family `𝒞` of disjoint candidates
such that:
1. for each `j`, the members with `C_2 ⊇ R_j` cover `R_j × Ẑ_odd`, and every member has
   `C_2 ⊇` some `R_j`;
2. `ĝ` maps each member onto a member;
3. `Q = Ẑ ∖ ⋃𝒞` is nonempty, or `|𝒞| ≥ 2`.

Images of boxes under `ĝ` are explicit finite unions of boxes, so this is a finite search, and
21.74(a) is decidable on `CT_∅(Z)`. If `V = ∅`, then `g` has finite order and the answer is YES.

*Proof.*
- **⇒.** Take `𝒞` to be the parts meeting `V × Ẑ_odd`.
  - By Lemma B.1 each has `C_2 ⊇ R_j`, so `C_2 = [w]` for a prefix `w` of `u_j`.
  - By Lemma C its odd modulus divides `m_j`.
  - Conditions 1–3 are inherited from `𝒫`.
- **⇐.** `Q` is `ĝ`-invariant and lies in `U × Ẑ_odd`.
  - There `ĝ^N = id` for `N = ord(g|_U)`, since the formula of `g^N` on `U` is the identity and
    blocks share formulas.
  - Refine `Q` into boxes on which every `ĝ^i` (`i < N`) is canonical. The common refinement of
    their images consists of intersections of boxes, which are boxes (CRT), and it is permuted.
  - Adding `𝒞` gives a permuted partition with at least two parts. ∎

## Checks

- **The mod-3 element** of the odd-moduli node: `n ↦ 4n`, `n + 9`, `(n − 3)/4`.
  - Here `a = 0`, `C(y) = 4y` (`t = 2`), `r = −1` and `R(y) = −1 + (y + 1)/4` (`s = 2`).
  - `ψ_n(y) = 4^(−2n)(y + 1) − 4^(−n)`, with `p_n = −1/(4^n + 1)`, so `p_1 − p_2 = −12/85`.
  - `E(3) = 1 + 1 = 2`, while `E(5) = E(17) = 0`. So `m* = 9`, and the search finds
    `{0(3), 1(3), 2(3)}`. The 2-power candidates alone fail, as proved there.
- **2-power sub-case.** It is the case `m′ = 1` of the search, which recovers the cone node.

## Lesson for general BH

**A permuted partition must commute, over each flow component, with the attractor–repeller
"holonomy" `C^(−n)R^n`.**
- These maps are hyperbolic, and their fixed points move with `n`. So they pin every hidden odd
  coordinate to a bounded depth, with no dependence on the size of the partition.
- In one base, coordinate structure is therefore decidable in full.
- In two bases the same holonomy maps exist, but the components themselves (Collatz, machines) are
  no longer finite or computable. That, not the coordinates, is where 21.74(a) can become hard.
