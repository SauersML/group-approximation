---
rg: 2
id: free-action-leavitt-tensor-hosts-have-trivial-k1-k2
kind: claim
title: For a free action of a finitely generated group on a compact zero-dimensional space, the Leavitt tensor of the binary crossed product has trivial K_1 and K_2, torsion included
distinct_from:
  cantor-crossed-product-leavitt-tensors-are-k-trivial: that needs a torsion-free Farrell-Jones acting group and allows any action; this allows torsion in the acting group but needs the action to be free, which the trace detector shows cannot be dropped.
  leavitt-tensor-k1-sees-traces-of-nilpotent-matrices: that gives a necessary trace condition and counterexamples with p-torsion under trivial actions; this asserts vanishing when all torsion acts freely, where that screen is shown here to pass.
  dihedral-cantor-crossed-product-k1-has-exponent-four: that computes K_1 of the crossed product itself for a dihedral action; this concerns its Leavitt tensor, where K_1 is expected to vanish.
---

**OPEN.** Premise (K) of `boone-higman-via-leavitt-units-of-rigid-sft-overgroups`.

## Statement

Let `Λ` be a finitely generated group acting freely on a compact Hausdorff zero-dimensional space
`X`. Let `B = LC(X, F_2) ⋊ Λ` and `L = L_(F_2)(1,2)`. Then `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`.

The route needs this only for the `Λ` and `X` produced by
`decidable-groups-lie-in-fp-free-minimal-crossed-products`. A weaker statement would suffice: the
same conclusion for groups satisfying the Farrell-Jones conjecture.

## Known cases (established)

1. **Torsion-free Farrell-Jones `Λ`, any action.** `cantor-crossed-product-leavitt-tensors-are-k-trivial`.
2. **Finite `Λ`, free action.**
   - A free action of a finite group on a compact zero-dimensional space has a clopen fundamental
     domain `D`, so `X = ⊔_h hD`, and `B ≅ M_|Λ|(LC(D, F_2))` via the matrix units
     `1_(hD) u_(hh'^(-1)) 1_(h'D)`.
   - So `B ⊗ L ≅ M_|Λ|(LC(D, L))`. By Morita invariance its K-theory is that of `LC(D, L)`, which
     vanishes by `cantor-crossed-product-leavitt-tensors-are-k-trivial-proof` (a flat union of
     finite products of `L`, each K-trivial by `ara-cortinas-leavitt-tensor-k-theory-vanishes`).

## Freeness is necessary

Let `Λ = Z/2 = <t>` act trivially on any nonempty `X`. Then `B = LC(X, F_2)[Z/2]` is commutative, so
`φ(f_1 + f_t u_t) = f_t(v)` at a point `v` is a trace. The element `x = u_t - 1` has `x^2 = 0` and
`φ(x) = 1`. So `χ_(φ,1) ≠ 0` in `leavitt-tensor-k1-sees-traces-of-nilpotent-matrices`, and
`K_1(B ⊗ L) ≠ 0`. This is Corollary 3 there, with `LC(X, F_2)` coefficients.

## The trace screen passes for free actions

Let `g ∈ Λ` have order `2^j >= 2`. Corollary 2 of the detector requires `(u_g - 1)^m ∈ [B, B]` for
all `m >= 1`.
- For `h ≠ 1` acting freely, `X` is covered by finitely many clopen `W` with `W ∩ hW = ∅`, which may be
  taken disjoint. For such `W`, `[1_W u_h, 1_W] = 1_W 1_(hW) u_h - 1_W u_h = -1_W u_h`, since
  `u_h 1_W = 1_(hW) u_h`. Summing over the cover, `u_h ∈ [B, B]`.
- `<g>` acts freely, so it has a clopen fundamental domain `D`, and
  `1 = Σ_i u_(g^i) 1_D u_(g^i)^(-1) ≡ 2^j 1_D = 0` modulo `[B, B]`. So `1 ∈ [B, B]`.
- `(u_g - 1)^m` is a combination of the `u_(g^i)`, all of which lie in `[B, B]`.

So the detector finds no obstruction. The screen does not prove vanishing: it only rules out the
known mechanism for `K_1 ≠ 0`.

## Attempts

- **Farrell-Jones with torsion (sketch, not closed).**
  - Assume `Λ` satisfies the K-theoretic Farrell-Jones conjecture with additive coefficients relative
    to `VCyc`. By `crossed-product-rings-inherit-fjc-with-additive-coefficients` the same holds for
    the coefficient ring `LC(X, L)`, and `B ⊗ L ≅ LC(X, L) ⋊ Λ` as in the proof of the
    torsion-free case. It then suffices that `K_*(LC(X, L) ⋊ V) = 0` in degrees `<= 2` for every
    virtually cyclic `V <= Λ`.
  - *Finite `V`*: case 2 above.
  - *`V = F ⋊ Z` with `F` finite*: the ring is a twisted Laurent ring over
    `M_|F|(LC(D, L))`, which is K-trivial and regular coherent. The twisted Nil terms vanish by
    `regular-coherent-laurent-coefficients-kill-twisted-nil-terms`, and the Bass-Heller-Swan term
    is a cofibre of `1 - α` on `K(M_|F|(LC(D, L))) = 0`.
  - *`V` with quotient `D_∞`*: `V = V_1 *_F V_2` with `[V_i : F] = 2`, so the ring is an amalgam
    `R_1 *_(R_0) R_2` of K-trivial rings, each free of rank `2` over `R_0`. This needs Waldhausen's
    Nil vanishing over regular coherent `R_0`, or the Davis-Quinn-Reich / Bartels reduction from
    `VCyc` to `VCyc_I`. Both are recalled and **not verified**.
  - **Where it stops**: those imports, and the Farrell-Jones conjecture for the `Λ` given by (E),
    which need not be a known Farrell-Jones group.
