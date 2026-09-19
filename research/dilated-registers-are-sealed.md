---
rg: 2
id: dilated-registers-are-sealed
kind: claim
title: A homeomorphism that dilates a register copy of Q never reads another coordinate into the register, so cross-coordinate odometer germs cannot build Q x| <d>, and every host that is almost-automorphic on the register coordinate sees only bounded denominators
distinct_from:
  one-coordinate-registers-admit-no-dilation: that assumes the host is coordinatewise cellular (each output coordinate is a cylinder map of one input coordinate); this proves, for an ARBITRARY homeomorphism, that the register output depends only on the register input, and then needs cellularity only on the register coordinate, so it covers hosts with adding-machine, affine or other germs that mix the remaining coordinates.
  rational-rotations-and-doubling-have-no-common-tree-coding: that assumes the dilation is a skew product over the register with a covering base map; this proves that shape is forced.
  natural-q-rtimes-2-in-2v-h-iff-odd-odometer-roots: that is the natural 2-adic copy of Q x| <2>, where Q is not a register; this is register copies.
---

**ESTABLISHED** by `dilated-registers-are-sealed-proof` (lane bh-free-16, 2026-09-18; elementary; not reviewed;
no priority claimed).

## Setting

The setting is that of `one-coordinate-registers-admit-no-dilation`, except that no host is assumed.
- **The space.** `K = C_r × W`, where `C_r` is a Cantor space with a rooted tree coding (its vertex sets are the
  *cylinders*) and `W` is any compact metrizable zero-dimensional space (the other coordinates).
- **The register.** `π_0 : C_r → R/Z` is continuous and onto, injective off a countable set, and every cylinder
  has a shadow `π_0(Z)` that is a finite union of nondegenerate closed arcs. Put `π = π_0 ∘ pr_r`.
- **The register copy.** `a ↦ q_a` is an injective homomorphism from a non-cyclic `A <= Q` to `Homeo(K)`, with
  `π ∘ q_a = π + a` and the locality condition (R) of that node.
- **The dilation.** `t ∈ Homeo(K)`, `d >= 2` an integer, and `t q_a t^-1 = q_(da)` for all `a ∈ A`.

## Theorem

1. **Sealing (no host hypothesis).** There is a finite partition of `K` into clopen boxes `B_i = Z_i × W_i` with the
   following property. On each `B_i`, the register coordinate of `t(z, w)` is `φ_i(z)` for a continuous map `φ_i`
   that does not depend on `w`, and `π_0 ∘ φ_i = d·π_0 + f_i` on `Z_i`, with `f_i ∈ R/Z` a constant.
   - The same holds for every `q_a`, with `d = 1` and twist `a`.
   - So information flows out of a dilated register, as in overflow and carries into other coordinates, but never
     into it. No germ can add another coordinate's value into the register while `t` normalizes the copy: not an
     odometer, an adding machine `(x, y) ↦ (x + y, y)`, an affine or linear germ, or anything else.
2. **Arithmetic (register-cellular hosts).** Suppose each `φ_i`, and the register maps of each `q_a` from item 1,
   is a tree almost-automorphism on `Z_i`: a finite partition into cylinders, each mapped onto a cylinder by an
   isomorphism of rooted subtrees. Then `A ⊆ (1/M) Z[1/d]` for some `M`. In particular `A ≠ Q`.

**Hosts covered by item 2.** Item 2 applies whenever every host element acts on `C_r` by a tree
almost-automorphism wherever its register output reads only the register input. This includes:
- `nV`, every `SV_G`, `2V_τ`, and `2V_H` for every self-similar `H <= Aut(T_2)`;
- Zappa–Szép (Li) hosts over product `k`-graphs;
- Katsura–Exel–Pardo-type hosts;
- hosts whose germs are `2`-adic affine maps of `Z_2^k`, including cross-coordinate adders and `GL_k(Z)`-type
  mixing (by item 1, a register output that reads only `k_r` is a one-dimensional affine map `z ↦ 2^m u z + b`,
  which is almost-automorphic).

## What this closes and what is left

- **The design "an odometer adding another coordinate's value into the register" is dead in every host.** This was
  escape (ii) of `one-coordinate-registers-admit-no-dilation`, and the target of the Röver–Nekrashevych direction in
  `board/major-gln.md` R3. Item 1 needs no finiteness, cellularity or finite-state hypothesis.
- **Two escapes are left for register copies.**
  - **(a) Register-coordinate germs that are not tree almost-automorphisms.** For example, asynchronous
    transducers of the rational group or of `Aut(V)`. There, `f_i` is still locally constant, but cylinders need
    not map to cylinders.
  - **(b) Registers spread over a block `R` of two or more coordinates.** Item 1 holds verbatim for the block, which
    is still sealed. The arithmetic can fail when the block maps mix coordinates inside the block: a box with one
    shallow side is not one of finitely many.
- **Copies of `Q` that are not registers** are a separate question. The natural `2`-adic copy is decided in
  `natural-q-rtimes-2-in-2v-h-iff-odd-odometer-roots`.

## Lesson for general BH

**Equivariance seals a dilated register.**
- The twist `f = π∘t − dπ` is invariant under the copy, so it cannot depend on the register.
- It cannot vary continuously with the other coordinates either. At a split point of the register coding, a
  one-sided neighbourhood forbids small twists of one sign, and the partner point forbids the other sign.
- So a dilation of a divisible register is a lift of the covering map with finitely many rotations. The host's
  only freedom is in how it codes cylinders on that one coordinate.

Two consequences for GL_n(Q) hosts:
- **Cross-coordinate "mixing" germs cannot rescue a register.** Arithmetic can flow out of a divisible
  coordinate (carries, overflow) but never into it while it is dilated.
- **Where the infinitely many primes must sit.** Either in a coding of the register that is not almost-automorphic
  (non-synchronous transducers), or in a copy of `Q` that is not a circle register at all. The natural `2`-adic
  copy puts them in the odd roots of the odometer, inside the coefficient group.
