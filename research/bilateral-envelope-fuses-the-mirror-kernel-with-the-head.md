---
rg: 2
id: bilateral-envelope-fuses-the-mirror-kernel-with-the-head
kind: claim
title: The bilateral LEF envelope fuses the mirror kernel with the head, so no tracial approximation of H_bi (or of P plus one finitary swap) descends to a head-seeing approximation of EL_n(J)
distinct_from:
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that writes EL_n(J) = P/L_- with P inside the LEF group H_bi and says the difficulty sits in the quotient step; this proves that the LEF envelope H_bi cannot carry out that quotient step at the level of any character, because inside H_bi the mirror head (1,w') is conjugate to the head (w,1).
  sofic-quotients-by-finite-normal-subgroups-are-sofic: that passes soficity to quotients by a finite kernel through orbit sets; this is an obstruction for the infinite locally finite kernel L_-, and it is a conjugacy obstruction in the envelope, not a failure of normalization as in (MQ5).
  untwisted-bilateral-symbol-enrichment-is-lef: that proves H_bi is LEF; this computes that every character of H_bi which is 1 at a single nontrivial finitary element is 1 on all of GL_fin(W), so the LEF structure of H_bi says nothing about the Toeplitz group beyond its symbol.
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that shows every CE character of EL_n(J) is trivial on L or has trivial scalar kernel; this shows the characters of EL_n(J) that come from H_bi through the mirror fibre product are exactly those trivial on L.
---

**ESTABLISHED** (route `bilateral-envelope-fuses-the-mirror-kernel-proof`).

**Notation.** As in `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`:
- `n >= 3`. `E_+ = EL_n(J)` acts on `V_+^n` and `E_- = EL_n(J)` on the mirror half `V_-^n`.
- `P = E_+ x_(SL_n(A)) E_-` sits inside `H_bi = GL_fin(W) x| EL_n(A)`.
- `pr : P -> E_+` has kernel `1 x L_-`. So `EL_n(J) = P / L_-`.
- `w = x_13(Q)` is the head, and `w'` is the same element of `E_-`.
- `c in GL_fin(W)` is the finitary involution that swaps the basis vectors `e_(0,i)` and `e_(-1,i)` for `i = 1..n` and
  fixes the rest.

A **character** of a group is a normalized, positive definite, conjugation-invariant function. Every asymptotically
multiplicative sequence of maps into unitary groups (sofic, hyperlinear, LEF composed with a representation, periodic,
window) has ultralimit traces that are characters (route, Step 1).

**Statement.**

**(F1) Fusion.** `c (1,w') c^(-1) = (w,1)`. So the mirror head, an element of the kernel `L_-`, is conjugate in `H_bi`
to the head. The head is not in `L_-`, and it maps to `w != 1` in `EL_n(J)`.

**(F2) Characters of H_bi.** Let `tau` be a character of `H_bi` with `tau(g) = 1` for a single `g != 1` in
`GL_fin(W)`. Then `tau = 1` on all of `GL_fin(W)`, and `tau` factors through `H_bi -> EL_n(A)`.

**(F3) Descended characters.** Let `chi` be a character of `EL_n(J)`, and suppose that `chi o pr` extends to a character
of the group `<P, c>`. Then `chi` is trivial on the finitary kernel `L`, so it factors through the symbol
`EL_n(J) -> SL_n(A)`. In particular `chi(w) = 1`. This applies in particular when `chi o pr` is the restriction of a
character of `H_bi`. Conversely, every character of `SL_n(A)` arises this way.

**(F4) Approximations.** Let `rho_k : <P,c> -> U(d_k)` be asymptotically multiplicative, and suppose
`tr rho_k(1,w') -> 1`. This holds for `rho_k` defined on all of `H_bi`, such as restrictions of LEF local embeddings
of `H_bi` composed with arbitrary unitary or permutation representations of the finite groups. Then
`tr rho_k(g) -> 1` for every `g` in `L_+ x L_-`. So no approximation of `EL_n(J)` that sees the head is the descent of
such a family. This holds for sofic and for hyperlinear approximations alike, and for every `n >= 3`, including the
`n = 20` of `agent-leavitt-not-bcs-negative-root-corner`.

**(F5) Linear models: the invariant is the rank.** Let `sigma : P -> GL_m(F_2)` be a map that is multiplicative on a
finite set containing `1`, `(w,1)` and `(1,w')`, and suppose
`rank(sigma(w,1) - 1) = rank(sigma(1,w') - 1)`. Then for every homomorphism `pi` from `GL_m(F_2)` to a unitary or
symmetric group, `tr pi sigma(w,1) = tr pi sigma(1,w')`. The reason is that involutions of `GL_m(F_2)` are conjugate
exactly when they have the same `rank(g - 1)`. Every periodic or window compression of `H_bi` gives both heads rank
`1`, so it dies here with any `pi` at all.

**Class killed.** Every approach that builds a head-seeing approximation of `EL_n(J)` by descending approximations of
the LEF envelope through `EL_n(J) = P/L_-` dies. This covers:
- LEF models of `H_bi`;
- their permutation or unitary representations;
- sofic or hyperlinear approximations of `H_bi`;
- characters of `H_bi`;
- finite-window and periodic linear models with any representation.
- **Invariant.** The conjugacy class of the finitary transvection in `GL_fin(W)`. As a character-level statement, the
  fixed-point proportion is a class function.
- **Step where every member dies.** The requirement `tr -> 1` on `L_-`, applied to the mirror head. By (F1) it
  transfers to the head, and by simplicity of `L_+` it spreads to all of `L_+`.

**What survives.** A sofic (hyperlinear) approximation of `EL_n(J)` pulled back to `P` has trace `1_(L_-)`. On
`L_+ x L_- <= GL_fin(W)` this trace is regular on the first factor and trivial on the second. Survivors must therefore
approximate `P` in a way that:
- **distinguishes the orientation**, since the trace cannot extend to `<P,c>`;
- in linear models, **breaks the rank symmetry**: `rank sigma(1,w') != rank sigma(w,1)`, with
  `sigma(1,w') != 1` unless the model already factors through `EL_n(J)`.

The mirror fibre product therefore gives no leverage beyond what `EL_n(J)` itself gives. The LEF envelope is not a
source of approximations of the Toeplitz group. It sees only the symbol.
