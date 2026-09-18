---
rg: 2
id: fp-linear-hosts-of-sl-q-have-wild-h3-quotients-proof
kind: route
title: The Lyndon–Hochschild–Serre corner term H_2(N)_Q survives into H_2(Γ) modulo a d_3 image from H_3(Q)
target: fp-linear-hosts-of-sl-q-have-wild-h3-quotients
requires: []
---

## Imported standard facts

The theorem numbers are recalled, not re-read; the statements are standard.
- **(H1)** For a perfect group `P`, the kernel of its universal central extension is
  `H_2(P; Z)`. For `P = E(Λ)` this gives `H_2(E(Λ); Z) = K_2(Λ)` (Milnor, *Introduction to
  Algebraic K-Theory*, §5).
- **(H2)** The Lyndon–Hochschild–Serre spectral sequence
  `E^2_(p,q) = H_p(Γ/N; H_q(N; Z)) => H_(p+q)(Γ; Z)` (Brown, *Cohomology of Groups*, VII.6).
- **(H3)** A finitely presented group has finitely generated `H_2(-; Z)`: it is of type `FP_2`
  (Brown, VIII.5).

## Part 2

Write `Q = Γ/N`.
- `N` is perfect, so `H_1(N) = 0` and `E^2_(p,1) = 0` for every `p`.
- In total degree 2, `E^2_(1,1) = 0` and `E^2_(0,2) = H_0(Q; H_2 N) = H_2(N)_Q`.
- Differentials into `(0,2)`:
  - `d_2` starts at `E^2_(2,1) = 0`;
  - `d_3` starts at `E^3_(3,0) = ker(d_2 : H_3(Q) -> E^2_(1,1) = 0) = H_3(Q)`;
  - `d_r` for `r >= 4` starts at `E_(r, 3-r)`, which is zero.
  Differentials out of `(0,2)` land in negative columns.
- So `E^∞_(0,2) = H_2(N)_Q / d_3(H_3(Q))`. This is the image of `H_2(N) -> H_2(Γ)`, the first
  step of the filtration, hence a subgroup of `H_2(Γ)`.
- If `H_2(Γ)` is finitely generated, so is `E^∞_(0,2)`. If `H_3(Q)` is finitely generated too,
  then `H_2(N)_Q` is an extension of two finitely generated groups, hence finitely generated.
- If the extension splits, the edge map `H_3(Γ) -> H_3(Q)` is onto, so `d_3 = 0` on
  `E^3_(3,0)` and `H_2(N)_Q = E^∞_(0,2)` is finitely generated.

This proves the contrapositives stated in the target.

## Part 1

- Take `N = SL_X(Q) = E(Q)`, which is perfect. By (H1), `H_2(N) = K_2(Q)`.
- `Γ` acts on `H_2(N)` through conjugation, and this action is the action of the lifted
  automorphisms on `K_2(Q) ⊆ St_X(Q)`.
  - Every `g ∈ Γ` is `f m` with `f ∈ SL_X(Q)` and `m ∈ Mon(X)`.
  - `f` acts by an inner automorphism of `St_X(Q)`, trivially on the centre `K_2(Q)`.
  - `m` acts trivially on `K_2(Q)`. This is Step 2 of `split-finitary-sl-q-extensions-are-not-fp-proof`, in brief:
    - a class `k ∈ K_2(Q)` is represented in `St_F` for a finite `F`;
    - on `St_F`, `m` acts like a finitary monomial `m'` agreeing with `m` on `F`;
    - on a larger finite block, `m'` acts like `g = m' ⊕ m'^-1 ∈ E(Q)` (Whitehead), because the two
      lifts differ by a homomorphism from a perfect `St_(F')` to the centre;
    - `g` acts by an inner automorphism, which fixes the central `k`.
- So `H_2(N)_(Γ/N) = K_2(Q)`, which is not finitely generated (Tate).
- By (H3) and Part 2, `H_3(Γ/N)` is not finitely generated, and the extension does not split.
- A group of type `FP_3` has finitely generated `H_3(-; Z)`, so `Γ/N` is not of type `FP_3`.
  Finally, `Γ = SL_X(Q)·M` with `M = Γ ∩ Mon(X)`: for `g = f m`, `m = f^-1 g ∈ Γ`. Hence
  `Γ/N ≅ M/(M ∩ N)`. ∎
