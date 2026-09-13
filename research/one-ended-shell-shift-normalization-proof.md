---
rg: 2
id: one-ended-shell-shift-normalization-proof
kind: route
title: A shift-normalizing enumeration is affine on the unique infinite component, contradicting its near index
target: one-ended-shell-inputs-admit-no-shift-normalizing-enumeration
requires: []
artifacts:
  - research/artifacts/shell-envelope-general-2026-09-13.md
---

Suppose `phi` exists. Composition is right to left.

**1. `phi` is an injective endomorphism with `s^m lambda_h s^-m = lambda_(phi(h))` near infinity for all `h`.**
- Near identities multiply. Extend `phi` to words by
  `phi(g_1...g_k) = phi(g_1)...phi(g_k)`, with `phi(g^-1) = phi(g)^-1`. Then
  `s^m lambda_w s^-m = lambda_(phi(w))` near infinity for every word `w`.
- A nonidentity `lambda_h` moves every point, since the action is free, so it
  is not near-trivial. If `w = 1` in `P`, the left side is the identity, so
  `phi(w) = 1`. Thus `phi` descends to a homomorphism `P -> P`.
- It is injective, because conjugation preserves near-nontriviality.

**2. The transported shift.** Put `sigma = nu^-1 s^m nu`.
- If `m > 0`, `sigma` is an injection `P -> P` missing exactly the `m` points
  `M_0 = nu^-1({0,...,m-1})`.
- If `m < 0`, `sigma` is a bijection from `P \ M_0` onto `P`, with
  `|M_0| = |m|`.
- In both cases the near identity for `g` in `S` reads
  `sigma(g y) = phi(g) sigma(y)` for all but finitely many `y` where both
  sides are defined.

**3. Rigidity on the infinite component.**
- Only finitely many labeled edges `{y, gy}` of the Cayley graph `Cay(P,S)`
  break this identity. Let `A` be the finite set of their endpoints together
  with `M_0`.
- The graph `Cay(P,S)` is locally finite and connected, so `Cay(P,S) \ A` has
  finitely many components. Since `P` is one-ended, exactly one of them, `E`,
  is infinite, so `P \ E` is finite.
- For adjacent `y, gy` in `E`,
  `phi(gy)^-1 sigma(gy) = phi(y)^-1 phi(g)^-1 phi(g) sigma(y) = phi(y)^-1 sigma(y)`.
  So `phi(y)^-1 sigma(y)` is a constant `c` on the connected set `E`, and
  `sigma = theta` on `E`, where `theta(y) = phi(y) c`. The map `theta` is an
  injection of `P` with image `phi(P) c`.

**4. `phi` is onto.**
- In both cases the image of `sigma` is cofinite in `P`.
- It is contained in `theta(E) ∪ sigma(P \ E)`, which lies inside
  `phi(P) c` together with a finite set.
- If `phi(P)` had index at least 2, the complement of `phi(P) c` would contain
  a whole coset, which is infinite. So `phi` is an automorphism and `theta`
  is a bijection of `P`.

**5. Counting.**
- **Case `m > 0`.** Since `sigma` is injective and equals `theta` on `E`,
  `sigma(P \ E)` lies in `P \ theta(E) = theta(P \ E)`. Both sets have
  `|P \ E|` elements, so they are equal, and `sigma(P) = theta(P) = P`. This
  contradicts the `m` missing points.
- **Case `m < 0`.** Here `M_0` is contained in `P \ E`. The set
  `sigma((P \ E) \ M_0)` has `|P \ E| - |m|` elements, fewer than the
  `|P \ E|` points of `P \ theta(E)` that it must cover. So `sigma` is not
  onto, a contradiction.

**Consequences.**
- (1) and (2) follow because an inclusion `s^m lambda(P) s^-m <= lambda(P)`
  gives such a `phi`: each conjugate is some `lambda_h`, and `h` is unique by
  freeness.
- For the gate, `B = lambda(P)` with `B <= s^epsilon B s^-epsilon` means
  `s^-epsilon lambda(P) s^epsilon <= lambda(P)`, which is excluded with
  `m = -epsilon`.
- (3) is the first-coordinate projection of the parity fiber product.

**Zigzag check.** The permutation `f = lambda_1` sends `0 -> 1`,
`2k-1 -> 2k+1`, `2 -> 0` and `2k -> 2k-2` for `k >= 2`.
- For even `n >= 4`, `s f s^-1 (n) = f(n-1) + 1 = n+2 = f^-1(n)`.
- For odd `n >= 3`, `s f s^-1 (n) = f(n-1) + 1 = n-2 = f^-1(n)`.
