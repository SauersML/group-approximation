---
rg: 2
id: cancellative-incidence-patterns-do-not-force-domination-proof
kind: route
title: Shared-pointer parity gadget with exact coupon residual, Evans embedding with a loop isotope, and a Z/3 group-ring contradiction
target: cancellative-incidence-patterns-do-not-force-domination
requires: [sofic-radical-localizes-bernoulli-deficit-witnesses]
artifacts:
  - research/artifacts/right-cancellative-pattern-firewall-2026-09-12.md
  - research/artifacts/cancellative-firewall-reverification-2026-09-17.md
  - experiments/cancellative-firewall-2026-09-17/verify_gadget.py
  - experiments/cancellative-firewall-2026-09-17/verify_gadget.json
---

The proof is Sections 2-6 of the 2026-09-12 artifact. The independent re-derivation is Sections 1-3 and 5 of the
2026-09-17 artifact.

1. **Theorem A.**
   - **The pattern.** (L), (R), the shared pointer set and `V_1 Δ V_2 Δ V_3 = {o}` were checked by hand and by program
     for `k = 4, 8, 16, 32`.
   - **Entropy of the code.** `H(psi) = t + 1`.
   - **The residual.** The outputs of gadget `g` are `(j_g, x0[j_g] + A + B)`, `(j_g, A + C)` and `(j_g, B + C)`, with
     `(A, B, C)` uniform given `J` and `x0`. So `y_F` is equivalent to `J`, independent uniform masks and
     `(x0[j_g])_g`. Hence `H(x0 | y_F) = E #unrevealed = k (1 - 1/k)^R` exactly.
   - **Checks.** Exact enumeration: `1.0`, `0.5`, `3.0` on three small instances. Monte Carlo at `k = 4, 8`: 0 decoding
     errors.
   - **Result.** `Phi = (t + 1 + k(1 - 1/k)^R)/k <= (log2 k + 1 + 1/k)/k`. For `k = 4` this is `0.7817`.
2. **Theorem B.**
   - Evans (T. Evans, *Embedding incomplete latin squares*, Amer. Math. Monthly 67 (1960) 958-961): "an incomplete
     latin square of order n can be embedded in a complete latin square of order 2n".
   - The isotope `x ∘ y = (x / v) · (u \ y)` has identity `u · v = o` and preserves the incidence
     `(f · v) ∘ (u · e) = f · e`.
   - Built explicitly for `k = 4`: a loop of order 530.
3. **Theorem C.** `delta = c_1^-1 c_2` stabilizes `P`, and the stabilizer acts freely, so it is `Z/3`. Then
   `c_1 (1 + delta + delta^2) Ê = x0`, and left multiplication by `c_1 (1 + delta) c_1^-1` gives `0 = x0 + x0'` with
   `x0' != x0`. It also follows from `quadrangle-closure-kills-shared-pointer-parity-gadgets`, but it is not routed
   through it.
4. **Consequences.**
   - **Average domination only.** On the loop the count gives average domination, and nothing at `o`.
   - **Tree star.** It reveals `2^(d+1) - 2` coordinates, gives `Phi <= (t + d + 1/k)/k`, and violates (R).
   - **Downward tree windows.** They embed in the free monoid, hence in the free group, with no extra coincidences.
     By the required claim, consequence "every sofic group is Rokhlin-maximal at every `q`", they have
     `Phi >= log q`.
