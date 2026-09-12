---
rg: 2
id: binary-corner-weakly-finite-unit-representation-proof
kind: route
title: Halving pulls weakly finite corner images back to unit representations, and corners of weakly finite rings are weakly finite
target: binary-corner-weakly-finite-images-are-unit-representations
requires: [binary-leavitt-unit-group-is-simple]
artifacts:
  - research/artifacts/binary-weakly-finite-representations-2026-09-12.md
---

Artifact Section 1, Lemmas W.1–W.2 and the proof of Theorem W, parts (b) <=> (c) <=> (d).

1. **Corners (Lemma W.1).** If `W` is weakly finite, so is `pWp` for every idempotent `p`: pad `XY = p I_n`
   by `(1-p) I_n`. So is every subring containing `p`.
2. **1 => 2 (Lemma W.2).** For a nonzero quotient `q : T -> W`, `φ = q ∘ ψ'` is unital. `φ([g]) - 1` is
   `q(f(1 - [D(g)]))`, which equals `q` of `(f_(K_3) + f_(K_4))` times a block unit. If it vanished, then
   `q(f_(K_3)) = 0`. The units `π_M f_(K_3)` and `f_(K_3) π_M^(-1)` in `T` give `q(f_(K_2)) = 0`, and likewise
   `q(f_(K_4)) = 0`. So `q(f) = 0` and `W = 0`.
3. **2 => 1.** `φ(f) = u + u² != 0`, since `u² = u` would force `u = 1`. `φ(T)` is a subring of the weakly
   finite corner `φ(f) W φ(f)` with the same unit.
4. **2 <=> 3.** A homomorphism `G -> W^x` extends to `A -> W` when `W` has characteristic two. By
   simplicity, its kernel contains `g` only if it is all of `G`.

The only outside inputs are Lemma 1.1 of `research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md`
(`ψ'` is unital), the equivalence of the `f_K` inside `T` (its Theorem B, step 4 => 5), and the required
simplicity.
