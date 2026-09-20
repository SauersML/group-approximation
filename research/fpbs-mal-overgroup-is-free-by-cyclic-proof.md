---
rg: 2
id: fpbs-mal-overgroup-is-free-by-cyclic-proof
kind: route
title: Two mutually inverse homomorphisms between M and F(u,v,w) x| <b>, from the Magnus rewrite of r at psi = (1,1)
target: fpbs-mal-overgroup-is-free-by-cyclic
requires: []
artifacts:
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/semidirect.py
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/semidirect_out.txt
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/magnus.py
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/magnus_out.txt
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/fox.py
  - experiments/fpbs-mal-free-by-cyclic-2026-09-17/fox_out.txt
---

Let `s = t b^-1` and `y_i = b^i s b^-i` in `F(b, t)`.

1. **Magnus rewrite.** Substitute `t = s b` in `r` and track the `b`-height.
   This gives, up to cyclic permutation (so up to conjugacy in `F(b,t)`),
   ```text
   r ~ y_0 y_0 y_1^-1 y_2^-1 y_0 y_-1^-1
   ```
   (`magnus.py`, row `psi=(1,1)`). So in `M`,
   `y_2 = y_0 y_-1^-1 y_0^2 y_1^-1`.
2. **`Θ` is an automorphism.** `Θ^-1 Θ` and `Θ Θ^-1` fix `u, v, w`
   (`semidirect.py`, check 1). So `P := F(u,v,w) ⋊_Θ <b>` is defined.
3. **`φ: M → P`.** Set `b ↦ b`, `t ↦ v b`, `a ↦ u v^-1 b^2`. Check 2 of
   `semidirect.py` verifies `[t, a] = 1` and `t b t^-1 = b a b^-2` in the
   faithful normal form `(word, n)`.
4. **`ρ: P → M`.** Set `b ↦ b`, `v ↦ y_0`, `u ↦ y_-1`, `w ↦ y_1`. The
   defining relations `b x b^-1 = Θ(x)` hold:
   - `x = u`: `b y_-1 b^-1 = y_0`;
   - `x = v`: `b y_0 b^-1 = y_1`;
   - `x = w`: `b y_1 b^-1 = y_2 = y_0 y_-1^-1 y_0^2 y_1^-1 = ρ(v u^-1 v^2 w^-1)`,
     by step 1.
5. **Mutually inverse.**
   - On `M`: `ρφ(b) = b` and `ρφ(t) = y_0 b = t`. Also
     `ρφ(a) = y_-1 y_0^-1 b^2 = b^-1 t b t^-1 b^2 = a`.
   - On `P`: `φρ(b) = b` and `φρ(v) = φ(t b^-1) = v`. Also
     `φρ(u) = b^-1 v b = Θ^-1(v) = u` and `φρ(w) = b v b^-1 = Θ(v) = w`.
6. **Kernels.**
   - `r` abelianises to `0` (`fox.py`), so `M^ab = Z^2` is torsion-free and
     `K = [M, M] = ker(M → Z^2)`.
   - Each of `u, v, w` maps to `(−1, 1)` in `(b, t)`-coordinates. So
     `K = ker(F_3 → Z^2) = ker ε`, a normal subgroup of `F_3` with quotient
     `Z`, which is free of infinite rank.
   - `ε` is `Θ`-invariant (check 3), so `K` is `b`-normalised.
   - For each primitive `psi`, `ker psi / K = ker(psi on Z^2) ≅ Z` splits.
     The listed lifts `b, t, t b^-2, t b^-1` have `psi`-value `0` at
     `(0,1), (1,0), (1,2), (1,1)` respectively.
   - The stage is `<a, b> = <u v^-1 b^2, b> = <u v^-1, b>`.
7. **Alexander data.** `fox.py` computes the Fox derivatives and checks the
   fundamental formula. It returns `Δ = −(x^2 + x + y − 1)/x`, whose Newton
   support is `(1,0), (0,0), (−1,1), (−1,0)`. After multiplying by `x`, that
   is the triangle `(0,0), (2,0), (0,1)`. The width formula is the support
   function of this triangle.
