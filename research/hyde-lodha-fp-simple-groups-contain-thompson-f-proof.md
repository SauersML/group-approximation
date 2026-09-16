---
rg: 2
id: hyde-lodha-fp-simple-groups-contain-thompson-f-proof
kind: route
title: Two commutators in the Higman--Thompson stabilizer have an orbital approached from one end only, so Brin's theorem gives F
target: hyde-lodha-fp-simple-groups-contain-thompson-f
requires:
  - brin-plo-i-one-sided-approach-gives-a-copy-of-f
artifacts:
  - research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md
---

Artifact Section 4. Maps compose on the left, `supp g = {x : g(x) ≠ x}`, and
`supp(g h g^{-1}) = g(supp h)`. `η = n(n+1) ≥ 6`, and `F_η` is the group of piecewise linear
homeomorphisms of `[0,1]` with finitely many breakpoints in `Z[1/η]` and slopes in `η^Z`
(Hyde--Lodha, arXiv:2302.04805, definition after Proposition 1.4, read from the PDF).

1. **The bump.**

   ```text
   f(x) = ηx on [0, η^{-2}],   x + η^{-1} − η^{-2} on [η^{-2}, 1 − η^{-1}],   1 − η^{-1}(1 − x) on [1 − η^{-1}, 1].
   ```

   - `f ∈ F_η`: slopes `η, 1, η^{-1}`, breakpoints `η^{-2}, 1 − η^{-1}`.
   - `f(x) − x` is `(η−1)x`, `η^{-1} − η^{-2}`, `(1 − η^{-1})(1 − x)` on the three pieces, so
     `supp f = (0,1)`.
   - For `p ∈ Z[1/η]`, `β_{p,m}(x) = p + η^{-m} f(η^m(x − p))` on `[p, p + η^{-m}]`, identity
     elsewhere. It lies in `F_η` and has `supp β_{p,m} = (p, p + η^{-m})`.
2. **Elements.** `u = f ∘ f`, `v_1 = β_{η^{-1},1}`, `v_2 = β_{2η^{-1} − η^{-2}, 2}`, and
   `k_i = u^{-1} v_i u v_i^{-1} = [u, v_i^{-1}] ∈ [F_η, F_η]`. Put `Q = ⟨k_1, k_2⟩`.
3. **Values of `u^{-1}`.** `f^{-1}` is `y/η` on `[0, η^{-1}]` and `y − η^{-1} + η^{-2}` on
   `[η^{-1}, 1 − η^{-2}]`. Using `2η^{-1} ≤ 1 − η^{-2}`:

   ```text
   u^{-1}(η^{-1}) = η^{-3},   u^{-1}(2η^{-1}) = 2η^{-2},   u^{-1}(2η^{-1} − η^{-2}) = η^{-2}.
   ```

4. **Supports.** `supp(u^{-1} v_i u) = u^{-1}(supp v_i)`, which is `(η^{-3}, 2η^{-2})` for `i = 1`
   and `(η^{-2}, 2η^{-2})` for `i = 2`. Both lie below `2η^{-2} < η^{-1}`, so they are disjoint
   from `supp v_i ⊂ (η^{-1}, 2η^{-1})`. Hence

   ```text
   supp k_1 = (η^{-3}, 2η^{-2}) ⊔ (η^{-1}, 2η^{-1}),   supp k_2 = (η^{-2}, 2η^{-2}) ⊔ (2η^{-1} − η^{-2}, 2η^{-1}).
   ```

   Each interval is a single orbital of the corresponding `k_i`, since a conjugated bump moves
   every point of its support.
5. **Orbital of `Q`.** `supp Q = supp k_1 ∪ supp k_2 = (η^{-3}, 2η^{-2}) ⊔ (η^{-1}, 2η^{-1})`.
   By Brin §1, orbitals are components of the support, so `A = (η^{-1}, 2η^{-1})` is an orbital
   of `Q`.
6. **One-sided approach.** The orbitals of `k_2` are `(η^{-2}, 2η^{-2})`, which is not in `A`,
   and `(2η^{-1} − η^{-2}, 2η^{-1}) ⊂ A`. The latter ends at `2η^{-1}`, and its left end is
   strictly above `η^{-1}`. So `k_2` approaches `2η^{-1}` in `A` but not `η^{-1}`.
7. **Brin.** `Q ≤ PL_o(I)`. By `brin-plo-i-one-sided-approach-gives-a-copy-of-f`, `Q` contains
   a copy of `F`. Brin writes maps on the right, but the theorem is convention-independent:
   `g ↦ g^{-1}` is an anti-isomorphism from the group to itself.
8. **Into `Q_n`.** By HL Proposition 1.4(2) there is an isomorphism `φ : F_η → Stab_{Γ_n}(0)`,
   given by the 1-periodic action (HL §3.1). Commutators go to commutators, so
   `φ(Q) ≤ [Stab_{Γ_n}(0), Stab_{Γ_n}(0)] ≤ [Γ_n, Γ_n] = Q_n`. ∎

Steps 1–6 are machine-checked for `n = 2, ..., 6` in exact rational arithmetic by
`experiments/fournier-facio-simple-factor-corner-2026-09-16/check_thompson_f_commutators.py`.
