---
rg: 2
id: shift-homology-in-positive-degree-is-inert-under-automata-proof
kind: route
title: Pattern functions form a permutation basis with finite stabilizers, so positive-degree homology sees only constants
target: shift-homology-in-positive-degree-is-inert-under-automata
requires: []
artifacts:
  - research/artifacts/shift-homology-inertness-and-coset-calibration-2026-09-17.md
  - experiments/cohopfian-shift-homology-2026-09-17/check.py
---

## Direct proof

The full details are in the artifact, §1, §2 and §4. The script checks the finite
computations exactly.

1. **Permutation basis.**
   - Fix `a0 in A` and `A' = A \ {a0}`. The functions
     `e_{F,c}(x) = prod_{w in F}[x(w) = c(w)]`, for finite `F` and `c : F -> A'`, form a
     `Z`-basis of `C(A^Omega, Z)`.
   - The reason: `Z^A` has basis `{1} ∪ {delta_a : a in A'}`. Take tensor products over a
     window, then the direct limit.
   - The action is `g e_{F,c} = e_{gF, c o g^-1}`. So `C(A^Omega, Z)` is `Z·1` plus a
     permutation module with stabilizers `G_{F,c}` inside the setwise stabilizers of the `F`.
2. **Finite stabilizers.** For `Omega = G`, `gF = F` with `F` nonempty finite forces
   `g in F F^-1`. So all `G_{F,c}` are finite.
3. **Projectivity.** For finite `H`, the idempotent `e_H = |H|^-1 sum h` shows that
   `Q[G/H] = QG e_H` is a summand of `QG`. By flat base change, `H_n(G; M) = Tor_n^{QG}(Q, M)`
   for a `QG`-module `M`. Tor vanishes on projectives in degree `n >= 1` and commutes with
   direct sums. So the inclusion of constants induces `H_n(G; Q) ≅ H_n(G; C(A^G,Q))` for
   `n >= 1`. For torsion-free `G` the module is free over `ZG`, so the same holds over `Z`.
4. **Automata.** `tau^* f = f o tau` is a `ZG`-map and fixes `1`, so `tau^*` commutes with the
   inclusions of constants. Hence `H_n(tau^*)` is the canonical identification.
5. **Maps over a base.**
   - `C(Y × A^G, Q) = C(Y,Q) ⊗ C(A^G,Q)` (locally constant functions on a product of totally
     disconnected compacta). With the diagonal action, `C(Y,Q) ⊗ Q[G/H] ≅ QG ⊗_{QH} Res_H C(Y,Q)`
     is projective, since `Res_H` is projective by Maschke and induction preserves projectives.
   - So `u -> u ⊗ 1` is an isomorphism on `H_n`, `n >= 1`.
   - A map `Phi` over `id_Y` fixes every `u ⊗ 1`, so `H_n(Phi^*) = id`.
6. **Calibration.** In `BS(1,2) = Z[1/2] x| Z`, with `t a^r t^-1 = a^(2r)`, `K = <a>` and
   `p(gK) = g t^-1 K`:
   - `p` is well defined, because `k t^-1 K = t^-1 k^2 K`. It is equivariant, with fibres of
     size 2, and `G_{p(eK)} = t^-1 K t = <a^(1/2)>`.
   - The parent-copy automaton satisfies `tau^* e_F = e_{p(F)}`, so it preserves the summand
     `Q[V]`.
   - By Eckmann–Shapiro (`Q[G/K] = QG ⊗_{QK} Q` with `QG` free over `QK`),
     `H_1(G; Q[V]) = H_1(K; Q) = Q`.
   - The map `v -> p(v)` is the projection `G/K -> G/L` with `L = t^-1 K t`, followed by the
     isomorphism `gL -> g t^-1 K`. On `H_1` these act as corestriction `[a] -> 2[a^(1/2)]`
     and conjugation `a^(1/2) -> t a^(1/2) t^-1 = a`.
   - So `tau^*` acts on this `Q` as `×2`. A summand injects on homology, so `tau^* ≠ id` on
     `H_1(G; C({0,1}^V, Q))`. ∎

The route uses no imported theorem. Maschke's theorem, flat base change for Tor and
Eckmann–Shapiro for induced modules over free extensions are textbook homological algebra, each
with its one-line reason given inline.
