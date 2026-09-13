---
rg: 2
id: o2-multiplier-ideal-with-non-k1-injective-unitization
kind: claim
title: Some non-unital C*-algebra with a unital O_2 in its multiplier algebra has a non-K1-injective unitization
artifacts:
  - research/artifacts/lxi-o2-multiplier-reduction-2026-09-12.md
  - research/artifacts/k1-o2-ideal-finite-nuclear-dimension-2026-09-13.md
---

There is a non-unital C\*-algebra `I` with Cuntz isometries `S_1, S_2 ∈ M(I)`,
`S_1S_1^* + S_2S_2^* = 1`, and a unitary `u = 1 + x ∈ Ĩ` with `[u] = 0` in `K_1(I)` but `u ∉ U_0(Ĩ)`.
Equivalently, `1 + x` is not null-homotopic in `Ĩ`, while `1 + S_1^k x S_1^{*k}` is for some `k`. By
`o2-multiplier-extension-k1-injective-iff-unitization` this refutes STW Problem LXI.

## Attempts

- Necessary structure (artifact, Proposition 4): `I ≅ M_2(I)` through the isometries; `I` has no
  nonzero finite-dimensional representation; `I` is not stable; `I = C_0(Y) ⊗ D` with `O_2 ⊆ D` only
  reproduces LXI for `D`. Module form: `I = K(E)` with `E ≅ E ⊕ E`, and non-nullness is detected at
  finite stages `End(E_n)`.
- Euler-class protection dies (`euler-class-protection-fails-for-o2-self-similar-modules`). Over
  commutative stages the complement `P_n` of a trivial rank-two witness support has `e(P_n) = 0` at
  late stages. So the LIX odd top Chern number and Toms's trapped spin-bordism class cannot protect a
  witness here. A protection is needed that is not killed by `P ⊕ θ^2 ≅ θ^4 ⊕ η`.
- Not attempted yet: non-commutative stages with infinite dimension-rank ratio (Villadsen algebras of
  infinite stable rank), and non-type-I `I` such as hereditary subalgebras `her(a)` of `B ⊗ K` with
  `a ⊕ a ~ a` over a finite algebra `B` failing comparison.
- Finite nuclear dimension (lane ex-k1-halving-homotopy, established
  `o2-ideal-finite-nucdim-counterexample-unital-quotients`).
  - The recalled pointer "no bounded traces implies stable" is false as stated: `C_0([0,1)) ⊗ O_2` fails it.
  - Robert's criterion (arXiv:1002.2180v2, Corollary 1) also needs no nonzero unital quotients.
  - Such `I` never have bounded traces. So a σ-unital witness of finite nuclear dimension has a unital
    quotient containing `O_2`.
  - Its largest ideal without unital quotients is stable and can be divided out.
- The halving isometry is not strictly pure (same lane). If `I` is σ-unital and `S_1^n S_1^{*n}` converges
  strictly, Wold's decomposition gives `I ≅ H_I ⊕ P_∞ I`. Mingo--Phillips and Kasparov stabilization then
  give `I ≅ I ⊗ K`. So every witness `I` has non-convergent `S_1^n S_1^{*n}`.
- Commutative modules over contractible bases (same lane). Let `I = K(E)` over the Hilbert cube, with `E`
  exhausted by complemented finitely generated submodules. Every stage is free, so its unitary group
  `C(Q, U(r))` is connected, and `Ĩ` is K1-injective. Hilbert-cube witnesses need Dixmier--Douady-type
  modules with no complemented finitely generated exhaustion. Over non-contractible infinite-dimensional
  bases, a protection would have to be a secondary obstruction that survives trivial summands, for
  example with `π_{2r}(S^{2r-1}) = Z/2` coefficients. None has been constructed.
- Strict isometry path criterion: a strictly continuous isometry path from `1` to `S_1` in `M(I)` makes `Ĩ`
  K1-injective. Any unital quotient of `I` blocks it.
