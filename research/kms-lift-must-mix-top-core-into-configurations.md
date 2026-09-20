---
rg: 2
id: kms-lift-must-mix-top-core-into-configurations
kind: claim
title: Mixed Frobenius exponents on the KMS top - if every cycle of the counter permutation is non-contracting the action is unfaithful, so faithfulness needs at least one contracting cycle; and a KMS lift with non-contracting counters must send the resulting B_0-core into the configuration module, where T being abelian makes a T-component of F(A_0) invisible to T and visible only to the top relations
distinct_from:
  kms-top-renormalizations-must-contract: that proves the uniform-exponent case; this proves the mixed case, factor by factor, and states the design constraint it leaves for a lift.
  kms-configuration-lift-needs-non-contracting-counters: that asks for non-contracting counters; this says where the needed contraction can go and how the rest must be absorbed by T.
  two-counter-kms-groups-are-self-similar: that is the crux KD2_p; this is an attempt record under it.
---

**ESTABLISHED (lane bh-kd2p, 2026-09-19):**
- **Theorem M** is a lane proof.
- **Parts L and D** are an attempt record.
- KD2_p stays **OPEN**. Not independently reviewed.

## Theorem M (mixed exponents)

**Setting.** As in `kms-top-renormalizations-must-contract`, with `K ≥ 2` and `f : H → B_K` a virtual
endomorphism. Suppose the renormalization has **product Frobenius–Möbius form**:
- `U_H = ∏_i ⟨s_i^{p^{e_i}}, (1 − s_i)^{p^{e_i}}⟩`, so `S = ⊗_i Frob^{e_i}(R^{(i)})`, where `R^{(i)}` is the
  `i`-th one-variable factor;
- there are a permutation `π` of `{1, …, K}`, ring isomorphisms `σ_i : R^{(i)} → R^{(π(i))}` defined over `F_p`,
  and integers `j_i` with `e_i + j_i ≥ 0`, such that `ψ̃(Frob^{e_i}(a)) = Frob^{e_i + j_i}(σ_i(a))` for
  `a ∈ R^{(i)}`.

**Statement.** If `Σ_{i∈C} j_i ≥ 0` for every cycle `C` of `π`, i.e. no cycle contracts, then `f` is not simple.
So a faithful action in this class has at least one contracting cycle.

**Proof.**
- **Weights.** Pick integers `w_i ≥ e_i` with `w_{π(i)} ≤ w_i + j_i` for all `i`. This is possible exactly when
  every cycle has `Σ j ≥ 0`: set the weights along each cycle by the running sums, and shift them up.
- **The ideal.** Let `Z_0` be the set of points of `P^1(F_{p^r}) \ {0, 1, ∞}`. Möbius maps defined over `F_p`
  permute it. Put `𝔞 = ∏_{c∈Z_0} (x − c)^N` in each factor, and `𝔟 = ∏_i Frob^{w_i}(𝔞^{(i)})·R`, a nonzero
  ideal of finite codimension.
- **`𝔟` lies in the domain.** `M` contains a finite-codimension ideal `∏_{z∈Z} 𝔪_z^{N'}`. Take `r` and `N`
  large, with `Z_0` containing every coordinate of the points of `Z`. Since `(x_i − c_i)^N ∈ 𝔪_z` for each `i`, we
  get `𝔟 ⊆ ∏_i 𝔞^{(i)} R ⊆ ∏_z 𝔪_z^{N'} ⊆ M`.
- **`𝔟` is invariant.**
  - A generator of `𝔟` is `c = ∏_i Frob^{w_i}(a_i)`. It lies in `S`, since `w_i ≥ e_i`.
  - `ψ̃(c) = ∏_i Frob^{w_i + j_i}(σ_i a_i)`. Its `i`-th factor lies in `Frob^{w_{π(i)}}(𝔞^{(π(i))})`, because
    `w_i + j_i ≥ w_{π(i)}` and `σ_i(𝔞^{(i)}) = 𝔞^{(π(i))}`.
  - `π` is a bijection, so `ψ̃(c) ∈ 𝔟`.
  - By the Hartogs extension `f̂` (part (b) of `kms-top-renormalizations-must-contract`),
    `f(cr) = ψ̃(c) f̂(r) ∈ 𝔟`.
- So `𝔟` is a nonzero normal subgroup in the domain with `f(𝔟) ⊆ 𝔟`, and it lies in the core. ∎

**Remarks.**
- For `π` a single cycle with all `e_i = e` and all `j_i = j`, this is part (c) of the uniform-exponent theorem.
- Kochloukova–Sidki is `π = (1 2 ⋯ K)`, with `j_1 = −1` and the other `j_i = 0`: one contracting cycle.

## Part L. What is left on the top, and a failed shortcut

- **What Theorem M allows.** Partially contracting renormalizations: some cycles contract, supplying faithfulness,
  while the others are isometric or expanding and could carry the machine's counters without shrinking.
- **The naive dummy-counter shortcut fails.** One could try adding unused counters, running Kochloukova–Sidki on
  them and the identity on the real counters, via the tensor product `id ⊗ f_KS`. But the domain
  `R_real ⊗ M_dummy` then has infinite index, because `R_real` is infinite-dimensional. So this is not a virtual
  endomorphism.
- **Open.** Does a partially contracting renormalization of `B_K` with a finite-index domain exist at all?

## Part D. The design constraint for a lift (attempt record)

- **B_0 does not see the machine.** By G5c, the machine part `T_0 = ⟨x_{qA_0}⟩` of `T` is fixed by
  `M_0 = {ã_i, ã_i', A_0}`. Also, the hard equalities of KMS Theorem 4.3(b) live in `T_0` under the counters
  `a_i` of the one-variable factors `B_i`, which are Krull-dimension-1 factors and so not subject to Theorem M.
- **The core must be absorbed by `T`.**
  - Let a lift `F` of `G(M)` induce, modulo `T`, a virtual endomorphism `F̄` of `B_0` with non-contracting
    counters.
  - Then `F̄` has a nonzero core `𝔟`, by Theorem M. So `F(𝔟 ∩ H) ⊆ T·𝔟`.
  - Faithfulness of `G(M)` then requires the `T`-components of iterates of `F` on `𝔟` to separate its elements.
- **Where a `T`-component can live.** `T` is abelian, so for `t ∈ T` conjugation by `tA_0` on `T` equals
  conjugation by `A_0`. A choice `F(A_0) = tA_0` is invisible to the `T`-relations G5–G8. It is constrained only
  by the top relations:
  - `(tA_0)^p = t·(A_0 − 1)^{p−1} = 1` in module notation;
  - the BR relations of `B_0` under conjugation by `F(ã_i)`, `F(ã_i')`.
- **The concrete next step.** Find `t ∈ T` with `t(A_0 − 1)^{p−1} = 0`, compatible with G4 under the `F̄`-images
  of the `ã_i`, such that the iterates separate `𝔟`. Since `x_{qA_0}(A_0 − 1) = 0` by G5c, the elements of `T_0`
  satisfy the exponent condition automatically. **So the machine module itself can supply the mixing:
  `t ∈ T_0`.**

## Lesson

**On the KMS top, faithfulness costs one contracting cycle, and the core it leaves must be absorbed by the
machine module.** A hard self-similar KMS group, if it exists, renormalizes the top by a map that is not
faithful on the top alone. It is rescued by writing configuration elements into the images of the top lamps,
e.g. `F(A_0) = tA_0` with `t ∈ T_0`.
