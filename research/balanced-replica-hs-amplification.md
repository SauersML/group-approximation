---
rg: 2
id: balanced-replica-hs-amplification
kind: claim
title: Balanced replicas keep the multiplicative defect small while crushing the trace
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Lemma.**  For `U, V ∈ U(d)` write `d_2(U,V)^2 = (1/d)‖U-V‖_F^2 = 2 - 2 Re tau(U*V)`
and put `B(U) = U ⊗ conj(U)`.  Then for every `m ≥ 1`

```text
d_2( B(U)^{⊗m} , B(V)^{⊗m} )^2  ≤  2m · d_2(U,V)^2,
tau( B(U)^{⊗m} )                =  |tau(U)|^{2m}.
```

**Proof.**  Set `a = tau(U*V)`, so `Re a = 1 - delta^2/2` with
`delta = d_2(U,V)`.  Entrywise conjugation satisfies `conj(U)^* = conj(U^*)`,
so `tau(B(U)^* B(V)) = tau(U^*V) · conj(tau(U^*V)) = |a|^2`, whence

```text
d_2(B(U),B(V))^2 = 2 - 2|a|^2 ≤ 2 - 2(Re a)^2 = 2 delta^2 - delta^4/2 ≤ 2 delta^2,
```

and in particular `1 - |a|^2 ≤ delta^2`.  For `m` copies the normalized trace
is multiplicative, `tau((B(U)^*B(V))^{⊗m}) = |a|^{2m}`, so
`d_2^2 = 2(1-|a|^{2m}) ≤ 2m(1-|a|^2) ≤ 2m·delta^2` using `1-t^m ≤ m(1-t)` on
`t = |a|^2 ∈ [0,1]`.  The trace identity is multiplicativity of `tau` under
tensor products together with `tau(conj(U)) = conj(tau(U))`.  ∎

**Why it is worth a node.**  It fixes the parameter coupling that every
"take many replicas and classicalize" argument needs.  Given unitary tables of
defect `delta_n → 0`, choose `m_n → ∞` with `m_n delta_n^2 → 0` (e.g.
`m_n = ⌊delta_n^{-1}⌋`): the balanced `m_n`-fold table still has multiplicative
defect tending to zero, so **the number of symmetric replicas may go to
infinity independently of how fast the matrix dimension explodes**.  Any
rounding theorem whose error is `O(m^{-1/2})` with dimension-free constants —
which is exactly the shape of the 2026 Hilbert–Schmidt de Finetti bound cited
in `definetti-group-table-rounding` — can then be applied at a level `m` chosen
*after* the finite table and *before* the microstate.

Balancing is not cosmetic.  Plain tensor powers accumulate scalar phase:
`U = e^{i theta} I`, `V = I` have `d_2(U,V)` arbitrarily small while
`U^{⊗m} = e^{i m theta} I` is far from `V^{⊗m}` once `m theta ≈ 1`.  Doubling
against the conjugate representation kills the phase before amplification,
and simultaneously converts trace separation `|tau(U_w)| ≤ eta` into
`|tau(U_w)|^{2m}`, i.e. separation improves under the same operation that
creates the replicas.

Two scope limits.  (i) The construction is a homomorphic reparametrization of
the *table*, not of the group: `g ↦ B(U_g)^{⊗m}` is again a unitary table on
the same finite window, in dimension `d^{2m}`, and nothing here says the
enlarged table is any easier to round.  (ii) `tau(B(U)^{⊗m}) → 0` needs
`|tau(U)| < 1`, so the amplification separates only elements the original
table already separated.

Source and re-derivation: `research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md`
(its Lemma 4.1 and Consequence 4.2; the proof above was re-derived here).
