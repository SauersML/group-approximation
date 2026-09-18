---
rg: 2
id: jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group
kind: claim
title: The binary Jacobson group GL_n(J) = EL_n(J) is the quotient of a LEF group, its fibre product with the mirror Toeplitz extension, by a locally finite simple normal subgroup
distinct_from:
  untwisted-bilateral-symbol-enrichment-is-lef: that proves the bilateral semidirect product H_bi is LEF and says replacing the Toeplitz extension by it erases the load-bearing relation; this shows the actual extension, fibred with its mirror over the symbol, is a subgroup of H_bi, so the Toeplitz cocycle is cancelled by the mirror cocycle and all remaining difficulty sits in one quotient by a locally finite kernel.
  jacobson-one-sided-symbol-preimages-are-lef: that proves the two half preimages are LEF; here that follows as the special case of subgroups over which the mirror extension splits, and the whole group is covered as a quotient.
  binary-jacobson-core-is-weakly-sofic-with-fd-head-radical: that records E as locally finite by residually finite, the open extension direction; this records E as LEF modulo locally finite, the open quotient direction, with an explicit ambient LEF group.
  sofic-quotients-by-finite-normal-subgroups-are-sofic: that passes soficity to quotients by finite kernels; the kernel here is infinite, locally finite and simple, and the orbit-set argument fails at the step recorded in (MQ5).
---

**ESTABLISHED** (route `jacobson-toeplitz-extension-mirror-quotient-proof`).

**Notation.**
- `J = F_2<S,T | TS=1>`, `Q = 1-ST`, and `A = F_2[z,z^(-1)]`.
- `W = F_2^(Z x {1..n})` is finitely supported, with basis `e_(k,i)`.
- `V_+ = span{e_(k,i) : k >= 0}` and `V_- = span{e_(k,i) : k < 0}`.
- `J` acts on the `k`-coordinate of `V_+` by `S e_k = e_(k+1)`, `T e_0 = 0` and
  `T e_(k+1) = e_k`. It acts on `V_-` through the mirror basis
  `e'_k = e_(-1-k)` by the same formulas.
- `E_+` and `E_-` are `GL_n(J)` in these two actions.
- The symbols are `pi_+ : S -> z, T -> z^(-1)` and `pi_- = theta o pi_+`,
  where `theta(z) = z^(-1)`.
- `L_+- = GL_fin(V_+-)`, and `H_bi = GL_fin(W) x| EL_n(A)` is the untwisted
  bilateral group of `untwisted-bilateral-symbol-enrichment-is-lef`.
- `n >= 3`.

**(MQ1) General linear equals elementary.** `GL_n(J) = EL_n(J)` for every
`n >= 2`, and `pi_+(GL_n(J)) = SL_n(A)`.
- The determinant of every symbol is `1`, by Fredholm index.
- So in `leavitt-corner-toeplitz-support-class-is-jacobson-hyperlinearity`
  the Whitehead sandwich `(TJ1)` collapses: `EL_20(J) = GL_20(J)`. The worry
  there that `GL_20(T_2)` need not lie in `EL_20(T_2)` does not arise.

**(MQ2) Mirror fibre product.** Put
`P = E_+ x_(SL_n(A)) E_- = {(g,h) : pi_+(g) = pi_-(h)}`. Then
`(g,h) |-> g (+) h` is an injective homomorphism `P -> H_bi`, landing in
invertible operators on `W` of the form "Laurent matrix plus finite rank".
Hence **`P` is LEF**, so sofic and hyperlinear.

**(MQ3) The quotient.** The projection `P -> E_+` is onto, with kernel
`{1} x L_-`. So

```text
EL_n(J) = GL_n(J) = P / L_-,     P <= H_bi LEF,     L_- infinite, locally finite, simple.   (MQ)
```

The head `w = x_13(Q)` lifts to `(w,1)`, which in `H_bi` is a nonidentity
finitary transvection.

**(MQ4) Split subgroups are LEF.** Let `A_0 <= E_+` be such that
`E_- -> SL_n(A)` has a homomorphic section `s` over `pi_+(A_0)`. Then
`a |-> (a, s(pi_+ a))` embeds `A_0` in `P`, so `A_0` is LEF.
- Toeplitz compression of polynomial matrices is multiplicative. So
  `SL_n(F_2[z^(+-1)])` lifts to both halves, and this recovers
  `jacobson-one-sided-symbol-preimages-are-lef`.

**(MQ5) Where the finite-kernel orbit transplant dies.** No nontrivial finite
subgroup of `L_-` is normalized by a generating set of `P`.
- **Invariant.** `V_-^n` is a simple `M_n(J)`-module, and the group algebra of
  any generating set of `E_-` spans `M_n(J)`.
- **Step where it dies.** The orbit-set construction of
  `sofic-quotients-by-finite-normal-subgroups-are-sofic` needs a finite kernel
  normalized by the inspected generators. Exhausting `L_-` by finite subgroups
  does not supply one.

**Impact.**
- **Where the obstruction must live.** The Toeplitz twist is not an
  obstruction by itself: paired with its mirror it disappears inside a LEF
  group. Any proof that `EL_3(J)` is not sofic (or not hyperlinear) must use a
  property that does **not** lift from `P/L_-` to the LEF group `P`. Properties
  held by all subgroups of `H_bi`, including every relation pattern in finitely
  many elements of `P`, cannot serve. Only the quotient step by `L_-` can carry
  it.
- **What a positive answer needs.** `EL_3(J)` is sofic iff `P` has sofic
  approximations that are asymptotically trivial on each finite subset of `L_-`
  and stay separated off `L_-`.
  - By (MQ5), the obvious construction of such approximations is not
    available.
  - In the periodic LEF models, `L_-` acts faithfully.
- **Relation to the Kourovka question.** (MQ) is an explicit LEF analogue of
  the class in Thom's Kourovka question 21.118 (quotients of residually finite groups by
  amenable normal subgroups), recorded in
  `research/artifacts/sk-questions-ggt-literature-2026-09-13-part2.md`. So a
  general permanence theorem "LEF modulo locally finite is sofic" would settle
  the Jacobson branch positively. It would also refute
  `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`. That permanence
  is not known.
