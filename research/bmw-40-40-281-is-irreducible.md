---
rg: 2
id: bmw-40-40-281-is-irreducible
kind: claim
title: The degree-(4,4) BMW group of class 40_40#281 is irreducible, and its invariant-subtree quotient is a semilinear Möbius group over F_3((s)) with elements of infinite order
distinct_from:
  bmw-44-sat-survivor-parity-kernels-not-left-orderable: that is the OPEN dichotomy "reducible or non-left-orderable parity kernel" for three classes; this settles the first alternative for #281 only, so for #281 that claim becomes the statement that Γ^+ is not left-orderable
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that refutes left orders by SAT; this is an irreducibility proof and says nothing about orders
artifacts:
  - experiments/bmw-281-linear-model-2026-09-17/README.md
  - experiments/bmw-281-linear-model-2026-09-17/mobius281.py
  - experiments/bmw-281-linear-model-2026-09-17/mobius281.log
  - experiments/bmw-281-linear-model-2026-09-17/checkaut.log
  - experiments/bmw-281-linear-model-2026-09-17/l2test.g
  - experiments/bmw-281-linear-model-2026-09-17/l2test.log
  - experiments/bmw-281-linear-model-2026-09-17/chain.log
  - experiments/bmw-281-linear-model-2026-09-17/compare.log
---

**ESTABLISHED (hand proof; its twelve rational-function identities are also checked exactly by
`mobius281.py`).** Proof: `bmw-40-40-281-irreducible-mobius-proof`.

**Setting.**
- `Γ` is the BMW group of degree (4,4) in class `40_40#281` of
  `experiments/bmw-census-left-orders-2026-09-17/census_40_40.json`, where all eight letters are
  involutions.
- `K` is the 4-state automaton group on the ternary tree obtained by restricting the vertex
  stabilizer `H_x` to its invariant subtree (`selfrep.build`; the same automaton arises on both
  sides):

  `a_0 = (a_1,a_1,a_1)`, `a_1 = (12)(a_0,a_2,a_2)`, `a_2 = (12)(a_2,a_0,a_0)`, `τ = (01)(τ,τ,τ)`.

**Theorem.** Let `O = F_3[[s]]` and `σ : s ↦ −s`. Define `Φ : {0,1,2}^ω → O` by
`Φ(xw) = t_x(Φ(w))`, where

    t_0(z) = sσ(z),   t_1(z) = C(sσ(z)),   t_2(z) = −C(sz),   C(y) = (1−y)/(1+y).

Then:
1. `Φ` is an isomorphism of rooted trees from `{0,1,2}^*` onto the residue-ball tree of `O`.
2. `Φ` conjugates `a_0, a_1, a_2, τ` to the semilinear Möbius maps
   `σ`, `−σ`, `z ↦ −z` and `T(z) = (u − z)/(1 − suz)`, where `u = 1/(1−s)`.

   So `K ≅ ⟨σ, −σ, −z, T⟩ ≤ PGL_2(F_3((s))) ⋊ ⟨σ⟩`, inside the semilinear Iwahori subgroup
   (lower-left entry in `sO`).
3. `τa_2` corresponds to `z ↦ (z + u)/(suz + 1)`, which has infinite order: its eigenvalue ratio is
   a principal unit `≠ 1` of `F_3[[√s]]`.
4. Hence `K` is infinite and not torsion. So `H_x` is infinite, `pr_V(Γ)` is non-discrete, and `Γ`
   is irreducible (Burger–Mozes, Prop. 1.2).

**Consequences for the census.**
- `40_40#281` is an irreducible BMW lattice whose parity kernel `Γ^+` survives the positive-cone SAT
  test through radius 10 (`bmw-44-sat-survivor-parity-kernels-not-left-orderable`).
- For this class the dichotomy there reduces to one question: is `Γ^+` left-orderable?
- The earlier heuristic that `K` is a Gupta–Sidki-type torsion group is false.
- The planned hand proof that `L_2` is self-replicating at `0` cannot exist. Modulo level 5,
  `φ_0(Stab_{L_2}(0))` has index 3 in `L_2`, and three of the eight generators lie outside it
  (`l2test.log`).
- The linear model explains this: the section chain lives in the decreasing congruence levels of
  the Iwahori group.

**Not claimed.** That `K` is dense in the semilinear Iwahori group. The level orders
`4·3^{3m−2}` agree through level 7 (`chain.log`), and `compare.log` matches the two groups on every
computed invariant for `m ≤ 4`. Nor is any statement made about `pr_V(Γ)` or `H_x` beyond this
quotient.
