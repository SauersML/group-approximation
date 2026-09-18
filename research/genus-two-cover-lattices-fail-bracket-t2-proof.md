---
rg: 2
id: genus-two-cover-lattices-fail-bracket-t2-proof
kind: route
title: Gysin sequence over Gamma_2(4), transfer injectivity, and Shapiro's lemma
target: genus-two-cover-lattices-fail-bracket-t2
requires:
  - hoffman-weintraub-level-four-siegel-betti-numbers
---

Notation is as in the target. `Gamma_2(4) = ker(Sp_4(Z) -> Sp_4(Z/4))` has
`dim H^2(Gamma_2(4); Q) = 118`, imported from `hoffman-weintraub-level-four-siegel-betti-numbers`.

**Step 1: the level-four preimage has large H^2.**

*Case `G = Gamma~_2`.* Since `pi_1(Sp_4(R)) = Z`, the preimage `Lambda` of
`Gamma_2(4)` sits in a central extension `1 -> Z -> Lambda -> Gamma_2(4) -> 1`.
Consider the Lyndon--Hochschild--Serre spectral sequence with `Q` coefficients:
`E_2^{p,q} = H^p(Gamma_2(4); H^q(Z; Q))`. The coefficients are untwisted
because the kernel is central, so conjugation acts trivially on
`H^1(Z; Q) = Hom(Z, Q)`. They vanish for `q >= 2`. With only two rows, the
spectral sequence is the Gysin exact sequence

```text
H^0(Gamma_2(4);Q) --(cup e)--> H^2(Gamma_2(4);Q) --inf--> H^2(Lambda;Q) -> ...
```

Exactness at `H^2(Gamma_2(4); Q)` gives `dim ker(inf) <= 1`. Hence
`dim H^2(Lambda; Q) >= 117`.

*Case `G = E_n`.* The preimage `Lambda_n` sits in `1 -> C_n -> Lambda_n -> Gamma_2(4) -> 1`.
Here `H^q(C_n; Q) = 0` for `q >= 1`, so the LHS spectral sequence collapses to
`H^*(Lambda_n; Q) = H^*(Gamma_2(4); Q)` and `dim H^2(Lambda_n; Q) = 118`.

**Step 2: finite index preserves it.** Let `Delta <= G` have finite index and
put `Delta' = Delta ∩ Lambda_G`. It has finite index `m` in `Lambda_G`. Transfer
satisfies `cor ∘ res = m` on `H^2(Lambda_G; Q)`, and `m` is invertible in `Q`,
so `res : H^2(Lambda_G; Q) -> H^2(Delta'; Q)` is injective and
`dim H^2(Delta'; Q) >= 117`.

**Step 3: pass to complex coefficients.** For any group and field extension
`Q ⊂ C`, one has `H_n(-; C) = H_n(-; Q) ⊗ C` and `H^n(-; K) = Hom_K(H_n(-; K), K)`.
The natural map `Hom_Q(H_2, Q) ⊗ C -> Hom_Q(H_2, C)` is injective. Hence
`dim_C H^2(Delta'; C) >= 117`.

**Step 4: apply Shapiro.** Since `[Delta : Delta']` is finite, induction and
coinduction agree: `CoInd_{Delta'}^{Delta} C = C[Delta/Delta'] = l^2(Delta/Delta')`.
This is the unitary permutation representation `pi`, of dimension `N = [Delta : Delta']`.
Shapiro's lemma gives

```text
H^2(Delta; l^2(Delta/Delta')) = H^2(Delta'; C),   of dimension >= 117.
```

This proves `(G2T1)`, and `Delta` fails `[T_2]`.

**Step 5: the adjoint form.** Regard `M_N(C)` with `Ad pi` as `pi ⊗ conj(pi)`.
The dual permutation representation `conj(pi)` contains the constant vector,
so `pi = pi ⊗ 1` is a direct summand of `Ad pi`. Cohomology commutes with finite
direct sums, so `H^2(Delta; M_N(C), Ad pi) != 0`. The central subgroup
`Delta ∩ <z>` lies in `Delta'`, because `z` lies in `Lambda_G`, and it acts
trivially on `Delta/Delta'` by centrality, so it lies in `ker pi`.

**Why the step is sharp for the approach class.** DGLT/BLSW Theorem 1.1(F) and
BDL Conjecture 1.8 take as hypothesis vanishing of `H^2(Gamma, V)` for *all*
unitary `V`, finite-dimensional ones included. Step 4 exhibits a
finite-dimensional counterexample module inside every finite-index subgroup.
This is a dead end for that hypothesis, not for stability itself.
