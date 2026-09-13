---
rg: 2
id: artin-type-f-k-plus-1-iff-salvetti-pi-k-fg
kind: claim
title: "An Artin group whose Salvetti complex has pi_i = 0 for 2 <= i < k is of type F_{k+1} iff pi_k of the Salvetti complex is a finitely generated module"
---

Let `X` be a finite connected CW complex with `π_1(X) = G`, and let `k ≥ 2` be such
that `π_i(X) = 0` for `2 ≤ i ≤ k − 1` (no condition when `k = 2`). Regard `π_k(X)` as a
left `ZG`-module through the action of `π_1`. Then `G` is of type `F_k`, and the
following are equivalent:

1. `G` is of type `F_{k+1}`;
2. `G` is of type `FP_{k+1}`;
3. `π_k(X)` is finitely generated as a `ZG`-module.

**For Artin groups.** For every finite Coxeter graph `Γ` the Salvetti complex
`Sal(Γ)/W` is a finite CW complex with fundamental group `A_Γ` (L. Paris,
*K(π,1) conjecture for Artin groups*, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1211.7339,
Theorem 3.10; R. Charney and M. W. Davis 1995; M. Salvetti 1994). So:

- every Artin group `A` is of type `F_3` iff `π_2(Sal(A))` is a finitely generated
  `ZA`-module;
- if `π_2(Sal(A)) = ⋯ = π_{k−1}(Sal(A)) = 0`, then `A` is of type `F_{k+1}` iff
  `π_k(Sal(A))` is a finitely generated `ZA`-module.

The K(π,1) conjecture (`artin-group-k-pi-1-conjecture`) asks for `π_k(Sal(A)) = 0` for
all `k ≥ 2`. Its first step, the "K(π,1) conjecturette" `π_2(Sal(A)) = 0`, is open in
general: R. Boyd, *An introduction to the geometric and combinatorial group theory of
Artin groups*, arXiv:2601.08658v1, §2.3.7, records that the claimed proof was retracted
by Elias and Williamson. Type `F_3`, and inductively type `F_∞`, only needs finite
generation of the first nonvanishing homotopy module, not its vanishing.

This is the precise form of "type `F_∞` without the K(π,1) conjecture" used on the
direct side of Zaremsky Problem 1.5 (`every-artin-group-is-type-f-infinity`). The proof
route is `artin-type-f-k-plus-1-iff-salvetti-pi-k-fg-proof`.
