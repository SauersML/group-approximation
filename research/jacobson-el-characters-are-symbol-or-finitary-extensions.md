---
rg: 2
id: jacobson-el-characters-are-symbol-or-finitary-extensions
kind: claim
title: Every character of EL_n(J) is a symbol character or the zero extension of a nontrivial character of the finitary kernel
distinct_from:
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that proves, for CONNES-EMBEDDABLE characters only, that either tau is trivial on L or the scalar kernel is trivial; this classifies ALL characters of EL_n(J) exactly (tau is trivial on L, or tau vanishes off L and is the zero extension of a nontrivial character of L), and gives the trace decomposition with the high-rank limit lambda_tau.
  degree-zero-leavitt-core-characters-are-dirac-haar-mixtures: that classifies characters of the tensor-tower core of the Leavitt group, where every character is w*1+(1-w)*delta; this classifies characters of the Jacobson elementary group, whose finitary kernel is a corner tower carrying the whole countable Thoma--Skudlarek family.
  finitary-extension-ce-iff-action-lifts-to-normalizer: that is a lifting criterion for Connes embeddability of crossed products of R; this is a character classification, which shows that every CE character of EL_n(J) not factoring through the symbol is a zero extension from L, whose GNS algebra is a cocycle crossed product over the finitary kernel.
  subshift-elementary-groups-are-character-rigid: that proves character rigidity for elementary groups over subshift algebras, where characters are trivial or regular; here the finitary kernel is a locally finite corner limit with infinitely many characters, and the conclusion is inducing, not rigidity.
  lamplighter-host-elementary-groups-are-character-rigid: that is character rigidity for lamplighter-host elementary groups; this group is not character rigid (it has the countably many zero extensions of Thoma--Skudlarek characters), and the result is a two-piece classification.
artifacts:
  - research/jacobson-el-characters-are-symbol-or-finitary-extensions-proof.md
---

**ESTABLISHED.**

**Setup.**
* `J = F_2<S,T | TS=1>` and `n >= 2`.
* `E = EL_n(J)` acts faithfully on `V = F_2^(N x {1..n})` (finitely supported vectors).
* `L = GL_fin(N x {1..n}, F_2)`, the finitary kernel, is simple and self-centralizing
  (`leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity`, (S1)--(S4)).
* `p : E -> Q = E/L ≅ EL_n(F_2[x,x^(-1)])` is the symbol map.
* `Tr`, `Ch`, and the zero (trivial) extension `e psi` are as in
  `dlv-locally-inner-inducing-character-classification`. Characters are extreme traces.

**Theorem A (character classification).**
1. `L` is a locally inner subgroup of `E`: for each `g in E` and each finitely generated `F <= L` there is
   `h in L` with `g f g^(-1) = h f h^(-1)` for all `f in F`.
2. `L` is inducing in `E`: every character `phi` of `E` with `phi|_L` not identically `1` vanishes on `E \ L`.
3. Consequently every character of `E` is exactly one of the following:

```text
(A1)  phi = sigma o p        with sigma in Ch(Q)              (phi|_L == 1),
(A2)  phi = e psi            with psi in Ch(L) \ {1_L}         (phi = 0 off L),
```

Every function of either form is a character of `E`, and the two parametrizations are injective. In the ICC
case the characteristic function of `L` appears as `delta^Q_e o p` in (A1).

**Corollary B (traces, and the high-rank limit).** Let `tau` be any trace of `E`. The limit

```text
lambda_tau = lim_(m -> oo) tau(w)    over w in L with rank(w - 1) = m                  (B1)
```

exists uniformly in `w` and lies in `[0,1]`. Moreover `tau = lambda_tau (sigma o p) + (1 - lambda_tau) e psi` for
some `sigma in Tr(Q)` and `psi in Tr(L)`. In particular

```text
|tau(g)| <= lambda_tau      for every g in E \ L.                                      (B2)
```

So a trace that is asymptotically regular on high-rank finitary elements (`lambda_tau = 0`) vanishes off `L`.
A trace that keeps weight `c` on some symbol-nontrivial element, such as `x_12(S)` or a constant `x_12(1)`, keeps
weight at least `c` on every high-rank finitary element.

**Corollary C (the CE form of the hole).** Let `S_CE` be the set of `psi in Ch(L) \ {1_L}` such that `e psi`
is CE. Then:
* Every CE character of `E` is either a symbol character (A1) or `e psi` with `psi in S_CE`.
* In particular, microstates for a CE character that is nontrivial on `L` have `tr U_g -> 0` for every
  `g in E \ L`. This sharpens alternative (b) of `(JH1)`.
* `delta^L_e` is a character of `L` (since `L` is ICC), and `e delta^L_e = delta^E_e`.
* The following are equivalent:

```text
E is hyperlinear   <=>   S_CE is nonempty   <=>   delta^L_e in S_CE.                   (C1)
```

* `E` is ICC.

**Corollary D (countability).**
* `L ≅ GL(∞,2)`, so the non-symbol part `Ch(E) \ p^*Ch(Q)` is in bijection with `Ch(GL(∞,2)) \ {1}`.
* That set is countable by Thoma--Skudlarek, as quoted in Gorin--Kerov--Vershik.
* So the hyperlinearity of `EL_20(J)`, the last hole of `agent-leavitt-not-bcs-negative-root-corner`, is
  decided by countably many explicit test functions `e psi`.
* The zero extensions of the rank characters `2^(-k rank(g-1))` are the Haar fixed-point characters `phi_k`
  of `(JH2)`.

**What this does not give.** It does not decide whether any `e psi` is CE. For `psi != 1_L`, `pi_psi(L)''` is
the hyperfinite `II_1` factor (see the proof, Remark R). The GNS algebra of `e psi` is generated by it and by
unitaries `u_g`, `g notin L`, that are orthogonal to it. The algebra is therefore a cocycle crossed product
of `R` by the residually finite group `Q`. The open step is the Connes embeddability of that one cocycle
crossed product, the setting of `finitary-extension-ce-iff-action-lifts-to-normalizer`.

Proof: [[jacobson-el-characters-are-symbol-or-finitary-extensions-proof]].
