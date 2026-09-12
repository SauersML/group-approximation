---
rg: 2
id: twisted-edge-over-amalgamated-product-base-is-mf
kind: claim
title: The graph edge over a base of the form Gamma amalgamated with S times Q is MF under relative profinite compatibility
distinct_from:
  twisted-rope-edge-is-mf-under-relative-profinite-compatibility: that requires the base to be the full product `Gamma x Q`; this only attaches `Q` along the edge subgroup `S`, which is the shape produced by a compiler in which the embedded group commutes with the edge subgroup and nothing else.
---

ESTABLISHED.  Let `Gamma` be a countable MF group, `S <= Gamma`, `Q` a
countable residually finite group, `tau : S -> Q` a homomorphism, and

```text
B = Gamma *_S (S x Q),
R = < B, u | u (s,1) u^-1 = (s, tau(s)),  s in S >.                   (AE1)
```

Suppose `Gamma` has a decreasing sequence of finite-index normal subgroups
`Gamma_k` with (i) `intersection_k S Gamma_k = S` and (ii) for every
finite-index normal `Q' <= Q` some `k` has `tau(S cap Gamma_k) <= Q'`.  Then
`R` is operator-MF.

## Proof

The proof of [[twisted-rope-edge-is-mf-under-relative-profinite-compatibility]]
goes through with two changes.

*Finite quotients of the base.*  Take a filtration `Q_k` of `Q` with `tau(S
cap Gamma_k) <= Q_k` and put `Sbar_k = S Gamma_k / Gamma_k`.  The map `S x
Q -> Sbar_k x Q/Q_k` and `Gamma -> Gamma/Gamma_k` agree on `S`, so they
induce `B -> B_k := (Gamma/Gamma_k) *_(Sbar_k) (Sbar_k x Q/Q_k)`, an amalgam
of finite groups, hence virtually free.  The images `C_1 = Sbar_k x 1` and
`C_2 = graph(taubar_k)` are finite, `taubar_k` is well defined by `(ii)`,
and `D_k = < B_k, u | u(sbar,1)u^-1 = (sbar, taubar_k sbar) >` is an HNN
extension of a virtually free group over finite subgroups, hence virtually
free and residually finite.

*Reducedness.*  An element `a in B` outside `S x Q` has a reduced amalgam
form containing a letter of `Gamma \ S`; by `(i)` that letter stays outside
`Sbar_k` for large `k`, so the image of `a` is a reduced word of length at
least two in `B_k` and lies in no factor, in particular not in `C_1` or
`C_2`.  An element `(s,q) in S x Q` outside `C_1` (resp. `C_2`) has `q != 1`
(resp. `q != tau(s)`), and its image leaves `C_1` (resp. `C_2`) once `q`
(resp. `q tau(s)^-1`) leaves `Q_k`.  Hence Britton-reduced words of `R`
stay Britton-reduced in `D_k` for large `k`; likewise reduced amalgam words
of `B` with a `Q`-letter stay reduced in `B_k`.

*Assembly.*  `p : R -> Gamma` (kill `Q` and `u`) is a retraction; elements
with `p(r) != 1` are separated by the MF embedding of `Gamma`, and elements
with `p(r) = 1`, `r != 1`, are either reduced amalgam words of `B`
containing a `Q`-letter or Britton-reduced words containing `u`, both
nontrivial in `D_k` for large `k`.  The tensor construction `(U_k(p r) (+)
1) (x) lambda_k(pi_k rho_k r)` of the product case then embeds `R` in the
norm matrix corona.
