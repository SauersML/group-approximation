---
rg: 2
id: euler-ring-rational-symbols-are-infinitely-generated
kind: claim
title: The symbols {u+1, u+1+ql} of the Euler ring D, for primes q != l, are independent in K_2(D), so E_N(D), E_N(T_l) and E_N(R_l) are not finitely presented and K_2(N, T_l) is not finitely generated
distinct_from:
  resolvent-ring-corner-symbols-survive-in-k2: that obstruction comes from the Z_(l) corner of R_l and its tame symbols; this one comes from the Euler ring D itself, through symbols of its lamp units, so it also reaches rings with no Z_(l) corner such as T_l.
  euler-triangular-ring-has-fg-central-unstable-k2: that is the open claim that K_2(N, T_l) is finitely generated and central; this refutes it.
  infinitely-generated-symbols-block-fp-elementary-groups: that is the general lemma; this supplies the infinitely generated symbols for D and every ring retracting onto it.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**ESTABLISHED (2026-09-18)** through `euler-ring-rational-symbols-are-infinitely-generated-proof`. Lane proof (gq-k2-q),
not independently reviewed. Inputs:
- `abc-twisted-laurent-k-theory-fibration`, Ara–Brustenga–Cortiñas Theorem 3.6 and Lemma 7.2, read at the source
  there;
- `infinitely-generated-symbols-block-fp-elementary-groups`;
- textbook facts: the tame symbol; regular local rings are UFDs; additivity of lengths.

In place of the Gersten/Kato complex, the proof uses an elementary two-dimensional reciprocity lemma, proved in the
route.

## Setting

As in `resolvent-ring-has-path-normal-form`:
- `A = Z[u][π_k^(-1) : k ∈ Z] ⊂ Q(u)` with `π_k = u + 1 + kl`;
- `σ(u) = u + l`, so `σ(π_k) = π_(k+1)`;
- `D = A[x^(±1); σ]`;
- `T_l = [[D, M],[0, Z]]` is the ring of `euler-triangular-ring-is-fp-rf`.

For `d ∈ Z ∖ {0}` put `c_d = {π_0, π_d} ∈ K_2(A)`, a Steinberg symbol of two commuting units.

## Statement

1. **An invariant.** For a prime `p ≠ l`, let `I_p(z) = Σ_k k·v_p(∂_k z)` for `z ∈ K_2(A)`, where `∂_k` is the tame
   symbol of `Q(u)` at `π_k`, with values in `Q^x`. Then `I_p` is a homomorphism `K_2(A) -> Z` with `I_p ∘ σ = I_p`.
2. **Values.** `I_p(c_d) = d·v_p(d)`. In particular, for primes `q, p ≠ l`, `I_p(c_q) = q` if `p = q` and `0`
   otherwise.
3. **Independence.** The classes of `c_q`, `q ≠ l` prime, in `coker(1 − σ_* : K_2(A) -> K_2(A))` generate a free
   abelian group of infinite rank. So do their images in `K_2(D)`, and in `K_2(T_l)` and `K_2(R_l)`, both of which
   retract onto `D`.
4. **Consequences.** For every prime `l` and every `N >= 3`:
   - `E_N(D)`, `E_N(T_l)` and `E_N(R_l)` are not finitely presented, by the symbol lemma applied to the commuting
     units `π_0, π_q`;
   - `K_2(N, T_l)` is not finitely generated. This refutes `euler-triangular-ring-has-fg-central-unstable-k2`, and
     with it the route `euler-triangular-residual-fng-from-fg-central-k2`.

## What is not claimed

Whether the finite residual of `St_N(T_l)` is finitely normally generated (`euler-triangular-steinberg-rf-residual-is-fng`)
is not decided here. It depends on whether the `c_q` die in every finite quotient of `T_l`, which is the
finite-quotient half, taken by `gq-infinite-primes`.

The heuristic (T2) of the refuted node assumed that the residues of `K_2(A)` land in `⊕_k K_1(Z) = ⊕_k Z/2`. They
land in `⊕_k K_1(Q) = ⊕_k Q^x`, because the lines `π_k = 0` are not pairwise comaximal: they meet over the primes
dividing `(k−j)l`.
