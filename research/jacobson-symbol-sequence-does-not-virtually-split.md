---
rg: 2
id: jacobson-symbol-sequence-does-not-virtually-split
kind: claim
title: The symbol sequence of the binary Jacobson elementary group splits over no finite-index subgroup, because the image layer of any lift of a unipotent elementary matrix carries nonzero Fredholm index for every lift of a commuting diagonal symbol
distinct_from:
  jacobson-symbol-sequence-does-not-split: that uses an odd-order constant and its isotypic idempotent, so it only reaches subgroups with odd torsion and explicitly leaves virtual splitting open (every finite-order element of a congruence subgroup is unipotent); this uses a unipotent involution x_12(a), which every finite-index subgroup contains, and the image layer im(u~+1) in place of an idempotent, so it settles virtual splitting negatively.
  outer-covering-lifts-are-virtual-sections: that is a general equivalence between lifting outer classes and virtual sections of Aut -> Out; this is a specific non-splitting theorem for the Toeplitz symbol extension of EL_n(J).
  birman-sequence-genus-three-does-not-virtually-split: same shape of statement (no virtual section) for a different extension (surface Birman sequence), with a different obstruction.
---

**ESTABLISHED** (route `jacobson-symbol-sequence-does-not-virtually-split-proof`).

**Notation** (as in `jacobson-symbol-sequence-does-not-split`).
- `J = F_2<S,T | TS = 1>` acts on `V_+ = F_2^(N)` by `S e_k = e_(k+1)`, `T e_0 = 0`, `T e_(k+1) = e_k`.
- `A = F_2[z,z^(-1)]`, symbol `pi : S -> z, T -> z^(-1)`; `ker(J -> A)` is the ideal of finite-rank operators.
- `n >= 3`, `E = EL_n(J) = GL_n(J)` acting on `V = V_+^n`, `Q = SL_n(A) = EL_n(A)`.
- Symbol sequence `1 -> L -> E -> Q -> 1`, `L = GL_fin(V)`.
- `u_a = x_12(a)` for `a in A`, and `h = diag(z, z, z^(-2), 1, ..., 1)`.

**Theorem.** For every nonzero `a in A` and every integer `k != 0`, `u_a` and `h^k` commute in `Q`, and

```text
(NVS)  no element u~ in E with symbol u_a commutes with any element h~ in E
       with symbol h^k; that is, [u~, h~] is a nontrivial element of L for
       every choice of lifts.
```

**Corollary (no virtual section).** Let `Gamma <= Q` be any subgroup of finite index. There is no homomorphism
`s : Gamma -> E` with `pi o s = id`. So the preimage `pi^(-1)(Gamma)` is never the semidirect product
`L x| Gamma` compatibly with the symbol map, for any `n >= 3` and any finite-index `Gamma` (no congruence
subgroup property is used).

More generally the sequence splits over no subgroup of `Q` containing a `Q`-conjugate of a commuting pair
`(u_a, h^k)` with `a != 0`, `k != 0`.

**The invariant.** For any lift `u~` of `u_a`, put `t = u~ + 1` (a lift of the square-zero symbol
`u_a + 1 = a E_12`). The image layer `t V` is mapped bijectively onto itself by every invertible operator
commuting with `u~`. And `tV` is commensurable with the first coordinate `V_+ (+) 0 (+) ... (+) 0`, on which the Toeplitz lift
of `h^k` acts as `S^k`, of Fredholm index `-k`. The subspace-relative Fredholm index is invariant under
commensurable change of subspace and finite-rank perturbation, so `0 = -k`.

**Why the odd-torsion obstruction could not see this.** A unipotent involution in characteristic 2 has no
isotypic idempotent (`F_2[C_2]` is local), which is why (G) of `jacobson-symbol-sequence-does-not-split`
says nothing about congruence subgroups. The image layer `im(u~+1)` replaces the idempotent: it is exactly
invariant under the centralizer of `u~`, which is all the index argument needs, and it needs no exact
finite-order lift at all.

**Impact.**
- Closes the "virtual splitting" question left open in `jacobson-symbol-sequence-does-not-split` and named as
  the next falsifiable step on `agent-leavitt-not-bcs-negative-root-corner`.
- Kills, for the hyperlinearity of `EL_20(J)` (equivalently the Toeplitz survivor class of the bounty-56 hole
  `agent-leavitt-not-bcs-negative-root-corner`), every reduction that passes to a finite-index subgroup and
  then treats it as a genuine semidirect product `L x| Gamma`: semidirect-product or wreath-type permanence
  theorems for amenable-by-residually-finite split extensions, and approximations of `E` pulled back along a
  section over a finite-index subgroup.
- **Limits.** The argument uses the Fredholm index on the defining representation, where `L` acts by
  finite-rank perturbations. It says nothing about the von Neumann 2-cocycle `omega` in
  `L(E) = R x|_(alpha,omega) Q` being a coboundary in `U(R)`, nor about decompositions of `pi^(-1)(Gamma)`
  as semidirect products along a normal subgroup other than `L`. Those remain open on the target hole.
