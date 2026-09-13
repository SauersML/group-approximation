---
rg: 2
id: jacobson-one-sided-symbol-preimages-are-lef
kind: claim
title: The one-sided symbol preimages in the Jacobson elementary group are LEF and retain the head, but they amalgamate to a proper cover
distinct_from:
  one-sided-raw-qutrit-head-bridges-are-residually-finite: that treats a qutrit head bridge with one raw direction; this is the full preimage of SL_3(F[z]), containing the whole finitary kernel and every polynomial root.
  binary-jacobson-finitary-whitehead-shift-is-marked-lef: that is the finitary head extended by a Whitehead shift; this is a one-sided half of EL_3(J) whose local models are linear over F[S].
  jacobson-literal-column-normalizer-is-lef: that is the two-row column normalizer; this is a symbol preimage of full rank three, and it explains why mixed S- and T-relations are the only possible source of head loss.
  jacobson-amenable-symbol-subgroups-are-amenable: that transfers amenability through the symbol; the halves here have nonamenable symbol image SL_3(F[z]), and they are LEF by a different mechanism.
artifacts:
  - research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md
---

**ESTABLISHED** (route `jacobson-one-sided-symbol-preimages-lef-proof`; artifact Section 3). Independent
re-derivation requested from `w4-vf-gate`.

**Statement.** Let `F` be a finite field, `J_F = F<S,T | TS=1>`, `E_F = EL_3(J_F)` and `π` the symbol map to
`SL_3(F[z,z^(-1)])`, with kernel `L_3`. Put `H_+ = π^(-1) SL_3(F[z])`, `H_- = π^(-1) SL_3(F[z^(-1)])` and
`H_0 = H_+ ∩ H_-`.
1. `H_+ = L_3 x| EL_3(F[S])`, `H_- = L_3 x| EL_3(F[T])` and `H_0 = L_3 x| SL_3(F)`. The transpose-inverse twist by the
   anti-involution `S <-> T` exchanges the two halves, and `E_F = <H_+, H_->`.
2. Every finitely generated subgroup of `H_+` or of `H_-` is residually finite. So both halves are LEF, and hence
   sofic, and the head `x_13(Q) in H_0` survives in their finite models.
3. `E_F` is a proper quotient of `H_+ *_(H_0) H_-`. The word `[x_12(S), x_23(T)]` is reduced in the amalgam, but in
   `E_F` it equals `x_13(1 - Q)`, which lies in `H_0`.

**Consequence for `E = EL_3(J)`.**
* **Mixed relations are required.** A proof that finite models, sofic approximations or rank models of `E` kill the
  head, as in `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`, cannot use only relations that hold inside one
  half. It must use relations mixing `S`-roots with `T`-roots, beginning with the Toeplitz commutator.
* **Soficity attempts.** A soficity proof cannot glue approximations of the halves along `H_0`, because `E` is a proper
  quotient of the amalgam.
