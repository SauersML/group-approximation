---
rg: 2
id: rel-hyperbolic-hosts-make-witness-powers-host-inner
kind: claim
title: If a witness kernel embeds non-parabolically in a relatively hyperbolic group H, then H is not MF; a relatively hyperbolic witness kernel has finite outer order, and hyperbolic-kernel witnesses exist exactly when a sofic torsion-free hyperbolic Kazhdan group has full MF radical
distinct_from:
  finite-outer-order-radical-witnesses-cross-alekseev-thom: that splits witnesses by the outer order of phi and treats the finite-order side; this proves that the order is finite for every relatively hyperbolic kernel, and that on the infinite-order side any relatively hyperbolic host of the kernel contains a finite-index subgroup of the witness.
  lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic: that proves that a lacunary hyperbolic witness kernel is hyperbolic and finitely presented, which puts it in region (AT); this proves that such a kernel also has finite outer order and full MF radical, so the witness is virtually the product K x Z.
  non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group: that turns a non-MF torsion-free hyperbolic group into a hyperbolic full-radical Kazhdan quotient; this produces the non-MF hyperbolic group from any witness whose kernel embeds in a hyperbolic group.
  ollivier-wise-z-torus-kernel-not-finitely-presented: that exhibits Kazhdan kernels inside hyperbolic tori of infinite outer order; this proves that any such kernel forces its hyperbolic host to be non-MF, and that the host is then a Rips-type torus up to finite index.
  hyperbolic-compression-centralizer-rigidity: that kills compression witnesses inside hyperbolic groups by centralizer rigidity; this concerns the automorphism of a mapping torus and uses finiteness of homomorphisms from FA groups.
artifacts:
  - research/rel-hyperbolic-hosts-make-witness-powers-host-inner-proof.md
  - research/fa-groups-finitely-many-homs-to-rel-hyperbolic-groups.md
  - research/finite-outer-order-radical-witnesses-cross-alekseev-thom.md
  - research/sofic-tf-hyperbolic-kazhdan-group-with-full-mf-radical.md
---

**ESTABLISHED** through `rel-hyperbolic-hosts-make-witness-powers-host-inner-proof`.

A **witness** is a pair `(G, K)` as in `finite-outer-order-radical-witnesses-cross-alekseev-thom`,
that is, satisfying (TFZ1) of `torsion-free-sofic-exact-mf-radical-over-z`. Write
`G = K ⋊_φ Z`, with `φ` the conjugation by a lift `t` of `1`.

A **relatively hyperbolic group** is taken with the Drutu--Sapir standing assumptions. It is
infinite, finitely generated, and relatively hyperbolic with respect to finitely many finitely
generated peripheral subgroups, none equal to the whole group. A word-hyperbolic group counts, with
peripheral subgroup `{1}`. A subgroup is **parabolic** if it lies in a conjugate of a peripheral
subgroup; for a hyperbolic group this means it is trivial.

## Theorem (host-inner powers)

Let `(G, K)` be a witness. Let `H` be relatively hyperbolic and `ψ : K → H` injective with
`ψ(K)` not parabolic. Then there are `m ≥ 1` and `h ∈ H` with

```text
ψ(φ^m(k)) = h ψ(k) h^(-1)      for all k in K.                     (HI)
```

Exactly one of the following holds.

- **(A)** Some `h^j` with `j ≠ 0` lies in `ψ(K)`. Then `[φ]` has finite order in `Out(K)`. So `G` is
  virtually the product witness `(K × Z, K)`, `K` is finitely presented, and `Rad_MF(K) = K`.
- **(B)** No `h^j` with `j ≠ 0` lies in `ψ(K)`. Then `(k, j) ↦ ψ(k) h^j` embeds
  `K ⋊_(φ^m) Z` in `H`. That group is isomorphic to the index-`m` subgroup `K ⋊ <t^m>` of `G`.

**In both cases `H` is not MF.**

## Corollaries

1. **(Relatively hyperbolic kernels.)** If `K` is itself relatively hyperbolic, then `[φ]` has
   finite order in `Out(K)`. Hence the witness is virtually `(K × Z, K)`, `K` is finitely presented,
   and `Rad_MF(K) = K`. This includes every word-hyperbolic `K`. So region (IO) of FO-AT contains no
   relatively hyperbolic kernel, and neither does the sub-case (IO-ext) with `K` MF.
2. **(Hyperbolic-kernel equivalence; closes the w16 "Not done" item.)** A witness with a
   word-hyperbolic kernel exists **if and only if** `sofic-tf-hyperbolic-kazhdan-group-with-full-mf-radical`
   holds. By part 3 of `lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic`, a witness whose
   kernel is quasi-isometric to a lacunary hyperbolic group has a word-hyperbolic kernel. So such a
   witness also exists only if that claim holds.
3. **(Hyperbolic hosts.)** If a witness kernel embeds in some word-hyperbolic group `H`, then `H` is
   a non-MF hyperbolic group, which settles `non-mf-hyperbolic-group`. If `H` is also torsion-free,
   then (H1) of `sofic-tf-hyperbolic-kazhdan-group-with-full-mf-radical` holds. With
   `non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group`, one of the following follows:
   - a witness with a hyperbolic kernel exists (the product `Q × Z`);
   - some torsion-free hyperbolic Kazhdan group is not sofic (`nonsofic-hyperbolic-group`).
4. **(MF kernels.)** An MF witness kernel (case IO-ext) embeds non-parabolically in no MF
   relatively hyperbolic group, and is not itself relatively hyperbolic.

## What this kills

- **Named invariant.** The class of `[φ]` in `Out_H(ψK) = N_H(ψK) / ψ(K) C_H(ψK)`, which is the part
  of `Out(K)` realized inside the host.
- **Where every member dies.** Drutu--Sapir finiteness (Corollary 4.37, applied to the FA group `K`)
  makes a power of `φ` host-inner. After that, either:
  - the power is inner in `K`, which puts the witness in the Alekseev--Thom product region; or
  - the index-`m` torus sits inside the host, and the host inherits non-MF.
- **What dies.**
  - Every (IO) design with a relatively hyperbolic kernel. Before this node, (IO) was the only region
    free of Alekseev--Thom 6.1.
  - Every design whose kernel is built inside a hyperbolic group, unless one accepts a non-MF
    hyperbolic group: such a design solves `non-mf-hyperbolic-group`, which is at least as hard as
    Gromov's residual-finiteness question.
  - Every design whose kernel is built inside an MF relatively hyperbolic group, outright.

## Not claimed

- No witness is constructed, and the flagship stays OPEN.
- Nothing is said about kernels that are only acylindrically hyperbolic, or about hosts that are
  only acylindrically hyperbolic. Drutu--Sapir finiteness is not available there.
