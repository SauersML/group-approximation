---
rg: 2
id: stw10-matrix-core-models-are-corner-amplifications
kind: claim
title: A u.c.p. model exact on a full matrix core is precisely an amplified corner model
distinct_from:
  stw10-qd-traces-admit-exact-finite-dimensional-core-models: that perturbs quasidiagonal trace models so a finite-dimensional core lies in the multiplicative domain; this classifies every resulting full-matrix-core model and gives exact coordinate defect formulas.
  stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses: that localizes a possible negative answer in a finitely generated weakly dense algebra; this removes all choices in the finite CAR-stage action and transfers its remaining norm obstruction to one matrix corner.
  stw08-exactness-coherifies-qd-models: that open claim seeks connecting homomorphisms between distinct finite-dimensional models; this is a one-model algebraic factorization and supplies no inter-model coherence.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `A` be a unital C-star algebra containing a unital copy
`D isomorphic to M_d`, with matrix units `(e_ij)`, and put

```text
p=e_11,                         B=pAp.
```

There is a canonical unital star isomorphism

```text
Phi:A -> M_d(B),                Phi(a)_ij=e_1i a e_j1,
Phi^(-1)([b_ij])=sum_(i,j) e_i1 b_ij e_1j.                 (MC1)
```

It carries `D` to `M_d tensor 1_B`.  If `psi:A -> M_k` is u.c.p. and
`D subset MD(psi)`, then `k=dm` for some `m`; after conjugating by a unitary
in `M_k`, there is a unique u.c.p. map `chi:B -> M_m` such that

```text
psi o Phi^(-1) = id_(M_d) tensor chi.                       (MC2)
```

Conversely every u.c.p. `chi` defines in this way a u.c.p. map with `D` in
its multiplicative domain.

The reduction preserves the finite-model data with explicit constants.  If
`Phi(x)=[b_ij]` and `Phi(y)=[c_ij]`, then the `(i,j)` block of the
multiplicative defect of `psi` is exactly

```text
sum_(ell=1)^d (chi(b_iell c_ellj)-chi(b_iell)chi(c_ellj)).  (MC3)
```

Thus coordinatewise corner defects at most `eta` give ambient defect at
most `d^2 eta`.  This is only a convenient bound; `(MC3)` is the exact
translation.

For a tracial state `tau` on `A`, define the normalized corner trace

```text
tau_B=d tau|B.
```

Then `tau=tr_d tensor tau_B` under `(MC1)`, and

```text
tr_(dm)(psi(x))-tau(x)
 = (1/d) sum_i (tr_m(chi(b_ii))-tau_B(b_ii)).               (MC4)
```

In the reverse direction the diagonal embedding

```text
iota:B -> A,             iota(b)=sum_i e_i1 b e_1i
```

satisfies `Phi(iota(b))=1_d tensor b`.  Hence multiplication and trace
defects of `chi` on a corner packet are exactly those of `psi` on its
`iota`-image, with no normalization loss.

Apply this to a CAR stage `D_n isomorphic to M_d` in `R`.  Together with
`stw10-qd-traces-admit-exact-finite-dimensional-core-models`, Problem X(2)
is equivalent to the following corner normal form.  For every `n`, finite
`X subset R`, and `epsilon>0`, there are `m` and a u.c.p.

```text
chi:p_n R p_n -> M_m
```

whose corner-coordinate defects in `(MC3)` and diagonal trace discrepancy
in `(MC4)` have absolute value below `epsilon`.  A convenient sufficient
condition is to make all pairwise defects on the finite coordinate packet
`{e_1i x e_j1:x in X, 1<=i,j<=d}` smaller than `epsilon/d^2`, and all its
diagonal trace errors smaller than `epsilon`.  The associated ambient model
has forced size `dm` and is exactly `id_(M_d) tensor chi`; there is no
remaining approximation or compatibility problem on the CAR stage itself.
