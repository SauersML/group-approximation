---
rg: 2
id: stw63-canonical-free-product-implementers-escape-weakly
kind: claim
title: Canonical free-product implementing unitaries must escape ultraweakly to zero
distinct_from:
  stw63-canonical-free-product-copies-are-aue: that asks whether a point-norm implementing sequence exists in the full free product; this proves the necessary escape behavior of every such sequence and rules out only exact conjugacy.
  stw63-full-tracial-shadow-forbids-joint-z-bridge: that obstructs a common central Jiang--Su copy; this is a direct statement about unitary conjugators for the canonical pair.
  stw63-all-von-neumann-codomains-have-uniqueness: that supplies approximate conjugators in the free-product factor; this proves that every possible choice of those conjugators converges ultraweakly to zero.
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Let

```text
F=Z*_(C)Z,
(M,tau)=(pi_(tau_Z)(Z)'',tau_Z)*(pi_(tau_Z)(Z)'',tau_Z),
theta:F->M,
```

where `theta` is the reduced tracial free-product representation.  Denote
the two von Neumann free factors by `M_0,M_1`, and let
`alpha:M_0->M_1` be the trace-preserving isomorphism induced by the
identification of the two copies of `Z`.

If `(u_n)` is any sequence in `U(M)` satisfying

```text
||u_n theta(i_0(z)) u_n* - theta(i_1(z))|| -> 0       (z in Z),   (WFE1)
```

then

```text
u_n -> 0 ultraweakly in M.                              (WFE2)
```

In particular this conclusion holds for the image under `theta` of every
prospective implementing sequence in `U(F)`.  There is no single unitary in
`M`, and hence none in `F`, which exactly conjugates the two canonical
copies.  Thus any positive solution of the canonical AUE problem must use
unitaries which escape every fixed normal Fourier coefficient in the
reduced free-product shadow.

Quantitatively, for every normal functional `varphi in M_*` and every
`delta>0`, there are a finite set `E subset Z` and `epsilon>0` such that

```text
max_(z in E) ||u theta(i_0(z))u* - theta(i_1(z))|| >= epsilon
```

for every `u in U(M)` with `|varphi(u)|>=delta`.  The same lower bound applies
to images of unitaries from `F`.  The finite test set may depend on the
chosen Fourier coefficient and `delta`; no coefficient-free positive lower
bound is asserted.

This theorem does not decide whether a sequence satisfying `(WFE1)` exists.
Such sequences do exist in `M` by finite-factor Jiang--Su uniqueness; the
theorem determines their unavoidable weak behavior.
