---
rg: 2
id: finite-block-coordinates-share-one-mf-image
kind: claim
title: Every coordinate of the finite block has one common image in every MF representation
distinct_from:
  hilbert-hotel-prescribed-mf-reflection: that realizes a prescribed MF quotient by a direct product; this is about the internal structure of one finite-block HNN extension and says nothing about prescribing a quotient.
  finite-block-mf-quotient-is-abelianized-amalgam: that computes the entire MF quotient under residual finiteness of V; the coordinate identification here needs no MF or residual-finiteness assumption on V.
artifacts:
  - non_mf_groups_exist.tex
---

Let `Gamma` be finitely presented with property (T), let `alpha : Gamma ->
Gamma` be injective of finite index `m > 1`, and let `V` be the ascending
HNN extension of `Gamma` along `alpha`.  For a **finite group `K`** put

```text
Omega = Gamma / alpha(Gamma),   F = K^Omega,   Lambda = F x| Gamma,
E_K   = < Lambda, t | t g t^(-1) = alpha(g), g in Gamma >.
```

Then for every homomorphism `rho` from `E_K` to an MF group,

```text
rho(k_omega) = rho(k_(alpha(Gamma)))      for every omega in Omega, k in K.
```

**No hypothesis on `K` beyond finiteness.**  Perfection is used only
afterwards, to turn "the common image is abelian" into "it is trivial".

## Two corollaries in opposite directions

**Perfect `K`.**  Distinct coordinates commute, so the common image is an
abelian image of `K`, hence trivial. Thus every MF map kills the normal
closure `B_K` of `F`. If `V` is additionally MF, the quotient `E_K/B_K=V`
separates everything outside `B_K`, giving `Rad_MF(E_K)=B_K`.
The manuscript assumes the stronger condition that `V` is residually
finite. Without that extra input the general formula is
`Rad_MF(E_K)=q^(-1)(Rad_MF(V))` for the quotient map `q:E_K->V`.

**`K = C_2`.**  The identification survives but nothing kills it, and
`z_omega z_(omega')` is a nontrivial element of `C_2^Omega` for
`omega != omega'`.  Hence

```text
Rad_MF(E_(C_2)) != 1.
```

## Why this matters

It closes a proposed replacement of the perfect-block construction by a
**finite Clifford block** — a finite group in which distinct coordinates
commute up to a central involution `z`.  That block makes the compression
defect visible (`[t c t^(-1), a]^2 = z`), so the criterion applies directly
and the finite-dimensional transport theorem looks removable.  The hope was
that the resulting group `G` would have `Rad_MF(G) = <z> ~= Z/2` exactly,
a sharper radical theorem than the current one, because `G/<z>` is exactly
`E_(C_2)`.

The corollary above refutes that: `Rad_MF(E_(C_2)) != 1`, so the Clifford
group's radical is strictly larger than `<z>`. This refutes that proposed
formula; it does not rule out computing a different exact radical.

**The finite-dimensional transport theorem is used in this argument**:
it proves the identification and excludes the proposed radical `<z>`.
This does not prove that no alternative construction or proof is possible.
