---
rg: 2
id: deligne-central-regular-trace-classification-proof
kind: route
title: Apply character rigidity for non-uniform higher-rank lattices with arbitrary center
target: deligne-maslov-sector-traces-are-central-regular
requires:
  - deligne-triple-cover-fd-central-invisibility
artifacts:
  - research/artifacts/deligne-maslov-character-rigidity-and-psd-cone-fence-2026-08-21.md
---

The connected three-fold cover of `Sp_4(R)` is a connected semisimple Lie
group of real rank two, without compact factors.  Its inverse image `E_3` of
`Sp_4(Z)` is an irreducible non-uniform lattice.  Dogon--Glasner--Gorfine--
Hanany--Levit, *Non-uniform higher-rank lattices are character rigid*,
arXiv:2507.21862, Theorem 1.5, applies to lattices in connected semisimple Lie
groups with arbitrary center.  It says that every extreme trace of `E_3` is
either finite-dimensional or induced from the center.

The center of the connected cover maps into the center `{+I,-I}` of
`Sp_4(R)`.  Conversely every lift of a central element is central: its
commutator with the connected covering group is a continuous map into the
discrete covering kernel and is therefore constant.  Hence

```text
Z(E_3) = preimage({+I,-I})
```

has order six.  Its order-three subgroup is `<z>`, so a fixed nontrivial
character of `<z>` has exactly two extensions to `Z(E_3)`.

Let `tau` be a trace on `A_omega`, regarded as a trace on `E_3`.  In its
central decomposition into extreme traces, the equality `z=omega` persists
almost everywhere (apply the components to the positive element
`(z-omega)^*(z-omega)`).  A finite-dimensional component is impossible by
`deligne-triple-cover-fd-central-invisibility`.  Character rigidity therefore
makes almost every component induced from a character of `Z(E_3)`.  Such an
induced trace is exactly `(CR1)`, and only the two extensions of
`z |-> omega` can occur.  Integrating the decomposition proves the claim.

**Source check (2026-09-13, lane ex-nh-deligne-hs).** ArXiv:2507.21862v1 (29 Jul 2025) was read
from the PDF on MSI, pp. 1--3.
- Definition 1.1: "A discrete group Γ is character rigid if every character of Γ is either
  finite-dimensional ... or vanishes outside the center Z(Γ)."
- Theorem 1.5: "Let H be a connected semisimple Lie group with rank_R(H) ≥ 2, no compact factors and
  arbitrary center. Let Γ an irreducible lattice in H. Assume either that Γ is non-uniform or that H
  has a factor with Kazhdan's property (T). Then the lattice Γ is character rigid, and satisfies the
  conclusion of Corollary 1.4."
- The connected triple cover of `Sp_4(R)` and its lattice `E_3` meet every hypothesis. The same
  statement applies verbatim to the connected covers of `Sp_(2g)(R)` for every `g >= 2`.
- Vanishing outside the center is the "induced from the center" form used above.
