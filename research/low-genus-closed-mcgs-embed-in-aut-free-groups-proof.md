---
rg: 2
id: low-genus-closed-mcgs-embed-in-aut-free-groups-proof
kind: route
title: Genus one is virtually free, and genus two is commensurable with the six-punctured sphere
target: low-genus-closed-mcgs-embed-in-aut-free-groups
requires:
  - aut-free-embeddability-passes-to-finite-index-overgroups
  - virtually-free-groups-embed-in-aut-free-groups
  - punctured-surface-mcgs-virtually-embed-in-aut-free-groups
---

By item 2 of `aut-free-embeddability-passes-to-finite-index-overgroups` it is
enough to embed some finite-index subgroup of `MCG(S_g)` in some `Aut(F_k)`: that
covers `MCG(S_g)` and the extended group, which contains it with index 2. Item 3
there then gives an `Out` host.

- **g = 0.** `MCG(S^2) = 1`.
- **g = 1.** `MCG(T^2) ≅ SL_2(Z)` (standard), finitely generated and virtually
  free; use `virtually-free-groups-embed-in-aut-free-groups`.
- **g = 2.**
  1. The hyperelliptic involution `ι` is central in `MCG(S_2)`, and
     `MCG(S_2)/⟨ι⟩ ≅ MCG(S_{0,6})`, the mapping class group of the sphere with six
     punctures (Birman--Hilden; standard, theorem number not re-read).
  2. `MCG(S_2)` is residually finite (Grossman 1974), so some finite-index
     `L ≤ MCG(S_2)` does not contain `ι`, and `L` maps injectively into
     `MCG(S_{0,6})`.
  3. `S_{0,6}` has punctures, so by
     `punctured-surface-mcgs-virtually-embed-in-aut-free-groups` some finite-index
     `M ≤ MCG(S_{0,6})` embeds in some `Aut(F_k)`.
  4. The preimage in `L` of `M ∩ image(L)` has finite index in `MCG(S_2)` and
     embeds in `Aut(F_k)`.

This mirrors the genus-two step of Belk--Fournier-Facio--Hyde--Zaremsky,
arXiv:2503.21882v2, Section 4 ("MCG(Σ) is commensurable to MCG(Σ′)" with `Σ′` the
six-punctured sphere), used there for the Boone--Higman property.
