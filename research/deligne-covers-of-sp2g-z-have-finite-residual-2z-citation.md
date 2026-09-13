---
rg: 2
id: deligne-covers-of-sp2g-z-have-finite-residual-2z-citation
kind: route
title: Import Deligne's finite-residual theorem for the finite symplectic covers from Stover's survey, Theorem 1.5
target: deligne-covers-of-sp2g-z-have-finite-residual-2z
requires: []
---

Citation import. On 2026-09-13 the PDF of arXiv:2407.07680v2 (24 Jan 2025) was
fetched on MSI into `/scratch.global/sauer354/ex/ex-nh-deligne-hs/stover.pdf` and
pages 1--4 were read. M. Stover, *Residual finiteness and discrete subgroups of
Lie groups*.

Verbatim, p. 3.

> "The symplectic group Sp_2g(R) < SL_2g(R) is homotopy equivalent to the unitary
> group U(g), which has fundamental group Z. Thus Sp_2g(R) has a connected n-fold
> cyclic cover for all n ∈ N; these covers are all nonlinear real Lie groups."

> "**Theorem 1.5** (Deligne [8]). Let Γ = Sp_2g(Z) and G_n → Sp_2g(R) be the
> unique finite, connected cover of degree n. If g ≥ 2 and n ≥ 3, then the
> preimage Γ_n of Γ in G_n is a Z/n central extension of Γ that is not residually
> finite."

> "In fact, Deligne gives a precise measure of the failure of residual
> finiteness. If Z ≅ Z/n ⊴ Γ_n is the center, then the intersection of the
> kernels of all homomorphisms from Γ_n onto finite groups is 2Z."

In the last sentence `Z` denotes the covering kernel `Z/n`. The full center of
`Gamma_n` is the preimage of `{+I, -I}` and has order `2n`. The kernel reading
is forced: `Sp_(2g)(Z)` is residually finite, so every element outside the kernel
survives in a finite quotient. Reference [8] is P. Deligne, *Extensions centrales
non résiduellement finies de groupes arithmétiques*, C. R. Acad. Sci. Paris Sér.
A-B 287 (1978), A203--A208.

Used at statement level.
