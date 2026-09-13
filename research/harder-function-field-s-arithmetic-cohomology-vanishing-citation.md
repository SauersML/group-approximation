---
rg: 2
id: harder-function-field-s-arithmetic-cohomology-vanishing-citation
kind: route
title: Harder, Invent. Math. 42 (1977), Hauptresultat of the Einleitung
target: harder-function-field-s-arithmetic-cohomology-vanishing
requires: []
---

Read from the Springer PDF (doi:10.1007/BF01389786), fetched to MSI on 2026-09-13; pages 135--136
read as images.

Setting, p. 135, verbatim:

> Sei K/F_q ein Funktionenkörper vom Transzendenzgrad 1 über dem endlichen Körper F_q. Sei S eine
> nicht leere, endliche Menge von Stellen des Körpers K. Sei O=O_S der Ring derjenigen Elemente aus
> K, die außerhalb von S ganz sind.
> Sei G_0/F_q eine einfach zusammenhängende, einfache Chevalley Gruppe. Sei G/K ihre Erweiterung
> auf K, d.h. G/K = G_0 × Spec(K). Sei Γ eine Kongruenzuntergruppe der Gruppe G_0(O) der O-wertigen
> Punkte von G_0/F_q. Dann lautet das Hauptresultat

p. 136, verbatim:

> **Satz.** 1. Die rationalen Kohomologiegruppen H^ν(Γ,Q) verschwinden für ν≠0, r|S|, wobei
> r = Rang G_0 und |S| die Anzahl der Elemente in S ist.
> 2. Ist d = r·|S| so ist die Dimension von H^d(Γ,Q) endlich und gleich der Multiplizität der
> speziellen Darstellung π_sp = ⊗_(v∈S) π_(v,sp) von ∏_(v∈S) G(K_v) im diskreten Spektrum von
> L^2(∏_(v∈S) G(K_v)/Γ).
> Dabei ist π_(v,sp) jeweils die spezielle Darstellung von G(K_v) (vgl. [9] und [2]).

Further context from p. 136: Harder states that his proof follows Borel's argument for
`S`-arithmetic groups in the number-field case very closely. `Γ` acts on the product `X` of the
Bruhat--Tits buildings `X_v`, `v ∈ S`, and the cohomology of `Γ` is that of `X/Γ`. Casselman's
results [9] force every irreducible summand of the relevant space of harmonic forms to be of type
`π_sp` or trivial.

Application at `SL_3`: `G_0 = SL_3` is simply connected, simple and split, with `r = 2`. For
`K = F_q(t)` and `S = {0,∞}` one has `O_S = F_q[t,1/t]`, and the principal congruence subgroups
`ker(SL_3(O_S) -> SL_3(O_S/(f)))` are congruence subgroups. For `S = {∞}`, `O_S = F_q[t]`.
