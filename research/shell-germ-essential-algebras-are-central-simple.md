---
rg: 2
id: shell-germ-essential-algebras-are-central-simple
kind: claim
title: For a minimal effective second-countable ample groupoid with compact Hausdorff unit space, the Steinberg algebra modulo its singular ideal is central simple; so every shell envelope sits in the units of a central simple algebra A_nu/J
distinct_from:
  cepss-nonhausdorff-steinberg-simplicity: that imports the criterion for simplicity of A itself, which needs the singular ideal to vanish; this is simplicity of the quotient by the singular ideal, which needs only minimality and effectiveness, plus triviality of its centre.
  shell-germ-steinberg-algebras-are-never-simple: that shows the singular ideal J of a shell envelope is nonzero and that the envelope survives in (A/J)^x; this shows A/J is central simple.
  germ-steinberg-algebras-over-v-are-fg-central-simple: that proves central simplicity of A under Hausdorffness or the CEPSS condition, neither of which holds for shell envelopes; this proves it for A/J with no such condition.
---

**ESTABLISHED.** Simplicity is an import, and a direct proof is included. The centre
computation is a lane proof, elementary and not reviewed. No priority claimed.

## Statement

Let `G` be a second-countable ample groupoid whose unit space `G^(0)` is compact Hausdorff,
let `K` be a field, `A = A_K(G)`, and let `J` be the singular ideal: the `f ∈ A` whose support
has empty interior (CEPSS `prp:singular empty int`, l.602; it is an ideal by
`prop:singularideal`, l.612). If `G` is minimal and effective, then:

1. `A/J` is simple;
2. its centre is `K`.

**Shell envelopes.** Let `G_nu` be the germ groupoid of a shell envelope `E_nu`. It is second
countable, ample, and has unit space `C`. It is minimal, since `V <= E_nu`, and effective, as
a germ groupoid. So `A_nu/J` is a central simple `K`-algebra. By
`shell-germ-steinberg-algebras-are-never-simple` (item 4), `E_nu` embeds in `(A_nu/J)^x`.
This supplies the central simple algebra that step 3 of
`boone-higman-via-germ-steinberg-algebra-presentation` needs, with `A` replaced by `A/J`.

## Source for 1

CEPSS, arXiv:1806.04362, e-print `CEPSS_revision_Mar07_2019.tex` (read on MSI on
2026-09-18). The remark after `thm:simple` (l.838–849) says the following. Suppose `G` is
second countable, ample, effective and minimal. Then Nekrashevych's Proposition 4.1 (IJAC 26
(2016), 375–397) makes `A/I` simple, where `I` consists of the functions vanishing on germs
whose source has trivial isotropy. And `I = S_K(G)`: "So `A_K(G)/S_K(G)` is a quotient of
`A_K(G)/I`", and it is nonzero. Nekrashevych's paper itself was not read. So here is a
direct proof.

## Proof of 1

Let `f ∈ A ∖ J`, `f = Σ_i c_i 1_(B_i)` with compact open bisections `B_i`.
- **A constant patch.** `supp f` has nonempty interior, so it contains a nonempty compact
  open bisection `W`. `W` is Hausdorff and each `B_i ∩ W` is open in it. For each `i`, shrink
  `W` to a compact open bisection inside `B_i ∩ W` if that is nonempty, and leave it otherwise.
  At the end, `W ⊆ B_i` or `W ∩ B_i = ∅` for every `i`. So `f` is constant on `W`, with value
  `c ≠ 0`.
- **Move it to units.** `h = f 1_(W^(-1))` satisfies `h(x) = f(w) = c` at every unit
  `x = r(w)`, `w ∈ W`.
- **Isolate a unit.** By CEPSS `lem:CEP1` (l.675), the units `u` with `G_u^u ⊆ int(Iso(G))`
  are dense. Effectiveness gives `int(Iso(G)) = G^(0)`, so some `x ∈ r(W)` has trivial
  isotropy. Write `h = Σ_j d_j 1_(D_j)`. There are three cases for each `j`:
  - `x ∉ s(D_j)`. Then `x` has a neighborhood disjoint from the compact set `s(D_j)`.
  - `x ∈ D_j`. `D_j ∩ G^(0)` is open, so `D_j` consists of units over a neighborhood of `x`.
  - `x ∈ s(D_j)` and `D_j x ≠ x`. Then `r(D_j x) ≠ x`, so some neighborhood `V` of `x` has
    `r(D_j V) ∩ V = ∅`.

  Take a compact open `V ∋ x` inside all these neighborhoods and inside `r(W)`. Then
  `1_V h 1_V = (Σ_(j: x ∈ D_j) d_j) 1_V = h(x) 1_V = c 1_V`. So `1_V ∈ (f)`.
- **Minimality.** As in the proof of CEPSS `thm:simple`, conjugating `1_V` by compact open
  bisections gives `1_L ∈ (f)` for every compact open `L ⊆ G^(0)`. Hence `1 ∈ (f)`.

So every ideal strictly containing `J` is `A`. Also `1 ∉ J`, since `supp 1 = G^(0)` is open.

## Proof of 2

Let `z ∈ A` with `[z, a] ∈ J` for all `a ∈ A`. Let `O` be the interior of `supp z`.
- **`O ⊆ G^(0)`.** Suppose `γ ∈ O` with `r(γ) ≠ s(γ)`. Take a compact open `U ⊆ G^(0)` with
  `s(γ) ∈ U` and `r(γ) ∉ U`. Then `[z, 1_U](η) = z(η)(1_U(s η) - 1_U(r η))`, which equals
  `z(η)` on the open set `O ∩ s^(-1)(U) ∩ r^(-1)(G^(0) ∖ U) ∋ γ`. So `[z, 1_U] ∉ J`, a
  contradiction. Hence `O ⊆ Iso(G)`. Since `O` is open, `O ⊆ int(Iso(G)) = G^(0)`.
- **`z` is constant on a dense open set of units.** On `G^(0)`, `z = Σ_j d_j 1_(D_j ∩ G^(0))`,
  a combination of indicators of finitely many open sets. So `z|G^(0)` is locally constant on
  a dense open `D ⊆ G^(0)`. Take `x, y ∈ D` with neighborhoods `N_x, N_y ⊆ D` on which `z` is
  constant. By minimality there is a compact open bisection `B` with `s(B) ⊆ N_x`,
  `r(B) ⊆ N_y` and `B ≠ ∅`. For `η ∈ B`, `(z 1_B)(η) = z(r η)` and `(1_B z)(η) = z(s η)`.
  So `[z, 1_B] ≡ z(y) - z(x)` on the open set `B`, and `[z, 1_B] ∈ J` forces `z(x) = z(y)`.
  So `z ≡ c` on `D`.
- **Conclusion.** `z' = z - c` is also central modulo `J`. So by the first step the interior of
  `supp z'` is an open subset of `G^(0)`, and it misses `D`. Since `D` is dense, that
  interior is empty, and `z' ∈ J`. Hence `Z(A/J) = K`. `∎`

## What it leaves

For the route `boone-higman-via-germ-steinberg-algebra-presentation` with `A/J` in place of
`A`, two conditions remain: `A/J` must be finitely presented, and step 5's Steinberg kernel
condition must hold. For the first, given a finite presentation of `A`, the question is
whether `J` is finitely generated as an ideal;
`shell-germ-singular-ideal-is-generated-at-the-singular-point` reduces that to the germ
group ring.
