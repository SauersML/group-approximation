# Finite presentation of St_n(R) for finitely presented noncommutative R: source record (lane gq-steinberg-q, 2026-09-17)

Consumer: `steinberg-finite-presentation-and-kazhdan-theorem`, established through the citation route
`steinberg-finiteness-kazhdan-citation`, which is used by `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`.

## Primary source (not read)

S. Krstić and J. McCool, *Presenting GL_n(k⟨T⟩)*, J. Pure Appl. Algebra 141 (1999), no. 2, 175–183,
DOI 10.1016/S0022-4049(98)00022-X (Crossref record checked 2026-09-17).
- ScienceDirect returned HTTP 403 to WebFetch on 2026-09-17.
- An earlier review found the Elsevier API needs a key.
- The primary text has not been read by any lane.
- Theorem number, per both secondary sources below: **Theorem 3**.

## Two independent secondary statements, verbatim

1. Ershov–Jaikin-Zapirain, *Property (T) for noncommutative universal lattices*, arXiv:0809.4095v2,
   e-print `EL_n0909.tex` lines 2496–2501. Quoted in the citation route by the 2026-09-13 review:
   > "By a theorem of Krstić and McCool [Theorem 3]{KrM}, the Steinberg group $St_n(R)$ is finitely
   > presented for any $n\geq 4$ and any finitely presented ring $R$, in particular for
   > $R=\mathbb Z\langle x_1,\ldots, x_d\rangle$. […] By [Corollary 2]{KrM}, the group $St_3(R)$ is not
   > finitely presented whenever $R$ surjects onto $F[t]$ for some field $F$."
2. T. Khanh, *General linear and Steinberg groups over the Leavitt algebra L_{F_2}(1,2)*, arXiv:2609.08428v1,
   HTML version fetched 2026-09-17:
   > "Krstić–McCool [10, Theorem 3] prove that St_n(B) is finitely presented for every finitely presented
   > associative unital ℤ-algebra B and every n≥4."

   Bibliography [10]: "S. Krstić and J. McCool, Presenting GL_n(k⟨T⟩), J. Pure Appl. Algebra 141 (1999),
   no. 2, 175–183."

## Hypotheses and the smallest rank

- **Hypotheses.** The ring must be unital, associative and finitely presented as a ring (a ℤ-algebra). There is
  no commutativity, no Noetherianity and no stable-rank condition. The ring `R_L` of
  `leavitt-resolvent-ring-is-fp-and-contains-q` qualifies.
- **Rank.** `n >= 4`, and this is sharp in general. By Krstić–McCool Corollary 2, as quoted by EJZ, `St_3(R)`
  is not finitely presented when `R` maps onto `F[t]`. For `R_L` this does not apply: it is simple and not
  commutative, so it has no quotient `F[t]`. Whether `St_3(R_L)` is finitely presented is not settled.
- **Where the rank matters.** Every rank the swarm uses is at least 10, so `n >= 4` is never binding.

## Making the presentation explicit

`st-n-of-ring-quotient-adds-one-relator-per-ideal-generator` gives, for `n >= 4`:

    St_n(Z⟨g_1..g_d⟩ / (ρ_1..ρ_l)) = St_n(Z⟨g_1..g_d⟩) / ⟨⟨x_12(ρ_1), …, x_12(ρ_l)⟩⟩.

- This is an elementary lane proof.
- So the only non-explicit ingredient is Krstić–McCool's presentation of `St_n` of the free ring `F_6`.
- Obtaining the 1999 paper, for instance through the MSI library proxy, would make `Γ_n` fully explicit.
## Third secondary witness (added by lane gq-lit-arxiv, 2026-09-17)

The zbMATH Open review Zbl 0930.19001 by W. van der Kallen, fetched verbatim via the zbMATH Open API, reads
in part: "Next they prove an analogue for noncommutative rings of a result of U. Rehmann and C. Soulé […]:
If \(n\geq 4\) and \(R\) is a finitely presentable ring, then \(St_n(R)\) is finitely presentable." The
full review, the channels tried for the primary text, and how to obtain it are in
`research/artifacts/gq-gq-lit-arxiv-krstic-mccool.md`.
- The primary text is still unread. ScienceDirect refuses automated fetches, including the open-archive
  PDF link.
- The article is Elsevier open archive (Crossref license 2013-07-17), so a normal browser or the MSI
  library proxy should open it.
