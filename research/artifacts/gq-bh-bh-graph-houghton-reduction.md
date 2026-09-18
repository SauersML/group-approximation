# bh-graph-houghton: reduction of Boone–Higman for graph Houghton groups (09-18)

## Sources read at source (TeX, fetched on MSI via the msi wrapper)
- Hill–Kwak–Udall–West, arXiv:2508.21264v1, `main.tex` (md5 12d1768383f5e383c6fba68bbdacc175).
  - Definitions: l.344–430.
  - Flux sequence and finite generation: l.656–760.
  - Algom-Kfir–Bestvina Theorem 3.1, as quoted: l.748.
  - Brown's criterion setup: l.1375–1510.
  - Open question: l.297.
  - Copy: `gqsrc/bh-graph-houghton/`.
- Belk–Fournier-Facio–Hyde–Zaremsky, arXiv:2503.21882v2 (`BHC_for_AutFn.tex`).
  - `prop:fp` (Carette): l.263.
  - The generating set X/Y: l.263–299.
  - `lem:trans`, `lem:faithful`, `prop:2trans`: l.305–358.
  - `prop:fg_stab` (the T-map): l.364–428.

## The construction in one paragraph
- **The group.** Let X be r rays of loops, and let P_G(r) be the G-automorphisms of G * F(X) that far out act as
  w_j·σ(x)·w_j⁻¹ on ray j, with σ Houghton.
- **The embedding.** The based-at-e_1 lift embeds PB_r in it (w_1 = 1).
- **The action.** Φ is the set of finitely supported G-homomorphisms, and it is invariant. BFFHZ's finite-rank lemmas,
  applied on a large finite E, give high transitivity and faithfulness (G MIF). Slides plus the T-map give finitely
  generated stabilizers.
- **What is left.** Only finite presentation of P_G(r).

## What is not done
- Finite presentation of P_G(r); the bounded-support presentation criterion is a sketch.
- Faithfulness of Map → Aut(π_1) for the infinite-type surfaces, which the surface and braided remarks need. Cited,
  not read.
- No MSI computation was run; none would certify finite presentation.
