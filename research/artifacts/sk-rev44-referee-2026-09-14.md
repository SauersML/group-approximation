# sk-rev44-referee: referee of the rev4.3 → rev4.4 changes (2026-09-14)

Target: `simple_kazhdan_sofic_group.tex` rev4.4 on main f34e9c0b1c, md5 c909343ec38f3d3e7976342073509639 (confirmed locally and on main). The lane could not write its own report file (harness refusal), so main records its verdict here.

## Verdict: no ERROR, no GAP. Three clarity fixes plus one optional.

## Checked by hand (correct)
- §1 renames 1_V, x; the reordered finite-models sentence; "N_k → ∞ as G is infinite".
- §2: X is a Cantor set (an isolated point forces X finite). Brown's formulation no longer relies on the dropped Kirchberg/LLP sentence; Ozawa's LLP remark (l.49–51) stays cited.
- Theorem 2 without "matricial"; Cor 3 "images of a fixed generating set" matches Theorem 2's marking.
- §3 main proof:
  - Neumann–Neumann wreath commutator;
  - level isolation without wraparound;
  - the lamplighter host with c and η;
  - the models;
  - the Whitehead product diag(v₁v₂v₁⁻¹v₂⁻¹,1,1).
- §3 solvable-WP block:
  - left multiplication gives [β,h_γ] = level-0 multiplication by γ⁻¹;
  - the products f(m)f′(m−ℓ) are ordered consistently with the models;
  - κ, θ, ζ stay inside θ's domain for |ℓ| ≤ r;
  - "the argument above applies to it" is justified;
  - the word problem transfers to G_Δ.
- §4: continuum clause (substitution reduction; digit coding realizes every degree; Sacks antichain).
- Questions: accurate; (Y,T′) removes the S clash.
- New wording accurate: "Kionke and Schesler asked…", Boone–Higman–Thompson, "In the proof of simplicity,…", the Darbinyan sentence.
- Dropped material is absent. A grep finds none of: separable factors, SL₃(Z), Heisenberg, Osajda, exactness, no decidable host, Kac–Moody background, w_g, KMS, Rauzy, CFKP, NPS, OzawaUniversal.

## Fixes (applied by main in rev4.5)
- **U1 (abstract, +2 lines):** "a subgroup of such a group" could read as "a subgroup of some G_X" (false: SL₃(Z) lies in no G_X). Replace with "a subgroup of an infinite finitely generated simple Kazhdan group that is a limit of finite simple groups whose Cayley graphs form expanders".
- **U2 (l.411–412):** "keeps it." → "keeps the word problem solvable."
- **U3 (l.313):** "Each property alone was known." → "Simple hosts with only one of property~\textup{(T)} and LEF were known."
- **U4 (optional, +1 line):** restore "on the normal structure of $\GL_n$" and "on a tower over one small cylinder" in the Stepanov sentence.

Not checked: bibliography data and locators (audited earlier), compile.
