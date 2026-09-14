# skf-consequences — ledger for simple_kazhdan_sofic_group.tex at bf961c128

Lane brief: `ct/ROSTER-sk.md` (session nonsofic-existence-49), re-scoped at 18:58. The committed note is the 340-line
version at bf961c128 (md5 7b3dc4ec92b4581553bc0dc2b0edcb99). Rows are keyed `LINE:<l>@bf961c128`.

## Earlier range withdrawn

The original range, tex 684–743 at b965d63ba (sec:consequences), no longer exists at the tip, so nothing was built or landed
for it.

## Range and split

- ct-bilateral-mf and skf-consequences share tex 174–228, "A finite tower detects every normal subgroup".
- Split proposed to ct-bilateral-mf (one direct message, 19:0x); it replies only if it objects:
  - ct-bilateral-mf, l.174–204: g, w, the separated partition, a root h not commuting with g, s ∈ B_1(U), k = [g,h] in
    the corner M_3(B_m(U)), κ locally constant, and the clopen W with κ ≡ κ₀ ≠ I_d.
  - skf-consequences, l.205–228: the tower copy H_W ≤ G; simplicity of GL_d(F_2); H_W ≤ N; e_12(e_W) ∈ N; the level
    ideal I_N; N = G.
- Interface, landed first in my module: the named Prop `TowerCornerWitnessStatement`. ct-bilateral-mf produces it.

CLAIM l.205–228 GroupApproximation/Manuscript/SimpleKazhdanSofic/TowerNormalSubgroup.lean

## Route check (tex 174–228)

The Pestov91 simplicity route on main (`SplitSimplicity.rootDetection_of_split`, `SimpleModCentreCrossed` via local
annihilation) is not the printed tower route, so the printed proof needs new carriers. Reusable carriers on main:

| printed step | carrier | verdict |
|---|---|---|
| GL_d(F_2) simple for d ≥ 3 (l.217–218) | `FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo` (Algebra/FinitaryLinearBinarySimple, root-imported) | fits; centerless follows from simple and nonabelian |
| every matrix over F_2 is elementary (generation, l.215) | `FinitaryLinear.elementaryGroup_zmodTwo_eq_top`, `ChainRadical.elementaryGroup_matrix_zmodTwo_eq_top` | fits |
| I_N two-sided ideal, R simple ⇒ N = G (l.224–228) | `Pestov91.levelIdeal`, `normal_eq_top_of_elGen_mem` (SimpleModCentre) | statement fits; Lean moves roots by commutators, while the printed sentence uses permutation matrices plus eq:elementary |

## RE-SCOPED 19:45 to the tip e80dcf20a (386 lines, md5 4ad4921253626a4f858866c716a13385)

The "Simplicity" subsection (≈ tex 179–238) was rewritten to go through one finite simple subgroup, with no κ₀
conjugation. Rows are keyed by 12-hex sentence hash from `metadata/SK_SENTENCE_CENSUS.tsv`, once skf-census has
regenerated it at the tip.

Split re-proposed to ct-bilateral-mf (19:5x); it replies only if it objects:
- ct-bilateral-mf: small V, the noncommuting root h = e_ij(e_V), k = [g,h], and the entries of k − I₃ and k⁻¹ − I₃
  lying in the ε-span (≈ l.180–196, 210–221).
- skf-consequences: ε_ab products and nonvanishing, ψ injective and multiplicative, the embedding of GL_d(F₂), H ≤ G,
  k ∈ H, H ≤ N, e_pq(e_V) ∈ N, the ideal J, the cover, N = G (≈ l.197–209, 222–238).
- Interface: `SimplicityCommutatorWitness` in the new module `Manuscript/SimpleKazhdanSofic/SimplicityStatement`.

CLAIM ≈ l.197–209, 222–238 GroupApproximation/Manuscript/SimpleKazhdanSofic/{SimplicityStatement,TowerMatrixUnits,TowerCopy,TowerCopyGroup,SimplicityNormalSubgroup}.lean

## Ledger

| printed step (tip e80dcf20a) | carrier | state |
|---|---|---|
| ε_ab = e_{T^aV}u^{a−b} | `SimpleKazhdanSofic.towerE` (TowerStatement, 94f396a4f) | landed |
| ε_ab ε_{a′b′} = δ_{ba′} ε_{ab′} (V ∩ T^jV = ∅, 0<\|j\|≤2w) | `towerE_mul_towerE` (TowerMatrixUnits) | probing |
| ε_ab ≠ 0 as V ≠ ∅ | `towerE_ne_zero` (TowerMatrixUnits) | probing |
| ψ injective, multiplicative, linear | `towerHom`, `towerHom_injective` (TowerCopy; blockwise ψ) | probing |
| A ↦ I₃ − ψ(I_d) + ψ(A) embeds GL_d(F₂) | `towerCopy`, `towerCopy_injective` (TowerCopyGroup) | probing |
| H ≤ G through transvections | `towerCopy_mem_elementaryGroup`, `towerCopy_elementaryUnit` | probing |
| GL_d(F₂) simple (d ≥ 3) | `FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo` (on main) | fits |
| k ∈ H, N ∩ H nontrivial normal, H ≤ N, e_pq(e_V) ∈ N; the ideal J, the cover, N = G | SimplicityNormalSubgroup (to write) | open |

Superseded: `TowerCornerWitness` (94f396a4f) was the interface for the bf961c128 text. It is landed, unwired, and not
consumed.
