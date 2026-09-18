# bh-free-38: Nowak's Torelli lower-central quotients (2026-09-18)

This is a lane artifact. Nothing here is reviewed, and no priority is claimed.

## Source read

Nowak, *Property (T) and nonlinearity of mapping class group quotients*,
arXiv:2609.12196v1 (10 Sep 2026). The TeX `torelli_T.tex` (3011 lines) was
fetched through the MSI e-print and is in `gq/src/bh-free-38/`.

| Item | TeX line | Content used |
|---|---|---|
| definitions | 176–178 | `Q_{g,c} = Mod/T_g[c+1]`, `N_{g,c} = T_g/T_g[c+1]` |
| Theorem A (`thm:main`) | 193 | `g>=3, c>=1`: `Q_{g,c}` is f.g., infinite and has (T); `N_{g,c}` is f.g. nilpotent; the quotient is `Sp_2g(Z)` |
| Theorem D (`thm:nonlinearity`) | 274 | `g>=3, c>=2`: every map `Q_{g,c} -> GL_d(C)` has infinite kernel |
| Malcev (`thm:malcev`) | 2179 | the Lie algebra of the unipotent completion is `t_g/t_g[c+1]` |
| Lemma `lem:rationalkernel` | 2214 | a rational `G_a` meets the lattice in an infinite set |
| Hain (`thm:hainkernel`) | 2282 | central `1 -> Z_g -> P_g -> U_g -> 1`, with `z_g ⊂ t_g[2]` and `z_g ∩ t_g[3] = 0` (Hain pp. 604–612) |
| Cor `cor:centralline` | 2317 | the line survives in `N_c` for `c >= 2` |
| Thm `thm:arithmeticextension` | 2345 | CSP and virtual algebraic extension (Margulis) for `Sp_2g(Z)`, `g>=3` |
| remark | 2498–2500 | (T) and superrigidity force the representation to kill Hain's central subgroup |
| Cor `cor:charzero`, `cor:allfields` | 2506, 2561 | no finite-index subgroup is linear, over any field |

## What this lane added

1. **`torelli-lower-central-quotients-do-not-virtually-split`**: if the extension
   virtually split, even modulo a finite subgroup, then Margulis's algebraic
   extension of the conjugation action would produce a finite-kernel
   representation, contradicting Theorem D.
2. **`torelli-lower-central-quotients-are-not-residually-finite`**, with its route:
   - Hain's rational central line, which is `Mod`-fixed because `Mod` is perfect,
     gives a normal virtually-`Z` subgroup `D` of `Q_{g,c}`.
   - `Q/D` is arithmetic in `U' ⋊ Sp_2g`, the Levi decomposition of the truncated
     relative completion. It virtually splits by Margulis–Raghunathan vanishing of
     `H^1`.
   - Over a virtual section, the preimage is a central extension of a congruence
     subgroup by `Z`. Its class is non-torsion by item 1.
   - Borel then makes that class a multiple of the universal-cover class, so the
     group is commensurable with a Deligne lattice. Deligne's theorem, through the
     repo's citation nodes, gives a nontrivial finite residual.
3. **`torelli-lower-central-quotients-satisfy-boone-higman`** (OPEN): records the
   word problem as open, gives the reduction to Johnson-filtration gaps, and lists
   the host exclusions.

## Trust surface

These inputs are cited, not read at source by this lane:
- Hain (via Nowak's statement);
- Margulis–Raghunathan vanishing of `H^1` for rational modules;
- the Levi decomposition of the relative completion;
- Borel's stable range in degree 2 for `Sp_2g`, `g >= 3`;
- Deligne 1978 (via the repo's citation nodes).

The Borel-free variant through Deligne's continuous-cohomology argument is only
sketched.

## Leads

- **Word problem, `c = 2`.** Relate `J(3)/T_g[3]` to Hain's line through
  Morita's Casson core `d`. Then the torsion part is the only obstruction.
- **Hosts.** A BH host must contain a Deligne-type lattice over `Sp_2g`. Test the
  Deligne-lattice host exclusions on main for transfer to `Sp_2g`, and to groups
  that are commensurable up to a finite central subgroup.
- **The other Nowak family.** `Aut(F_3)/(IA_3)[c+1]` has (T) by Nowak, but its
  linearity and residual finiteness are not addressed there. A similar Hain-type
  line would require analysing the relative completion of `Aut(F_3)`.
