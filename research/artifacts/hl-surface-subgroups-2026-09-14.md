# Lane hl-surface-subgroups: surface subgroups in every G_HB2(p) (2026-09-14)

Target: Gromov's surface subgroup question (`one-ended-hyperbolic-groups-contain-surface-subgroups`).

## Result

For every odd prime `p`, the Kac–Moody–Steinberg group `G_{HB_2^{(2)}}(p)` of Caprace–Conder–Kaluba–Witzel
contains a quasiconvex genus-2 surface subgroup. For `p ≥ 7` these groups are hyperbolic with property (T)
(CCKW Corollary 7.8). So the question has a positive answer for infinitely many pairwise non-isomorphic
hyperbolic Kazhdan groups, which are rigid and so outside Wilton's reduction.

Landed:
- `cckw-kms-triangle-groups-structure` and its `-citation` route: CCKW Theorem 3.1, the six non-euclidean
  KMS families, Proposition 7.6, Theorem 7.7, Corollary 7.8;
- `kms-hb2-girth-surfaces-give-surface-subgroups` and its `-proof` route: the girth-surface criterion for
  every odd prime;
- `kms-hb2-groups-contain-genus-two-surface-subgroups` and its `-proof` route: the certified instance;
- `experiments/kms-hb2-surface-subgroups/`: certificate, verifier, girth checks, logs;
- item 7 of the covered classes in `one-ended-hyperbolic-groups-contain-surface-subgroups`.

## How it was found

The `F_7` certificates of `ghb7-contains-a-genus-two-surface-subgroup` (lane ideas-growth-hyperbolic)
list six labelled girth surfaces for `G_HB2(7)`. Lift each label from `{1, …, 6}` to `{−3, …, 3}` and
evaluate the 72 vertex words in `SL_4(Z)` through `ψ`. Nontrivial words per surface:

| surface | 25 | 29 | 31 | 43 | 65 | 67 |
|---|---|---|---|---|---|---|
| nontrivial words | 56 | 64 | 64 | 32 | 12 | **0** |

Surface 67 uses only the labels `−1, 1, 2`. Its vertex words are identities in the integral nilpotent
groups `N_3 = <a,b | [a,b,a],[a,b,b]>` and `N_4 = <x,y | [x,y,x],[x,y,y,x],[x,y,y,y]>`. These surject onto
the vertex groups `U_3(p)`, `U_4(p)` at every prime, and no label is divisible by an odd prime. So one
surface works for all odd `p`.

## What had to be proved for general `p`

The `p = 7` criterion computed the vertex group intersections in `SL_4(F_7)`. For every odd `p`, the new
proof route instead does the following.
- It derives normal forms `y^β x^γ u^μ v^ν` from the relators.
- It checks that `ψ(a) = I+E_03+E_12`, `ψ(b) = I+E_10−E_23`, `ψ(c) = I+E_31` satisfy the relators over
  `Z`, with `(ψ(g)−I)^2 = 0`, so `ψ` is a homomorphism mod every prime.
- It reads injectivity on vertex groups and `X_i ∩ X_j = <g_k>` from symbolic entries of `ψ` on normal
  forms. Only division by 2 is used.
- It proves link girths `6, 8, 8` from the normal-form law: there are no 4-cycles, and for `U_4` no
  6-cycles, via the integer identity `2ν + e_3f_2f_3 = −(1+f_1)μ`.

Calibration: breadth-first search in `SL_4(F_p)` for `p = 3, 5, 7, 11` recomputes orders `p^3, p^4` and
girths `6, 8, 8` (`girth-calibration.log`).

## Literature boundary

- Web searches found Kangaslampi–Vdovina (arXiv:1409.1401), Kangaslampi (arXiv:1410.4655), and
  Constantine–Lafont–Oppenheim (arXiv:1407.3958, withdrawn by the authors for an error in Fact 3).
  They study triangular or Fuchsian buildings. `Y` here is not a building: its links are the
  opposite-chamber subgraphs of generalized polygons (CCKW Proposition 7.1).
- The CCKW extraction has no "surface". Nothing on surface subgroups of KMS groups was found.
- Not searched: MathSciNet or zbMATH, or citing papers of CCKW after 2023.

## Exact gaps and next steps

1. **The other five hyperbolic KMS families**: `G_HC2(1)(p)` of type `(3,3,4)`; `G_HC2(2)(p)` and
   `G_HBC2(2)(p)` of type `(3,4,4)` with other orientations of the `U_4` identifications; `G_HB2(3)(p)`
   and `G_HBC2(3)(p)` of type `(4,4,4)`. Two inputs are missing.
   - (a) *Intersections.* A symbolic vertex-injective quotient per family, or the development's
     stabilizer statement (Bridson–Haefliger II.12.18 and II.12.28, stabilizers are local groups) read at
     source, would give `X_i ∩ X_j = <g_k>`.
   - (b) *Labelled girth surfaces.* Orientable sizes are `T = 48` for `(3,3,4)`, `T = 24` for `(3,4,4)`
     and `T = 16` for `(4,4,4)`. Integer labels come from a CSP over `{±1, ±2}` with the normal-form laws.
     Each vertex type needs only `4^6` or `4^8` words.
2. **All hyperbolic generalized triangle groups with unipotent vertex groups** over `F_q`, `q = p^e`. The
   integer lift covers prime fields only.
3. **Gromov's question itself** stays open. This covers one infinite family of rigid hyperbolic groups,
   not a structural class such as all hyperbolic Kazhdan groups.
