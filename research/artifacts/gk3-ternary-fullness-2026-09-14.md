# Ternary anti-central corner: chain audit, an exact F_3 Leavitt tool, and left-inverse lift screens

Lane `gk3-ternary-fullness`, 2026-09-14. Target: refute Gottschalk's conjecture through a one-sided
inverse in `S_- = eps_- F_3[G]`, `G = L_(F_3)(1,2)^x`. No claim node is landed here: the screens are
computational slices of an open bilinear problem, and nothing below decides
`ternary-anti-invariant-swap-corner-is-full`.

## 0. Setting

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `S = F_3[G]`, `eps_+- = 2(1 +- [z])`.
- `S_- = eps_- S`, which is `S/(1 + [z])S`, with unit the image of `1`.
- `pi : S_- -> R` is the evaluation.
- `w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`, `e_- = 2 eps_-(1 + [w])`.

## 1. Chain audit at printed generality

1. **Corner ⇒ direct-finiteness failure** (`anti-invariant-swap-corner-refutes-ternary-surjunctivity`).
   - From `c e_- b = eps_-`, put `A = e_- b + eps_+` and `C = c + eps_+`. Then `CA = 1`, because `eps_+`
     is central and orthogonal to `eps_-`.
   - If `AC = 1`, then `e_- b c = eps_-`. Left multiplication by `e_-` gives `e_- = eps_-`, which
     contradicts `[d] e_- [d] = eps_- - e_- != 0`.
   - PASS.
2. **Direct-finiteness failure ⇒ strict linear automaton** (`stable-finiteness-failure-refutes-surjunctivity`).
   - `tau_a tau_b = tau_(ab)` is faithful. If `tau_C tau_A = id` and `tau_A` is onto, then `tau_A` is
     bijective with inverse `tau_C`, which forces `AC = 1`.
   - PASS.
3. **Left-invertible lift of `s0` with a nilpotent correction.**
   - Suppose `pi(alpha) = s0` and `beta alpha = eps_- + n` with `n` nilpotent. Then
     `(eps_- + n)^(-1) beta` is a left inverse of `alpha`.
   - `alpha beta' = eps_-` would give `s0 x = 1` in `R`, so `0 = t1 s0 x = t1`, a contradiction.
   - For a finite 3-group `P <= G` the augmentation ideal of `F_3[P]` is nilpotent, and `eps_-` is
     central, so every element of `span{eps_-(1 - [p]) : p in P}` is nilpotent.
   - PASS.

**Model test on a finite control.** The dihedral group `<X, Z> <= GL_2(F_3)` of order eight has
`ZXZ = -X`, so the split applies with `w -> X` and `d -> Z`. There `eps_- F_3[D_8] ~= M_2(F_3)`, the image
of `e_-` has rank one, and `c e_- b = 1` is impossible by rank. The chain predicts no strict automaton, as
it must. No flaw was found, so there is nothing to correct on main.

## 2. Tool: `experiments/gottschalk-ternary-corner/tleavitt.py` (cc42d45d4)

- **Path 1.** The normal form over `F_3`, orienting `s1 t1 -> 1 - s0 t0`.
- **Path 2.** The operator action on generic-tail words. `set_dual(True)` recomputes every product through
  it.
- **Units and the quotient.** Units carry checked inverses. `SMinus` stores `[g]` under the signed
  canonical key of `{g, -g}`, which realizes `F_3[G]/(1 + [z])`.
- **`tselftest.py`: all PASS on MSI** (job 784314).
  - Leavitt relations; `s0 t0 != 1`; `W^2 = D^2 = 1` and `DWD = -W`.
  - Thompson inverses; order three of `1 + S[000] s1 T[01]`; multiplicativity of `delta4`.
  - In `S_-`: `[z] = -1`, `[D][W][D] = -[W]`, `e_-` idempotent, and `pi(e_-) = 2(1 + w)`.
  - 466 products cross-checked by both paths.

## 3. Screen: `experiments/gottschalk-ternary-corner/pscreen.py`

- **The system.** For a FIXED lift `alpha` of `s0`, condition 3 is linear in
  `beta in span(C)` and `n in span{[p] - 1 : p in P}`. `P` is the level-two unitriangular group, of
  order 729. The screen solves this exactly over `F_3` by sparse elimination.
- **UNSAT certificates.** When unsolvable, the screen extracts a functional `phi` with `phi(1) != 0` that
  kills every column. `phi` is then re-verified from a fresh unit registry, with 150 dual-path products.
- **Lifts.**
  - The explicit support-four lift `s0 = A q_0 + A' q_1`, where `A = (0,10,11) -> (00,01,1)`,
    `A' = (00,01,1) -> (00,1,01)`, `q_0 = 2(1 + D)` and `q_1 = 2(1 - D)`.
  - Random perturbations of it by kernel vectors of `pi` inside a small ball.
- **Controls, all PASS in every job.**
  - C1: monomials of `R` recover `t0 s0 = 1`.
  - C2: `[g]` recovers `[g^-1]`.
  - C3: `e_-` is UNSAT, its certificate verifies, and a corrupted certificate is rejected.
  - C4: no lift of `s0` is supported on Thompson's `V`, because `V` fixes the all-ones vector of the
    Cantor module.
  - C5: the nilpotent correction is found for `1 + (1 - [p])`.

**Scope.** The true problem is bilinear in `(alpha, beta)`. Each instance is one linear slice with
bounded supports. UNSAT excludes only that slice.

## 4. Results

### 4.1 Job 784841: design flaw, no instance

The lift search `pi(sum lambda_g g) = s0` had no solution over any of the three balls:
- the `eld3` balls (nine-leaf elementary transvections, the compressors, `W`, `D`) of radius 1 and 2;
- the `vwd` ball (Thompson generators, `W`, `D`) of radius 2.

So no instance ran. This is why the explicit lift was added.

### 4.2 Job 785747: 17 instances, all UNSAT, every certificate verified

| family | `|C|` | lifts (support) | columns | rows | certificate support |
|---|---|---|---|---|---|
| eld3, radius 2 | 3346 | 5 (4, 11) | 4074 | 14109–35918 | 729–742 |
| mix = eld3 + V + A' + W + D, radius 2 | 4286 | 7 (4, 11) | 5014 | 17690–45537 | 739–781 |
| vwd, radius 3 | 384 | 5 (4, 13, 14) | 1112 | 2170–4029 | 731–857 |

**Calibration warning.** The certificates are supported on about `|P| = 729` keys, and the systems have
full column rank with rows far exceeding columns. This pattern fits a vacuous reason: the columns
`[c] alpha` may never reach the correction subgroup, and the `beta`-side balls contain no lift of
`t0 = 2 A^-1 (1 - sigma_00) + 2 A'^-1 (1 - sigma_01)`, which needs the level-two sign units. So 4.2 alone
is not evidence against the target. Job 4.3 adds the image-level feasibility test and a family `mix2`
containing that lift.

### 4.3 Job run3: image-feasibility calibration

(Pending; see the lane report.)
