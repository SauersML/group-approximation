# Leavitt isometry commutators, and the corner Leavitt family

Lane `gk-ri-nofd` (family R), 2026-09-12. Supports the established claim
`leavitt-isometry-commutators-constrain-el3-rank-models` and adds Attempts material to the open
gate `rank-models-of-el3-satisfy-the-two-root-identities`. It builds on
`research/artifacts/el3-two-root-identities-2026-09-12.md` ([TR]) and
`research/artifacts/el3-rank-ring-rigidity-2026-09-12.md` ([RR]).

## 0. Aim

The gate `rank-models-of-el3-satisfy-the-two-root-identities` is, in characteristic two and for
`R = L_(F_2)(1,2)`, the single identity `N_23 N_12 = 0`, where `N_ab = sigma(x_ab(1)) - 1` for a
homomorphism `sigma : EL_3(R) -> M^x` into a characteristic-two rank ultraproduct `M`. [TR]
Calibration C says a proof must use coefficients that generate a subring with **no
finite-dimensional representation** (a unital Leavitt family), or the no-rank-model hypothesis
beyond group relations. The listed dead attempts (five-term single-element expansion,
self-similar displacement counting, same-row/column identities) used only coefficient `1` or
finite-subgroup counting, never the isometry relations `t_i s_j = delta_ij`,
`s_0 t_0 + s_1 t_1 = 1`.

This note records two things: (Section 1) the exact operator relations the isometry structure
puts on a model, which are new handles of exactly the demanded kind; and (Section 2) the
reframing of the extraction as assembling an order-two Leavitt family in a corner, with the
impossibility half already established and the single-corner route shown circular.

Notation: char two throughout, so every `sigma(x_ab(c))` is an involution and
`n_ab(c) := sigma(x_ab(c)) - 1` satisfies `n_ab(c)^2 = 0`, `(1+n_ab)` a homomorphism
`(R,+) -> M^x`. `[g,h] = g h g^{-1} h^{-1}`, and `g^{-1} = 1 + (g-1)` when `(g-1)^2 = 0`.

## 1. The isometry commutator relations

The Steinberg relation `[x_12(a), x_23(b)] = x_13(ab)` holds in `EL_3(R)` for all `a, b in R`.
Take `a = t_i`, `b = s_j` and use `t_i s_j = delta_ij`:

```text
[x_12(t_i), x_23(s_j)] = x_13(delta_ij),   = x_13(1) if i = j,  = 1 if i != j.
```

Apply `sigma`. Put `A_i = n_12(t_i)`, `B_j = n_23(s_j)`, `Z = n_13(1) = N_13`. Expanding the
commutator of two involutions (as in [RR] Lemma 3),

```text
(1+A_i)(1+B_j)(1+A_i)(1+B_j) = 1 + A_iB_j + B_jA_i + A_iB_jA_i + B_jA_iB_j + A_iB_jA_iB_j .
```

**Lemma (isometry commutators).** In every characteristic-two rank model of `EL_3(L_(F_2)(1,2))`:

```text
(off)  i != j:  A_iB_j + B_jA_i + A_iB_jA_i + B_jA_iB_j + A_iB_jA_iB_j = 0 ;
(diag) i = j:   A_iB_i + B_iA_i + A_iB_iA_i + B_iA_iB_i + A_iB_iA_iB_i = Z .
```

Symmetrically, from `[x_12(s_i), x_23(t_j)] = x_13(s_i t_j)` one gets relations governed by the
elements `s_i t_j` (the level-one matrix units and their off-diagonal partners `s_i t_j`,
`i != j`, which are the nonzero nilpotent-free monomials of `R`). And from
`s_0 t_0 + s_1 t_1 = 1`, applied inside the root subgroup `12`,

```text
1 + N_12 = (1 + n_12(s_0 t_0))(1 + n_12(s_1 t_1)) ,
```

so `N_12` decomposes through the two orthogonal idempotents `e_i = s_i t_i`.

These relations use `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1` directly. By [TR]
Calibration C they are unavailable to any model of `EL_3(S)` for a coefficient ring `S` with a
finite-dimensional representation, because no such `S` contains a unital order-two Leavitt
family. They are therefore of exactly the type a proof of the gate must use, and are not among
the dead attempts in [TR] Section 5 or [RR] Section 4.

**Status of the connection to `N_23 N_12`.** The target product `N_23 N_12 = n_23(1) n_12(1)`
has coefficient `1` on both roots. The relations above carry coefficients `t_i`, `s_j`. Bridging
them requires expressing the coefficient-`1` root elements through the isometry generators. The
additive root homomorphism gives `1 + N_12 = (1+n_12(e_0))(1+n_12(e_1))` through the idempotents
`e_i = s_i t_i`, but `1` is not an additive combination of the `t_i`, and `x_12` of a product is
not a commutator, so no purely group-relational bridge is available. Establishing the bridge, or
running the relations (off)/(diag) directly toward `N_23 N_12 = 0`, is the open step. This lane
did not close it.

## 2. The extraction is a corner Leavitt family, and the single-corner route is circular

[TR] Theorem D extracts, from a model satisfying the matrix-unit hypothesis (equivalently
`N_23 N_12 = 0`), a unital ring homomorphism `C : R -> p_1 M p_1`, with `p_1 = N_12 N_21`, and
shows `p_1 M p_1` is again a rank ultraproduct. A unital homomorphism from `R = L_(F_2)(1,2)`
into a ring `e M e` is the same datum as an **order-two Leavitt family in `e M e`**: elements
`S_0, S_1, T_0, T_1 in eMe` with `T_i S_j = delta_ij e` and `S_0 T_0 + S_1 T_1 = e` (by the
universal property of `R` on that presentation).

**Impossibility half (already established, cited, not re-proved).** A corner `eMe` of a rank
ultraproduct `M`, with `e` an idempotent of positive rank, is again a rank ultraproduct ([TR]
Theorem D, via Fitting/idempotent lifting). By `leavitt-algebra-has-no-unital-rank-model` there
is no unital homomorphism `R -> eMe`, so `eMe` contains no order-two Leavitt family. Directly:
`T_0 S_0 = e` in a rank ring forces `S_0 T_0 = e` (stable finiteness), whence `S_1 T_1 = 0`; but
`T_1 S_1 = e` gives `rk(S_1 T_1) >= rk(T_1 S_1) = rk(e) > 0`, a contradiction.

**Consequence: the single-corner extraction is circular.** The only known way to place the
images `C(s_i), C(t_j)` inside one corner and make `T_i S_j = delta_ij` and `Sum S_i T_i = e`
telescope is the block form `n_ab(c) in p_a M p_b`, which is exactly the matrix-unit hypothesis,
i.e. `N_23 N_12 = 0`. So "extract a corner Leavitt family from a single Peirce corner" assumes
what it would prove. A non-circular extraction must build the four partial isometries from data
that a model with `N_23 N_12 != 0` genuinely supplies -- for which the isometry commutator
relations of Section 1 are the natural, and so far only, non-relational, no-f.d.-representation
input.

## 3. Where this lane stops

- The relations (off) and (diag) are proved and available, but not yet connected to the
  coefficient-`1` product `N_23 N_12`.
- The extraction is exactly the assembly of a corner Leavitt family; its impossibility is
  established; the single-corner route is circular.
- No non-circular assembly of the four partial isometries from `N_23 N_12 != 0` was found. This
  is the open content, and it is the whole gate.
