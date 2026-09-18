---
rg: 2
id: window-fakes-on-z4-z5-z7-klein-and-dinf-are-entropic
kind: claim
title: Minimal-window Rokhlin fakes on Z/4, Z/5, Z/7, (Z/2)^2 and D_inf are entropy vectors of F_2-linear codes, so no information inequality of any kind proves window domination in a group with an element of order divisible by 3, 4, 5 or 7, or with two distinct involutions of even or infinite product
distinct_from:
  torsion-window-fakes-are-realized-by-f2-linear-codes: that realizes only the order-3 fake, found by annealing one invariant-looking code, and lists orders 4 and 5, Klein and D_inf as open (annealing failed there); this realizes all of those and order 7, by a linear program over direct sums of one-bit linear atoms in which no atom need satisfy (T).
  shannon-window-fakes-on-klein-and-infinite-dihedral-hosts: that gives polymatroid fakes on the same hosts, killing Shannon-type derivations only; this gives genuine random variables, killing derivations that use any valid information inequality.
  minimal-window-shannon-derivations-miss-rokhlin-domination: that gives polymatroid fakes on cyclic orbits of order 3, 4 and 5; this makes the order 4 and 5 fakes entropic, at the values 85/107 and 4/5.
artifacts:
  - experiments/entropic-window-fakes-relaxed-2026-09-17/relaxed_target.py
  - experiments/entropic-window-fakes-relaxed-2026-09-17/atom_gen.c
  - experiments/entropic-window-fakes-relaxed-2026-09-17/atom_bin_lp.py
  - experiments/entropic-window-fakes-relaxed-2026-09-17/atom_lp.py
  - experiments/entropic-window-fakes-relaxed-2026-09-17/exact_support.py
  - experiments/entropic-window-fakes-relaxed-2026-09-17/exact_support_log.txt
  - experiments/entropic-window-fakes-relaxed-2026-09-17/rep_z4.json
  - experiments/entropic-window-fakes-relaxed-2026-09-17/rep_z5.json
  - experiments/entropic-window-fakes-relaxed-2026-09-17/rep_k2a.json
  - experiments/entropic-window-fakes-relaxed-2026-09-17/rep_dinf.json
  - experiments/entropic-window-fakes-relaxed-2026-09-17/atom_z7_dim1.json
  - experiments/entropic-window-fakes-relaxed-2026-09-17/verify_z4.log
  - experiments/entropic-window-fakes-relaxed-2026-09-17/verify_z5.log
  - experiments/entropic-window-fakes-relaxed-2026-09-17/verify_k2a.log
  - experiments/entropic-window-fakes-relaxed-2026-09-17/verify_dinf.log
  - experiments/entropic-window-fakes-2026-09-17/verify_linear.py
---
**ESTABLISHED** (route `window-fakes-on-z4-z5-z7-klein-and-dinf-are-entropic-proof`).

**Setup.** As in `torsion-window-fakes-are-realized-by-f2-linear-codes`. A configuration `(E, F)` has window
`X = FE ∪ {1}`. The *entropy premises* are:
- (I) the `x_g`, `g in X`, are independent and uniform with `H(x_g) = 1`;
- (D) `H(y_f | x_(fE)) = 0`;
- (T) `H(S) = H(tS)` whenever `S` and `tS` both lie in the window.

The goal is `Phi = H(y_f0) + H(x_1 y_F) - H(y_F) >= 1`, where `f0` is the first element of `F` below.

**Claim.** On each row below, there are independent uniform `x_g` on `F_2^D` and `F_2`-linear `y_f = W_f x`, with
the rows of `W_f` supported on the blocks of `fE`, satisfying (I), (D) and (T) exactly (entropies in units of `D` bits).
The resulting `Phi` is below 1.

| host | `E` | `F` | `D` | exact `Phi` | Shannon LP value |
|---|---|---|---|---|---|
| `Z/4 = <t>` | `{1,t,t^2,t^3}` | `{1,t,t^2}` | 107 | `85/107` | `7/9` |
| `Z/5 = <t>` | `{1,t,t^2,t^4}` | `{t,t^2,t^3}` | 10 | `4/5` | `4/5` |
| `(Z/2)^2 = <a,b>` | `{1,a,b,ab}` | `{1,ab,b}` | 107 | `85/107` | `7/9` |
| `D_inf = <r0,r1>`, `t = r1 r0` | `{1,r0,r1,t}` | `{r1,t^-1,1,t}` | 220 | `52/55` | `7/8` |
| `Z/7 = <t>` | `{1,t,t^2,t^4}` | `{1,t^3,t^5,t^6}` | 3424 | `1479/1712` | `5/6` |

These are the host configurations of `minimal-window-shannon-derivations-miss-rokhlin-domination` and
`shannon-window-fakes-on-klein-and-infinite-dihedral-hosts`. The entropic values sit between the Shannon LP value and 1.

**Consequence (class kill).** Let `D` be a derivation of `Phi >= 1` for one of these configurations that uses the
premises (I), (D), (T) as entropy equalities, and any inequality valid for the entropy vectors of all finite
families of random variables: Shannon, Zhang–Yeung, Dougherty–Freiling–Zeger, linear rank inequalities, or ones
not yet known. Then `D` does not exist. The configurations above satisfy every premise and violate the conclusion.

All sites and all translations `p q^-1` between sites lie in the host subgroup. So (I), (D) and (T) are the same
constraints in every group containing the host. Together with the order-3 realization, the kill holds in every group `G`
containing:
- an element of order divisible by 3, 4, 5 or 7; or
- two distinct involutions `s, s'` with `ss'` of even or infinite order. Then `<s,s'>` is `D_inf`, or it contains
  `(Z/2)^2`: if `n = ord(ss')` is even, `(ss')^(n/2)` is a central involution distinct from `s`, commuting with `s`.

The only torsion groups left are those where every element of finite order has order `m` or `2m`, with all prime
factors of `m` at least 11, and any two distinct involutions have a product of odd order. This is the same list as for
Shannon-type derivations. So *on these hosts, replacing Shannon by any stronger information inequality does not help*.

**Where every member dies.** Premise (T) equates *entropies* of translated sets, not *laws*. Here no individual
atom of the direct sum satisfies (T); only the weighted sum does. A genuine configuration also needs the codewords
to be translates `y_(tf) = psi(x_(tfE))` of one map, which this realization violates. A surviving local proof
must use at least one of:
- invariance in distribution, not only in entropy;
- the full codeword orbit rather than just `F`, as the Følner count does.

**Method (reusable).** The *linear-atom LP* sets every `x_g` to one bit and each codeword to one linear functional (or 0)
on its read bits. It minimises `Phi` over convex combinations of the atom rank vectors, imposing (T) on the combination
only. A rational optimum is the rank vector of a direct sum of atom copies, so any value `< 1` is an entropic fake.
It found these fakes within seconds to minutes, where annealing a single code (`linrep.c`) had failed.

**Open.**
- Are the Shannon values `7/9` (on `Z/4` and Klein), `7/8` and `5/6` entropic? The atom LP uses atoms of
  dimension at most 1 per codeword. The gap may be an artifact of that restriction, or it may be a non-Shannon
  effect, which would be the first sign that stronger inequalities matter here.
- For `Z/7`, `verify_linear.py` was not run: at `D = 3424` the representation is 44 MB. The exact check is the
  Fraction arithmetic of `exact_support.py` on the 110 atom rank vectors (route step 3).

## Attempts
