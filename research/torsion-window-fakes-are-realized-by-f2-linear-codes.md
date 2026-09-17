---
rg: 2
id: torsion-window-fakes-are-realized-by-f2-linear-codes
kind: claim
title: The order-three minimal-window Rokhlin fake is the entropy vector of F_2-linear codes, so no information inequality of any kind proves window domination from entropy premises in a group with an element of order 3
distinct_from:
  minimal-window-shannon-derivations-miss-rokhlin-domination: that gives a polymatroid fake, which kills Shannon-type derivations only; this realizes the same vector by genuine random variables (F_2-linear codes), which kills derivations that use any valid information inequality (Zhang-Yeung, DFZ, linear rank inequalities, or ones not yet known).
  twisted-linear-profile-deficits-are-rank-condition-failures: that is about linear profiles invariant on the whole group, whose deficits are rank-condition failures; this fake is linear only on one window and not equivariant, and Z/3 crossed products have the rank condition.
  shannon-window-fakes-on-klein-and-infinite-dihedral-hosts: that gives polymatroid fakes on order-2 hosts and at order 7; this treats only the order-3 fake and records the representability search on the others as open.
artifacts:
  - experiments/entropic-window-fakes-2026-09-17/verify_linear.py
  - experiments/entropic-window-fakes-2026-09-17/z3_rep.json
  - experiments/entropic-window-fakes-2026-09-17/zy_lp.py
  - experiments/entropic-window-fakes-2026-09-17/extract_fake.py
  - experiments/entropic-window-fakes-2026-09-17/linrep.c
---
**ESTABLISHED** (route `torsion-window-fakes-are-realized-by-f2-linear-codes-proof`).

**Setup.** As in `minimal-window-shannon-derivations-miss-rokhlin-domination`. For a configuration
`(k, E, F, psi)` with `X = FE ∪ {1}` and `k log q = 1`, the *entropy premises* on the minimal window are:
- (I) the `x_g`, `g in X`, are independent with `H(x_g) = 1`;
- (D) `H(y_f | x_(fE)) = 0` for `f in F`;
- (T) `H(S) = H(tS)` whenever `S` and `tS` both lie in the window.

The goal is `Phi = H(y_f0) + H(x_1 y_F) - H(y_F) >= 1`.

**Claim.** Let `t in G` have order 3, `E = {1, t, t^2}`, `F = {1, t}`. Let `x_1, x_t, x_(t^2)` be independent
and uniform on `F_2^6`, and let `y_1 = W_0 x`, `y_t = W_1 x` be the two `F_2`-linear maps of rank 5 listed in the
route. Then (I), (D) and (T) hold exactly (entropies in units of 6 bits), and

    Phi = 5/6 < 1 .

The entropy vector is the polymatroid fake of `minimal-window-shannon-derivations-miss-rokhlin-domination`.

**Consequence (class kill, strengthened).** Let `D` be any derivation of `Phi >= 1` for this configuration that uses:
- the premises (I), (D), (T), stated as entropy equalities; and
- any inequalities valid for the entropy vectors of all finite families of random variables. This includes
  Shannon, Zhang–Yeung, Dougherty–Freiling–Zeger, every linear rank inequality, and inequalities not yet known.

Then `D` does not exist, because the realization above satisfies every premise and violates the conclusion. So
the torsion obstruction is not an artifact of Shannon polymatroids. It holds in every group with an element of
order divisible by 3, since all sites and translations lie in `<t>`.

**Where every member dies.** Premise (T) equates *entropies* of translated sets, not *laws*. The two codewords
here are different linear maps, `W_1 ≠ W_0 ∘ shift`. Law-level invariance would force `y_t = β ∘ psi ∘ shift`, so it
would add the missing codeword `y_(t^2)` of the finite orbit, and with that codeword the window LP has value 1
(artifact Section 3 of `research/artifacts/shannon-window-certificates-2026-09-17.md`). A surviving local proof
must use at least one of:
- invariance in distribution, not only in entropy;
- codewords outside `F`, as the Følner count does.

**Computation.** `zy_lp.py` adds every Zhang–Yeung instance, over all assignments of window variables to the four
roles, to the Shannon LP. The LP values do not move:
- `Z/3` (5 variables, 168 instances): 5/6;
- `Z/4` with `E = Z/4`, `F = {0,1,2}` (10239 instances): 7/9;
- `Z/5` with `E = {0,1,2,4}`, `F = {1,2,3}` (70827 instances): 4/5.

This is consistent with realizability at orders 4 and 5, but it does not prove it.

**Open.** Whether the fakes at orders 4 and 5, and on the Klein and `D_inf` hosts, are entropic. `extract_fake.py` writes
their integer targets and `linrep.c` anneals `F_2`-linear realizations. On `Z/3` the search reaches loss 0 within 2M
iterations. On `Z/4` (`z4.txt`, block size 9), a 3M-iteration run ended with best loss 84 in block size 9. That is not
evidence of non-representability: larger blocks and other fields were not tried. The Klein `7/9` run was stopped before it finished.
