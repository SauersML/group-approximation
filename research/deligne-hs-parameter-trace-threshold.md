---
rg: 2
id: deligne-hs-parameter-trace-threshold
kind: claim
title: The Hilbert-Schmidt Maslov parameter group is the whole circle iff small-parameter models have sublinear trace defect, so the HS threshold is a square root and not linear
distinct_from:
  deligne-sep8-first-order-tensor-threshold: that is the operator-norm threshold, which needs op defect o(|t|); this is the normalized-HS parameter group, where only the normalized trace of the curvature has to be o(|t|), which allows HS defect of order o(|t|^(1/2)).
  deligne-sep7-norm-parameter-closed-subgroup: that proves the closed-subgroup structure of the operator-norm set P_op; this proves it for the larger HS set P_2 and adds the trace threshold and the mod-three reading.
  maslov-ce-parameter-set-is-a-closed-subgroup: that set E_CE requires canonical-trace microstates; P_2 imposes no trace, so E_CE is contained in P_2, and equality is not claimed.
  deligne-sector-gap-is-exactly-nonhyperlinearity: that is the fixed parameter 1/3; this places 1/3 inside a parameter group and gives a moving-parameter criterion for that group to be the whole circle.
---

**ESTABLISHED** through `deligne-hs-parameter-trace-threshold-proof`. Unreviewed; no novelty claimed.

Let `Gamma = Sp_4(Z)`, let `b` be the integral covering cocycle of
`deligne-sep7-norm-parameter-closed-subgroup`, and let `c_theta(g,h) = exp(2 pi i theta b(g,h))`. Write `||.||_2`
for the normalized Hilbert-Schmidt norm and `tau` for the normalized trace. Define

```text
P_2 = { theta in R/Z : there are U_n : Gamma -> U(d_n), U_n(e) = I, with
        ||U_n(g)U_n(h) - c_theta(g,h) U_n(gh)||_2 -> 0 for every fixed pair (g,h) }.
```

For a map `U`, put `D_U(g,h) = U(g)U(h)U(gh)^*`, which is a unitary (the curvature).

1. **(T1) Structure.** `P_2` is a closed subgroup of `R/Z` and contains `P_op`, so it contains `1/2`. Hence
   either `P_2 = R/Z`, or `P_2 = (1/m)Z/Z` for one even `m`.
2. **(T2) Trace threshold.** `P_2 = R/Z` if and only if there are nonzero reals `t_n -> 0` and maps
   `U_n : Gamma -> U(d_n)`, with `U_n(e) = I`, such that for every fixed pair
   ```text
   | tau(D_(U_n)(g,h)) - c_(t_n)(g,h) |  =  o(|t_n|).
   ```
3. **(T3) Square-root form.** Write `a = c_t(g,h)` and `eps = ||D_U(g,h) - a||_2`, which is the HS pair defect.
   Then `Re(conj(a) tau(D_U)) = 1 - eps^2/2`. So the condition in (T2) holds whenever
   ```text
   eps = o(|t|^(1/2))     and     Im(conj(a) tau(D_U(g,h))) = o(|t|)      for every fixed pair.
   ```
   HS defect `o(|t|)` is therefore not needed. The HS defect only has to be `o(|t|^(1/2))`, provided the mean
   curvature phase is centred at `2 pi t b(g,h)` to accuracy `o(|t|)`. In probabilistic terms: the curvature
   eigen-angles, measured from `2 pi t b`, need variance `o(|t|)` and mean `o(|t|)`. Their support may be
   large.
4. **(T4) Finite-window linear gap.** If `P_2 != R/Z`, there are a finite set `W` of pairs, `C > 0` and
   `t_0 > 0` such that every dimension `d`, every `U : Gamma -> U(d)` with `U(e) = I`, and every
   `0 < |t| < t_0` satisfy
   ```text
   max_((g,h) in W) | tau(D_U(g,h)) - c_t(g,h) |  >=  C |t|.
   ```
5. **(T5) Mod-three reading.** `1/3 in P_2` if and only if Deligne's triple cover `E_3` is hyperlinear. Hence
   ```text
   E_3 is not hyperlinear   <=>   P_2 = (1/m)Z/Z for an even m with 3 not dividing m.
   ```
   So non-hyperlinearity of `E_3` splits into two conditions that can fail independently:
   - (i) `P_2 != R/Z`, which is the linear trace gap (T4);
   - (ii) on the finite branch, `3` does not divide `m`.

**Reading.**
- The identity tuple `U = I` has `|tau(D) - c_t| = |1 - c_t| ~ 2 pi |t||b|`. So the threshold in (T2) sits
  exactly one order below the trivial model, as in the operator-norm case.
- *Heuristic, not part of the claim.* A winding construction puts a fraction `p ~ |t|` of eigenvalues on a
  full loop and leaves the rest exact.
  - It has `eps^2 ~ |t|` and `1 - Re(conj(a) tau D) ~ |t|`, so it sits exactly at the threshold.
  - This matches the scale `eps ~ |t|^(1/2)` in `research/artifacts/deligne-hs-metric-ladder-2026-09-13.md`.
    That artifact records `o(|t|)` *HS-defect* models as the sufficient scale. (T3) weakens this to trace
    defect `o(|t|)`, i.e. a winding fraction `p = o(|t|)` plus centring.
- An HS proof of non-hyperlinearity of `E_3` must therefore prove the linear trace gap (T4) on one finite
  window, or else control the prime three on the finite branch. An HS construction needs only
  sublinear trace defect at arbitrarily small parameters, and it then yields every parameter, including
  `1/3`.
