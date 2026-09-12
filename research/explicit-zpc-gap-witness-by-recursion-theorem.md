---
rg: 2
id: explicit-zpc-gap-witness-by-recursion-theorem
kind: route
title: Let a TailoredMIP instance search its own ZPC-IRS upper hierarchy, so that it never stops
target: explicit-zpc-irs-gap-game-witness
requires:
  - zpc-irs-value-computable-upper-hierarchy
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

Let `M -> G_M` be the effective Bowen--Chapman--Vidick TailoredMIP*=RE map
(arXiv:2501.00173, Theorem 2.31), exactly as used in
`perfect-zpc-irs-quantum-gap-game-proof`:

```text
M halts    => a perfect finite ZPC permutation strategy exists,
              hence omega_ZIRS(G_M)=1,
M diverges => omega*(G_M)<1/2.                                  (EXW1)
```

By `zpc-irs-value-computable-upper-hierarchy` there are rational linear-program
optima `alpha_t^Z(G)`, computable uniformly in the finite tailored game `G`,
with `alpha_t^Z(G) >= omega_ZIRS(G)` and `alpha_t^Z(G) -> omega_ZIRS(G)`.

**The self-referential instance.** For a machine index `e`, let `P_e` be the
machine that computes `G_(M_e)` and then, for `t=1,2,...`, halts as soon as
`alpha_t^Z(G_(M_e))<1`. Comparing a rational LP optimum with `1` is exact,
and `e -> P_e` is computable. By Kleene's recursion theorem there is an index
`e_*`, computable from the compiler's index, such that `M_(e_*)` and
`P_(e_*)` compute the same partial function. In particular `M_(e_*)` halts iff
`P_(e_*)` halts. Put

```text
G_0 = G_(M_(e_*)).                                               (EXW2)
```

1. **`M_(e_*)` does not halt.** Otherwise (EXW1) gives `omega_ZIRS(G_0)=1`, so
   `alpha_t^Z(G_0)>=1` for every `t`. Then `P_(e_*)` never halts, which is a
   contradiction.
2. **Quantum soundness.** Hence `omega*(G_0)<1/2` by (EXW1).
3. **Perfect ZPC-IRS value.** Since `P_(e_*)` never halts,
   `alpha_t^Z(G_0)>=1` for every `t`, so `omega_ZIRS(G_0)=lim_t alpha_t^Z(G_0)=1`.
4. **Attainment.** The ZPC-IRS strategies form a closed subset of the compact
   IRS strategy space, and game value is continuous, so value one is attained.
   This is the same compactness step as in `perfect-zpc-irs-quantum-gap-game-proof`.

`G_0` is one concrete finite game. Its verifier is computed from the fixed
TailoredMIP compiler by the s-m-n and recursion theorems, with no choice among
unidentified instances. The certificate of its two values is the argument
above, which uses only (EXW1) and the hierarchy. The perfect strategy is
obtained by compactness and is not described. Downstream compilers need only
its existence together with the named game.

**What this route does not give.** It says nothing about the readable
translate algebra, the selected menus, or atomicity of the value-one strategy.
So `perfect-gap-zpc-has-finite-readable-translate-algebra` and
`zpc-readable-control-freezing-to-lcs` are unaffected.

The same diagonal would select a finite-readable witness if the HALT side had
a computable readable bound: halt when the bounded-readable upper hierarchy
drops below one. `bcv-no-computable-perfect-halt-readable-bound` rules that
premise out.
