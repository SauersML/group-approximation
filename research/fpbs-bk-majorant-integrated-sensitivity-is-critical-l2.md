---
rg: 2
id: fpbs-bk-majorant-integrated-sensitivity-is-critical-l2
kind: claim
title: Integrating the Russo-BK inequality from p_c controls walk connectivity exactly when the critical operator is bounded
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is Hutchcroft's critical l2 conjecture itself; this shows that the Russo-BK differential-inequality route to integrated pivotal sensitivity yields a finite bound exactly on the graphs where that conjecture holds, and on collapsed graphs every finite-order version of it outputs +infinity.
  fpbs-critical-l2-equivalent-to-dyadic-projection-estimate: that makes the dyadic shell estimate Q2 equivalent to critical l2; this makes the tree-graph majorant for supercritical walk connectivity equivalent to critical l2, a different quantity (a_n(p) above p_c rather than critical shell norms).
  fpbs-integrated-sensitivity-universal: that is the OPEN target (IS); this is an obstruction theorem about one class of proofs of it, not a proof or disproof of (IS).
  fpbs-fibre-bubble-forces-mean-field-susceptibility: that integrates a differential inequality below p_c for the susceptibility; this integrates the entrywise Russo-BK inequality upward from p_c for the two-point kernel and shows why it cannot cross p_c without critical l2.
---

**Setting.** `Gamma` is a finitely generated nonamenable group, `S` a finite
symmetric generating set with `|S|=d`, `G=Cay(Gamma,S)`, `o` the identity,
`P` the simple random walk operator (`P(x,xs)=1/d`), `rho=||P||_(2->2)<1`,
`p_c=p_c(G)`, `tau_p(x,y)=P_p(x<->y)` and `T_p` the kernel `tau_p`; write
`T=T_(p_c)`. All kernel products are sums of nonnegative terms, valued in
`[0,infinity]`. Put `a_n(p)=E[tau_p(o,X_n)]`, `X` the walk from `o`, and

```text
A_n^(k) = sum_x P^n(o,x) [T (P T)^k](o,x),     M_n(delta) = sum_(k>=0) (d delta)^k A_n^(k).
```

`M_n(delta)` is the minimal entrywise solution of `X' = d X P X`, `X(0)=T`,
paired with the walk: it is what the Russo-BK inequality
`d tau_p/dp <= d (T_p P T_p)` produces when integrated upward from `p_c`.

**Theorem (ESTABLISHED).**

1. *(Majorant forces critical l2.)* If `M_n(delta)<infinity` for some
   `n>=0` and `delta>0`, then `||T_(p_c)||_(2->2) <= 1/(d delta p_c)`.
   More precisely `||T_(p_c)||_(2->2) = limsup_m (T^m(o,o))^(1/m)`, and
   `p_c^(k+n) T^(k+1)(o,o) <= A_n^(k)`.
2. *(Critical l2 gives the majorant.)* If `||T_(p_c)||_(2->2)=M<infinity`,
   then for all `n` and `0<delta<1/(dM)` with `p_c+delta<=1`,
   `a_n(p_c+delta) <= M_n(delta) <= M rho^n/(1-d delta M)`. So the radius
   `delta_*` of `M_n` does not depend on `n`, and
   `1/(dM) <= delta_* <= 1/(d p_c M)`. In every case `delta_*=0` iff
   `M=infinity`.
3. *(Finite-order expansions are vacuous under uniqueness.)* If `P_s` has a
   unique infinite cluster, then every entry of `T_s P T_s` is `+infinity`.
   More generally, every entry of any finite product of kernels from
   `{I, P, T_q : q in [0,1]}` that contains two factors `T_s, T_(s')` is
   `+infinity`, provided both `s` and `s'` have uniqueness. Under collapse
   `p_c=p_u` this holds for all `s,s'>p_c`, so every remainder term of every
   finite Picard iterate of `tau_q <= T + d int_(p_c)^q T_s P T_s ds` is
   `+infinity` for every `q>p_c`.

**The obstruction this names.** Call the *Russo-BK class* the arguments
that bound `a_n(p_c+delta)`, hence `lambda(p_c+delta)`, using only
Harris-FKG, Russo's formula, the BK inequality and the critical kernel. Any
such argument either keeps a supercritical factor, and then by (3) its
bound is `+infinity` on a collapsed graph, or it closes up to the
critical-kernel series `M_n(delta)`, and then by (1) it is finite only when
`||T_(p_c)||<infinity`. **Invariant:** `||T_(p_c)||_(2->2)`. **Step where
every member dies:** the passage from the critical kernel to any `delta>0`.
Either the first supercritical factor appears (vacuous by (3)), or the tree
series has zero radius (by (1)). So the class cannot prove (IS)
(`fpbs-integrated-sensitivity-universal`) on any graph where it does not
already prove Hutchcroft's conjecture
`fpbs-nonamenability-bounds-critical-connectivity-operator`. The class's
apparent advantage over l2 methods, namely that it tolerates spikes in
`tau_p` above `p_c`, is lost at its first step. Part (2) is Hutchcroft's
known mechanism, and it is included here to show that (1) is sharp up to the
factor `p_c`.

Proof: `research/fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof.md`.
