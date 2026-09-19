---
rg: 2
id: dkkms-ev-list-structure-needs-lists-exponential-in-k
kind: claim
title: The ev-form list structure (List-Str_t) fails on DKKMS 2-to-1 games for every list size t < 2^(k-l-11) -- a defect-line split of a J-instance with kernel rank k-8 has value 0.605 and ev-uncovered satisfied mass above 0.11 against every t-list, because a reference agrees with an A-label off a proper subspace with probability at most 1/2 -- while every list-guessing rerun of Theorem C with loss t^-1 or worse needs t < 2^(k-2l-5) against the outer soundness floor 2^-k, so that route to the constant-bias cell is dead for every t
distinct_from:
  dkkms-list-seed-needs-lists-exponential-in-l: that bounds lists in seed form (B-labels equal to the reference) with kernel rank 2l and gets t >= 2^(l-6); this bounds the ev-form mass D that Theorem C actually needs, allows an index map depending on the whole (U,V,L'), takes kernel rank k-8, and gets t >= 2^(k-l-11), which beats every outer-soundness budget.
  constant-bias-selectors-need-seed-dishonest-witnesses: that proves Theorem C and Lemma F with one reference; this refutes the list form of its 50 percent hypothesis (Str) on the YES inputs of regular Gap3Lin, for every list size compatible with the outer soundness of DKKMS.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the selector hole H1; this kills one route to its constant-bias cell (list-reference structure plus a list-guessing decoder) and leaves the hole open.
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that verifies (E), (M) with K = 1 and the annotation for honest encodings; this uses its annotation and edge law to build witnesses that no small list explains in ev-form.
artifacts:
  - experiments/ugc-ev-list-2026-09-17/check_ev_list_kernel_rank.py
---

**ESTABLISHED** (Theorem EL and Corollary EL). Route:
`dkkms-ev-list-structure-needs-lists-exponential-in-k-proof`.

## What is refuted

The held wave-14 node `list-reference-constant-bias-decoding-loses-t-squared`
(not on main) proves a list rerun of Theorem C, **Theorem C_t**, and names one
remaining selector-free prerequisite for the constant-bias cell of H1, in
ev-form. Its need `fb418c25` asks to prove it with `t = 2^(O(l))`, and to check
that DKKMS outer soundness is below `2^(-O(l)) gamma'^6 / t^2`.

> **(List-Str_t(gamma, gamma', eps))** every labelling `H` of `G` with
> `val_G(H) >= 1/2 + gamma` has outer labellings `lambda^1..lambda^t` of value
> `>= 1 - eps` and a map `i : Q -> [t]` with `D(H, Lambda) <= gamma - gamma'`,
> where `D(H, Lambda) := mu{ e in Sat(H) : ev_e(sigma_(p_e)) != <lambda^(i(q_e))_(a_e), x_e> }`.
>
> **(S_t)** on NO inputs `val(Phi) <= s < c_t0/2`, with
> `p = gamma'^3 2^(-l-2)` and `c_t0 := p^2/(t^2 K^2) - 2 eps`.

Both conditions are quoted from that node. This node shows that, on DKKMS
applied to regular Gap3Lin, no `t` satisfies both.

## Setting

The notation is that of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`
(DKKMS, ECCC TR16-198, Section 4.2, quoted verbatim there) and of Theorem LS in
`dkkms-list-seed-needs-lists-exponential-in-l`:
* tuples `U`, `X_U` (dimension `3k`), `H_U`, smoothed tuples `V`,
  `H' = H_U ∩ X_V`;
* the multi-edge game `G_multi`, whose copies `e` carry seed `w_e = (V,L')`,
  target `a_e = U` and direction `x_e ∈ L \ L'`, with `L = L' + <x_e>`;
* `ev_e(sigma)` is the unfolding of `sigma` at `(U,L)`, evaluated at `x_e`;
* a kernel `Phi = (phi, zeta) : F_2^X -> F_2^l x F_2^s` of rank `n = l + s`
  that kills every equation vector, `K = 0 x F_2^s`, `c(S) = Phi(S) ∩ K`;
* the **defect-line labelling** `h`: `y_d|_S` if `c(S) = <(0,d)>`, else `x|_S`,
  where `y_d = x + <d, zeta(·)>`.

A **t-list** here is any family of per-tuple functionals `lambda^j_U` on `X_U`
(`j <= t`), with no value condition, together with an index map `i(U, V, L')`.
The index may depend on the target tuple as well as on the seed, which is more
than List-Str_t allows. `D(h, Lambda)` is defined by the formula above.

## Statements

**Lemma A (half agreement).** Let `W` be a proper subspace of a finite
`F_2`-space `X`, let `x` be uniform on `X \ W`, and let `psi != 0` be a
functional. Then `Pr[psi(x) = 0] <= 1/2`, with equality iff `W` is not
contained in `ker psi`.

**Theorem EL.** Let the instance carry a generic kernel of rank `n = l + s`
(Theorem LS setting, `l >= 3`, `s >= 2`), let `x` satisfy every equation, and
let `beta_bad` be the `G_multi` mass of tuples on which `Phi` is not onto `X_V`.
Then for every t-list and every index map,

```text
D(h, Lambda)  >=  (3/8) P(N_l = 1)  -  t 2^(-s-2)  -  (3/8)(2^(l-k) + 2^(-s-1) + beta_bad),
val(h)        >=  v(l) - 2^(l-k) - beta_bad          (Theorem LS, item 2),
```

where `N_l` has the limit nullity law of Theorem LS, and
`v(l) = 1 - E[2^(-1-N_l)]`.

**Corollary EL (the refutation and the class kill).** Let `l >= 8`, `k >= 3l`,
and take the J-instance of rank `n = k - 8`, so `s = k - l - 8`. Then:

1. **List-Str_t fails for every `t < 2^(k-l-11)`.** The labelling `h` has
   value `>= 0.605`. For every `gamma <= 0.105`, every `gamma'` and every
   `eps`, every t-list with `t < 2^(s-3) = 2^(k-l-11)` has
   `D(h, Lambda) > 0.110 > gamma - gamma'`.
2. **Outer soundness floor.** Every regular 3LIN instance has
   `val(Phi_k) >= 2^(-k)`. With `K = 1` (item 4 of the decoding node),
   `(S_t)` forces `t < gamma'^3 2^(k/2 - l - 5/2)`. More generally, any
   condition of the form `val(Phi) < (p^2/(t^alpha K^2) - 2 eps)/2` with
   `alpha >= 1` forces `t < max(1, 2^(k-2l-5))`.
3. **Dichotomy.** Both upper bounds are below `2^(k-l-11)`, since `l >= 8`
   and `k >= 24`. So for every `t`, either (List-Str_t) fails on a perfectly
   satisfiable regular YES input, or (S_t) fails on every NO input. The same
   holds for every list-guessing loss `t^(-alpha)` with `alpha >= 1`.

The artifact checks item 1 exactly for `8 <= l <= 64` at `k = 3l`, where every
error term is largest. Beyond `l = 64`, Lemma 6 of the LS route moves every
quantity by less than `2^(-60)`.

## What this kills (impact types 3 and 4)

**Class killed.** Every closure of the constant-bias cell of H1 (or H2)
through two steps. First, a list-reference structure theorem in ev-form, on all
YES inputs of regular Gap3Lin. Second, a decoder that guesses the list index
and so loses a factor `t^(-alpha)`, `alpha >= 1`, in the outer soundness it
needs. This includes Theorem C_t with any `t`, and the plan of need
`fb418c25` (`t = 2^(O(l))`), which already fails at `k >= 3l`.

**Invariant.** The number `2^s - 1` of distinct defect-line assignments
`y_d|_(X_U)` at one tuple, against the list size `t`. It is bounded only by
the kernel rank `n = l + s`, which may be as large as `k - O(1)` on J-instances,
not by `l`.

**Where every member dies.** It dies at the list-guessing step of Theorem C_t,
against the floor `val(Phi_k) >= 2^(-k)`. By Lemma A, a reference that is not
the A-side branch assignment on the whole of `X_U` agrees with it on a satisfied
defect edge with probability at most `1/2`. So only defect lines whose own
assignment `y_d|_(X_U)` is in the list are covered beyond one half. Each line
has mass `< 2^(-s-1)`, so pushing `D` below `0.105` needs
`t >= 2^(k-l-11)` references. The soundness budget allows only
`t < 2^(k-2l-5)`.

**What survives.**
* **Restricted sources.** Sources whose YES inputs carry no kernel of rank
  `>= k - 2l + O(log(1/gamma'))` that is onto most `X_V`. Hard regular Gap3Lin
  families from PCPs are of this kind, since their equation vectors span. The
  padded transfer of Remark P of the Theorem M node, conditional on DKKMS
  Lemma 5.4, would carry the refutation to them, and the node does not claim
  that transfer.
* **Decoders not losing `1/t`.** Losses `t^(-alpha)` with `alpha < 1` are not
  refuted here. A decoder that does not guess the index needs a different
  analysis from Theorem C_t.
* **Single heavy reference.** This does not apply to value above `0.61`. The
  LS labellings have value near `0.606` to `0.61`, so `gamma > 0.11` is
  untouched.

## Belief change

The held node recorded that, in ev-form, "(List-Str_t) with `t = 2^(O(l))` is
the one remaining selector-free prerequisite", and that LS's labelling
"suggests that it satisfies (List-Str_(2^l)) with small `D`". Both are false.
A-side honest unfolding does not help in ev-form: a reference other than the
branch assignment is right on only half of the new directions, and the number
of branch assignments is `2^(k-l-8)`, not `2^l`.

## Attempts

* **Ev-form list lower bound (2026-09-19, swarm-0917-w15-w15-ugc-pull).**
  Proved Lemma A, Theorem EL and Corollary EL. The artifact checks Lemma A
  exhaustively on `F_2^m`, `m <= 5`. It checks Theorem EL's per-tuple
  inequality exactly in the image model `(l,s) = (3,2), (4,1)` against every
  list of one or two functionals and every list of branch assignments, with
  the best index per `L'`. It also checks the numbers of Corollary EL for
  `8 <= l <= 64`.
