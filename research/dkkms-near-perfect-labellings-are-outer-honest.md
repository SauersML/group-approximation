---
rg: 2
id: dkkms-near-perfect-labellings-are-outer-honest
kind: claim
title: Every labelling of the DKKMS multi-edge 2-to-1 game of value 1 - eta agrees outside mass 370(eta + SD) with the locally honest patchwork of a per-tuple outer labelling of value 1 - 300(eta + SD) and dirt 160(eta + SD), with absolute constants uniform in l once k is large for l
distinct_from:
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that verifies the list-decoding hypotheses for honest encodings of global 3LIN assignments and says nothing about arbitrary labellings; this is a 99 percent structure theorem for every labelling of value near 1, and its output is a per-tuple outer labelling, not a global assignment.
  efficient-branch-selectors-list-decode-honest-outer-labels: that decodes selectors from honest or near-honest witnesses; this proves that every near-1 labelling of the plain DKKMS 2-to-1 game is near-honest in the local patchwork sense, with no selector and no complexity assumption.
  efficient-branch-selector-on-proved-2to1-instances: that is the open selector hole; this is a rigidity theorem about the same instances that feeds the decoders against it and does not by itself mention orientations.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that shows the branch-blind coarsening forgets the Grassmann consistency across codimension-1 subspaces of one L; this is exactly the statement that the uncoarsened game does not forget it at the 99 percent level.
  two-to-two-games-theorem: that is the 1 percent soundness of Khot--Minzer--Safra and needs the Grassmann expansion theorem; this is the 99 percent regime, where a spectral gap of 1/2 for the Grassmann down-up walk and the BLR test suffice, with constants independent of l.
artifacts:
  - experiments/dkkms-rigidity-2026-09-17/check_grassmann_rigidity.py
---

**ESTABLISHED.** Route: `dkkms-near-perfect-labellings-are-outer-honest-proof`.

## Setting

The notation is that of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`.
The instance is the Dinur--Khot--Kindler--Minzer--Safra construction (ECCC
TR16-198, Section 4.2) on a regular 3LIN instance, with parameters `k`, `l` and
`beta = log log k / k`.

* `U` is a legitimate k-tuple, `X_U = F_2^(3k)`, `H_U = Span(x_e : e in U)`,
  and `h_U(x_e) = b_e`.
* `V` is the smoothed set of variables, `X_V <= X_U`.
* An edge of `G_multi` is the output `((U,L),(V,L'))` of the DKKMS edge
  process, restricted to `L meet H_U = {0}` and renormalised.
* A labelling is a pair `(A, B)`. `A` gives each folding class `C` a linear
  `sigma_C : R_C -> F_2`, unfolded at a member as `A(U,L) = (sigma_C)~_U |_L`.
  `B` gives each B-vertex a linear `B(V,L') : L' -> F_2`. The edge accepts iff
  `A(U,L)|_(L') = B(V,L')`.
* The outer game `Phi_k` has `A`-vertices `U` and `B`-vertices `V`, and `rho`
  is the law of `(U,V)`. Its labels are assignments to the variables, which are
  the same thing as linear functionals on `X_U` and `X_V`. The projection is
  `pi_UV(alpha) = alpha|_V` if `alpha` satisfies the equations of `U`, and `⊥`
  otherwise.

Put

```text
SD* := beta sqrt(k) 2^(l+3) + 3 * 2^(l-k).
```

## Statement

**Theorem R.** Let `l >= 3` and suppose that `k` is large for `l`: `2^(l-1) beta <= 1/8`,
`2^(l-k) <= 1/200` and `3k >= l + 2`. Let `(A, B)` be any labelling of `G_multi`
with value `>= 1 - eta`. Then there is an outer labelling `lambda` of `Phi_k`
with the following properties.

1. **Local honesty of the outer labels.** For every `U` outside a set of
   measure `112 eta + 56 SD*`, `lambda_U` satisfies all equations of `U`.
2. **Outer value.**
   `val_(Phi_k)(lambda) >= 1 - 300 (eta + SD*)`.
3. **A-side agreement.**
   `Pr_(edge) [ A(U,L) != lambda_U|_L ] <= 160 (eta + SD*)`.
4. **B-side agreement.**
   `Pr_(edge) [ B(V,L') != lambda_V|_(L') ] <= 210 (eta + SD*)`.

`lambda` is per-tuple, `lambda_U` being the nearest linear functional to the
Grassmann table `L -> A(U,L)`. It is not claimed to come from one global 3LIN
assignment, and it cannot in general (see the heuristic under Consequences).

**Corollary P (patchwork form).** Read each class `C` at a member
`kappa(C) = (U, L)` with `A(U,L) = lambda_U|_L` when one exists, and anywhere
otherwise. Let `hon_kappa(lambda)_C` be the class label whose unfolding at
`kappa(C)` is `lambda_(U_C)|_(L_C)`, and put `hon_kappa(lambda)_(V,L') = lambda_V|_(L')`.
Then:

* `hon_kappa(lambda)_C = sigma_C` for every class with such a member;
* the dirt, i.e. the edge mass whose unfolding of `hon_kappa(lambda)_C` differs
  from `lambda_U|_L`, is `<= 160 (eta + SD*)`;
* `(A, B)` and `hon_kappa(lambda)` agree at both endpoints outside edge mass
  `370 (eta + SD*)`.

**Corollary N (numbers).** If `eta <= 10^(-5)` and `SD* <= 10^(-5)`, then:

* `val_(Phi_k)(lambda) >= 1 - 0.006 >= 15/16`;
* the dirt is `<= 0.0032 <= 1/64`;
* the disagreement mass is `<= 0.0074 <= 1/128`.

`SD* <= 10^(-5)` holds once `log log k / sqrt(k) <= 2^(-l-3) 10^(-5)/2` and
`2^(l-k) <= 10^(-6)`, that is for all `k >= k_0(l)`, where `k_0(l)` is of
order `4^l` up to factors polylogarithmic in `l` and an absolute constant.

## What the proof uses

Everything is proved in the route except one quoted input, DKKMS Lemma 4.9
(the covering property, credited there to Khot--Minzer--Safra). It is applied
at dimension `l - 1`. There are four steps.

* **Spectral gap.** The down-up walk `L_1 > M < L_2` on `Gr(F_2^N, d)` has
  second eigenvalue at most `(2^(d-1) - 1)/(2^d - 1) < 1/2`, for every `N`.
  This follows from an exact recursion between the up-down and down-up walks.
* **99 percent rigidity of linear tables.** Suppose each `L in Gr(F_2^N, l)`
  carries a linear `F[L]`, and the test `L' ; L_1, L_2 > L'` rejects with
  probability `delta`. Then some linear `g` has `Pr_L[F[L] != g|_L] <= 20 delta`.
  The proof takes the plurality on the link of each vector, which the spectral
  gap controls, then BLR.
* **Per tuple.** Two independent extensions `L_1, L_2` of the same `(V, L')`
  disagree on `L'` with probability `<= 2 eta_U`, as in DKKMS Claim 5.5 at the
  99 percent level. Covering puts this within `SD*` of the ideal test.
* **Folding forces the equations.** In a class, `A(U, graph of phi)` differs
  from `A(U,L)` by `h_U o phi`. So a nearest `g` with `g|_(H_U) != h_U` would
  agree with the table with probability at most `2^(-l)` on a pair. The
  nearest functional therefore satisfies `U`.
* **Gluing.** Two distinct functionals on `X_V` agree on a random
  `(l-1)`-space with probability `<= 2^(1-l)`. So all good `U` above `V`
  induce the same `lambda_V`.

## Consequences

* **Local 99 percent rigidity holds.** Corollaries P and N give exactly the
  statement posted on the live bus by the lease holder of
  `efficient-branch-selector-on-proved-2to1-instances` as the OPEN
  prerequisite "dkkms-grassmann-2to1-test-is-locally-99-percent-rigid". Their
  constants are `eta_1 = 10^(-5)` and `zeta_1 = 1/128`, with outer value
  `15/16` and dirt `1/64`. That node is not in this worktree, so it is named
  here only in prose. The extra hypothesis is `k >= k_0(l)`. DKKMS choose
  `k` "large enough so that soundness holds" after `l`, so it is of the same
  kind.
* **For the selector hole.** That sibling analysis says the following. A
  polynomial-time orientation with YES lift value `>= 1 - eta_1` makes the
  underlying 2-to-1 labelling have value `>= 1 - eta_1`. Theorem R then makes
  its A- and B-labels a locally honest patchwork. The high-advantage decoder
  of that sibling lease turns such witnesses into `NP in RP`.
  - Once those nodes land, the selector route
    `rich-2to1-via-branch-selector-on-proved-2to1-instances` is closed at every
    DKKMS parameter point with `k >= k_0(l)`, under `NP not in RP`. The lift
    value would have to stay below `1 - 10^(-5)`, while the hole asks for
    `eta'(eta) -> 0`.
  - Constant-bias selectors with completeness in `(1/2, 1 - 10^(-5))` are not
    touched.
* **Why the survivor (H2-loc) is empty near 1.** A near-1 labelling cannot be
  non-honest inside the Grassmann layer of a constant fraction of tuples. On
  each tuple the table is `20 delta_U`-close to one functional, and folding
  makes that functional satisfy the tuple. Non-honesty can only be patchwork
  across tuples, and patchworks are exactly what the local form of the decoder
  handles.
* **Why global honesty is not claimed.** Heuristically, a labelling that uses
  different near-satisfying assignments on different tuples, switching only
  along the `beta`-resampling of `U -> V -> U'`, has value `1 - O(beta)`. Such
  a labelling is far from every global `hon(a)`. Theorem R allows it.

This neither proves nor refutes UGC, the rich 2-to-1 conjecture or the selector
hole by itself.

## Not covered

* Parameter points with `k < k_0(l)`, and in particular any fixed choice of
  `k` in `R_eta` that DKKMS might make below this threshold. The covering error
  `SD*` is additive and does not shrink with `eta`.
* The KMS 2-to-2 instances, and completeness regimes away from `1`.

## Attempts

* **Global rigidity (2026-09-18).** Asking for agreement with one global
  `hon(a)` fails at rate `beta` (patchwork heuristic above). This node proves
  only the per-tuple form, and the patchwork corollary is what the decoders
  need.
* **Covering worry (2026-09-18).** A first concern was that, given `U`, the
  subspaces `L'` produced by the edge process concentrate on a few
  hyperplane structures of `X_U`, so that the per-tuple test would not be a
  Grassmann test. It is not a problem. Lemma 4.9 at dimension `l - 1` puts
  the law of `L'` within `beta sqrt(k) 2^(l+3)` of uniform, and the rigidity
  lemma is proved for the exactly uniform test in every ambient dimension.
* **Artifact.** `check_grassmann_rigidity.py`, seed 20260918, checks three
  things.
  - The second eigenvalue of the down-up walk on `Gr(F_2^N, d)`, for
    `N <= 7`, `d <= 3`. It never exceeds `u_d`: for example `0.4000 <= 0.4286`
    at `(6,3)` and `0.3280 <= 0.3333` at `(7,2)`.
  - The rigidity ratio `dist / delta` on 140 corrupted linear tables. The
    corruptions are random, second-function-on-a-star, second-function-on-a-
    hyperplane, and star-of-two-points. The ratio is at most `2.28` against the
    proved `20`, and the proof's decoder attains the same distance.
* **Constants (2026-09-18).** The route proves sharper intermediate bounds
  than the statement: A-side `40 eta + 21 SD*`, B-side `205 eta + 107 SD*`,
  outer loss `277 eta + 143 SD*`. The Lemma 2 constant is `C_l <= 19`, with
  BLR over uniform pairs and no loss from conditioning on independence.
  - Folding invariance on `F_2^6` with two equations. In all trials every
    functional violating `h` is `>= (1 - 2^(-l))/2`-far from an invariant
    table, and in the 23 decisive trials the nearest one satisfies `h`.
