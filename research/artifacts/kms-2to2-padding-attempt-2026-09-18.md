# Padding the DKKMS right alphabet into KMS Definition 1.3: attempted route (2026-09-18)

Date: 2026-09-18, swarm-0917, calibrator lane. Target claim:
`kms-2to2-instances-are-padded-dkkms-selector-lecs` (OPEN).

**Status: attempt, not a route.** This file was posted as the route
`kms-2to2-padding-selector-membership-proof` with

    target: kms-2to2-instances-are-padded-dkkms-selector-lecs
    requires:
      - efficient-branch-selectors-list-decode-honest-outer-labels
      - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
      - two-to-two-games-theorem

titled "Read the Khot--Minzer--Safra paper for its instances, find none, pad the
DKKMS right alphabet with one free bit to land in Definition 1.3, and note that
(E) and (M) never mention a label so they transport to every presentation".
All three referee lenses (2026-09-18) refuted the claim **as stated** at Step 0,
the citation step: the enumeration of TR18-006's cited sources omits `[12]` =
Khot--Minzer--Safra, *On Independent Sets, 2-to-2 Games and Grassmann Graphs*,
ECCC TR16-124, which **does** construct a 2-to-2 game (its Definition 1.4,
Theorem 1.8), already single-alphabet and needing no padding. The identification
of Theorem 1.4's instances with `G_folded` is therefore unfilled, and (E)
`tau = 2^(l-1-2k)` and (M) `K = 1` are not established for the proved family.
Full reasons are in the `## Attempts` section of the claim file. The claim was
returned to OPEN and this file was demoted out of the compiled graph, so it
establishes nothing.

What is not in dispute: Steps 1--3 below are correct **about the padded
bipartite game `G_pad` constructed here** -- `T` is linear and invertible, the
relation is exactly 2-to-2 and lands in KMS Definition 1.3, `OPT` is unchanged,
the transport of (E) and (M) along a per-vertex alphabet injection is sound, and
the "one decoder for all `c`" use of Step 0 of
`efficient-branch-selectors-list-decode-honest-outer-labels-proof` is
legitimate. The replay
`experiments/kms-2to2-padding-2026-09-18/check_kms_2to2_padding.py` prints all
four structural checks green. What is not kept is the claim that `G_pad` is the
proved 2-to-2 family, and hence the advertised consequence that the decoding
theorem applies verbatim to the instances behind `two-to-two-games-theorem`.

Whoever picks this up needs: ECCC TR16-124 read for its actual instance family,
and (E)/(M) redone for the A--A presentation with its own edge law, its
`1`-to-`1` constraints, its transitivity requirement and its `V ⊆ U`
subsampling.

Two further cautions on the text below. Step 4 puts in quotation marks two
sentences attributed to
`efficient-branch-selectors-list-decode-honest-outer-labels-proof` that do not
occur in that file; they are paraphrases, substantively right about its Step 0
but not verbatim. And in `G_pad` the padded bit `c` occurs in no constraint at
all, so the 2-to-2 structure is inert by construction -- Step 4's conclusion
that the 2-to-2 shape buys a selector nothing is read off a degenerate game.

Artifacts: `experiments/kms-2to2-padding-2026-09-18/check_kms_2to2_padding.py`,
`research/artifacts/kms-2to2-instance-provenance-2026-09-18.md`.

---

Notation is that of the target claim and of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`. Quotations are
from the two ECCC PDFs, collected with page references in
`research/artifacts/kms-2to2-instance-provenance-2026-09-18.md`. **KMS** is
ECCC TR18-006, **DKKMS** is ECCC TR16-198. All credit for the constructions and
theorems quoted is theirs.

## Step 0: the citation step

The 56-page KMS text contains no reduction, no constraint graph and no
instance. Its content is the Grassmann Expansion Hypothesis (Theorem 1.8,
restated as Theorem 2.4) and its proof. The paper says where its instances come
from:

* Abstract: "This completes the proof of the 2-to-2 Games Conjecture (albeit
  with imperfect completeness) as proposed in [12, 3], along with a
  contribution from [2]."
* Appendix C: "In [3], the authors formulated a Linearity Testing Hypothesis
  and showed that it implied the 2-to-2 Games Conjecture (with imperfect
  completeness)."
* "[3] Irit Dinur, Subhash Khot, Guy Kindler, Dor Minzer, and Muli Safra.
  Towards a proof of the 2-to-1 games conjecture? Electronic Colloquium on
  Computational Complexity (ECCC), 23:198, 2016."

So the game is the `G_folded` of DKKMS Section 4.2: "In this section we
construct the instance of the 2-to-1 game `G_folded`."

## Step 1: the shape mismatch, and the map that fixes it

DKKMS, Constraints, page 23: "We let `Sigma_A = {0,1}^l` and
`Sigma_B = {0,1}^(l-1)`. ... The constraint between `(U,L)` and `(V,L')`
accepts pairs `(sigma,sigma')` iff `sigma|_(L') = sigma'`. It is clear that
this is a `2 : 1` constraint."

KMS Definition 1.3 wants one alphabet `F_2^l` on both sides and constraints
`T_ij x_i (+) T'_ij x_j in {b_ij, b'_ij}` with `T_ij, T'_ij` invertible. So a
presentation step is needed and neither paper writes it. Define `G_pad` by
padding the right alphabet with one free bit:

```text
Sigma_B^pad := Fun(L') x F_2,
constraint(C,(V,L')) accepts (sigma,(sigma',c))  iff  A_sigma(U,L)|_(L') = sigma'.
```

**(a) The folded constraint is exactly 2-to-1.** DKKMS folds by aggregation:
"a constraint between `C` and `(V,L')` accepts a pair of assignments
`(sigma,sigma')` if the unfolding of `sigma` satisfies all of the constraints
between members of `C` and the assignment `sigma'`. The weights are summed up
as well." Every member `(U,L)` of the class carrying an edge to `(V,L')` has
`L' subseteq L`, so Claim 4.3 with `D = L'` gives
`A(U_1,L_1)|_(L') = A(U_2,L_2)|_(L')`: the aggregated conditions coincide, and
the aggregate is exactly the single 2-to-1 condition. Unfolding
`Fun(R) -> Fun(L)` is a bijection (Step 1 of `dkkms-selector-membership-proof`),
so each fiber has exactly two elements. Artifact Part A checks this
exhaustively for `k = 2`, `l = 2` and `l = 3`: 161280 and 2580480 triples
`(L_1,L_2,L')`, 645120 and 20643840 label checks, 0 splits.

**(b) `G_pad` is an instance of Definition 1.3.** Take a basis
`v_1,...,v_(l-1)` of `L'`, extend by `v_l = x` to a basis of `L`, and use the
folding decomposition `z = r(z) + y(z)` with `r(z) in R`, `y(z) in H_U` of
Definition 4.2. By that definition `A_sigma(U,L)(z) = sigma(r(z)) + h_U(y(z))`.
Identify `sigma in Fun(R)` with its coordinates on a basis of `R`, and
`tau in Sigma_B^pad` with `(sigma'(v_1),...,sigma'(v_(l-1)), c)`. Then

```text
(T sigma)_i := sigma(r(v_i)),   T' := I,   b_i := h_U(y(v_i)),   b' := b + e_l,
```

and the constraint `A_sigma(U,L)(v_i) = sigma'(v_i)` for `i < l` with `c` free
reads exactly `T sigma + tau in {b, b'}`. `T` is linear because `sigma` is, and
invertible because `r` maps a basis of `L` to a basis of `R`; and `b != b'`, so
the constraint is 2-to-2 and not unique. Artifact Part B checks all of this
over 107520 quadruples `(b, R, L, L')` at `k = l = 2`: `T` linear, `T`
invertible, `b != b'`, the accepted set equal to the linear set, and every left
and right label in exactly two accepted pairs.

**(c) No value moves.** The padded bit appears in no constraint, so
`OPT(G_pad) = OPT(G_folded)`, and for every labelling `h` of `G_folded` the
best orientation-lift value of its padded extensions equals the best
orientation-lift value of `h` (artifact Part D, exhaustive enumeration of
orientations on 200 random abstract games).

## Step 2: (E) and (M) transport, because they never mention a label

In the LEC definition of
`efficient-branch-selectors-list-decode-honest-outer-labels`:

* **(E)** constrains the conditional law of `x_e` given `(w_e, a_e)`;
* **(M)** compares the law of `a_e` under `mu` with `rho_A`.

Both are functions of the pair (constraint distribution `mu`, annotation
`e -> (w_e, a_e, x_e)`) alone. The padding changes neither: `G_pad` has the
same constraints with the same weights and the same annotation, only larger
label sets at the `B`-vertices. Hence, by Steps 3 and 4 of
`dkkms-selector-membership-proof`,

```text
tau = 2^(l-1-2k)      (x_e uniform on X_U \ (L' + H_U), m = 3k),
K   = 1               (the U-marginal of mu is uniform on legitimate k-tuples).
```

The same argument gives the stronger, presentation-free statement in the target
claim: **(E) and (M) hold for every instance obtained from `G_folded` by a
per-vertex alphabet injection with the constraint relation transported.** So
the conclusion does not depend on which map from `G_folded` to Definition 1.3
KMS footnote 2 has in mind.

The remaining LEC data are unchanged as well: the outer game is DKKMS's
`Phi_k`, `m = 3k`, and `|Sigma_w| = |Fun(L') x F_2| = 2^l <= 2^l`, which is the
bound the decoding theorem uses. So `p = gamma^3 2^(-l-2)` is the same number
as in the 2-to-1 case.

## Step 3: (B) for every free bit and every orientation

Let `a` be an assignment, `c` a bit at every `B`-vertex, and
`hon_c(a)_C = a|_(R_C)`, `hon_c(a)_(V,L') = (a|_(L'), c_(V,L'))`. Let `o` be
any orientation of `G_pad` and `g_e(sigma',c) = A_(o_e(sigma',c))(U,L)(x_e)`.

Suppose `U` is clean for `a`, so `h_U = a|_(H_U)`, and suppose `hon_c(a)`
satisfies the oriented `e`. Then `hon_c(a)_C = o_e(hon_c(a)_(w_e))`, i.e.
`o_e(a|_(L'), c_(w_e)) = a|_R`, hence by Step 5 of
`dkkms-selector-membership-proof`

```text
g_e(hon_c(a)_(w_e)) = A_(a|_R)(U,L)(x_e) = <a, x_e> = <lambda^a_(a_e), x_e>.
```

Therefore
`Pr_e[g_e(hon_c(a)_(w_e)) = <lambda^a_(a_e), x_e>] >= val_(G_pad,g)(hon_c(a)) - eps_out(a)`
for every `c`, with `eps_out(a) <= 2k eps_3` as in the 2-to-1 case (DKKMS
legitimacy: "the fraction of `U` that are not legitimate is negligible, i.e.
`O(k^2/|X|)`"). Artifact Part C runs every orientation of the block, including
the two non-matching ones, both bits `c`, all `2^(3k)` assignments and all
`2^k` right-hand sides at `k = l = 2`: 13762560 clean satisfied cases, 0
failures; on dirty `U` the identity fails in 10321920 of 82575360 cases.

## Step 4: one decoder for all `2^(|B|)` padded honest encodings

A 2-to-2 selector cannot be converted into a 2-to-1 selector: the natural
conversion `o'_e(sigma') := o_e(sigma', c_(w_e))` reads the witness's bits `c`,
which the selector does not have. So the decoding theorem is applied to `G_pad`
itself. That is legitimate because, quoting
`efficient-branch-selectors-list-decode-honest-outer-labels-proof`, "**Step 0**
builds the decoder from `G`, `g`, `mu` and the annotation alone. It never
evaluates `hon`", and "**Step 1** uses the witness `(lambda, hon(lambda))` and
(B) only to obtain
`Pr_e[g_e(h_(w_e)) = <lambda_(a_e), x_e>] >= 1/2 + gamma`. From that inequality
alone it derives `P >= gamma`."

So: for each fixed `c`, the data `(Phi_k, G_pad, hon_c, annotation)` is an LEC
satisfying (B) up to `eps_out`, (E) with `tau = 2^(l-1-2k)` and (M) with
`K = 1`; and the decoder built in Step 0 is the *same* algorithm for every `c`,
because it does not see `hon`. Hence Theorem 1 of that claim fires as soon as
*some* pair `(a, c)` gives the branch inequality, which is exactly the
hypothesis of the target claim's theorem.

## Step 5: parameters and the conclusion

Identical to Step 7 of `dkkms-selector-membership-proof`, with the same outer
game, the same soundness (DKKMS "Lemma 5.4 (Soundness of Outer PCP, [18]). If
every assignment for `(X, Eq)` satisfies at most `s*` fraction of the
equations, then the players have no strategy that succeeds with probability
better than `eps = exp(-k/exp(ql))`.") and the same NP-hard source (DKKMS
"Theorem 4.1. There is an absolute constant `s* < 1` such that for every
constant `eps > 0`, Gap3Lin`(1-eps, s*)` is NP-hard on regular instances.").
With `p = (gamma/2)^3 2^(-l-2)`, `2^(l-1-2k) <= gamma/8`, `eps_k < p^2/8` and
`eps* = 2k eps_3 <= min(gamma/2, p^2/8)` one gets `c_0 >= 3p^2/4` and
`s < c_0/2`, so a selector with the stated honest completeness and
inverse-polynomial confidence puts regular `Gap3Lin(1-eps_3, s*)`, hence NP, in
RP. Near-honest witnesses are absorbed exactly as there. `square`

## What this does and does not settle

It settles membership: the proved 2-to-2 instances satisfy (E) and (M) with
`tau = 2^(l-1-2k)` and `K = 1`, under the DKKMS folding convention, and (B) up
to the dirty mass `k eps_3`. It does not settle
`efficient-branch-selector-on-proved-2to1-instances`, whose only survivor
remains the non-honest witness H2,
`view-local-selectors-beat-one-half-through-non-honest-witnesses`.
