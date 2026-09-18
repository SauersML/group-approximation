---
rg: 2
id: bafna-minzer-proof-transfers-to-group-shift-games
kind: route
title: A line-by-line referee of the Bafna--Minzer source finds that every step touching the alphabet is one of the eight group-valid identities of Lemma D, and every other step is host-only or alphabet-size bookkeeping, so Theorems 1.6--1.8 hold for left-shift games over every finite group
target: group-shift-games-easy-on-globally-hypercontractive-graphs
requires:
  - affine-ug-easy-on-globally-hypercontractive-graphs
artifacts:
  - experiments/ugc-bm-group-referee-2026-09-17/check_bm_group_referee.py
  - experiments/ugc-bm-group-referee-2026-09-17/output.txt
---

**Route.** Take the proof of Bafna--Minzer Theorems 1.6--1.8
(arXiv:2304.07284v1, LaTeX source `src/*.tex`, imported through
`affine-ug-easy-on-globally-hypercontractive-graphs`). Substitute the dictionary
of the target claim everywhere: `X_u - X'_u` becomes `X_u^(-1) X'_u`,
`X_v - X_u` becomes `X_v X_u^(-1)`, a global shift `+t` becomes right
multiplication by `t`, `X_u = 0` becomes `X_u = e`, and `Sigma = Z_q` becomes
`A`. The referee below checks every line of the source. Each line falls into
one of three classes:

* **(L)** an identity about the alphabet. Each such line is one of items 1--8
  of Lemma D in the target claim, and those are proved there for every finite
  group.
* **(H)** a statement about the host graph alone: functions on `V(G)`, their
  hypercontractivity, the structure and edge-covering theorems, subcube
  expansion. These never mention labels, so they are imported unchanged.
* **(B)** alphabet-size bookkeeping. `|Sigma|` or `log |Sigma|` appears only
  as a number, in degree bounds, in averaging over `s`, and in the
  Raghavendra--Tan conditioning count. It becomes `|A|` with no other change.

No line uses commutativity: no `s + s' = s' + s`, no composition of two shift
partitions, no characters of the alphabet. The only Fourier analysis in the
source is on the host (`structure.tex`, the spectrum of `C_(n, l, alpha)`),
which is class (H).

The authors state the same modularity themselves (`generalization.tex`,
lines 98--100): "the elimination of correlations and conditioning are
completely generic, and the rounding procedure only hinges on the constraints
being affine." The referee confirms that "affine" enters only through the
eight items of Lemma D.

## The referee

Line numbers refer to the arXiv LaTeX source of 2304.07284v1. "Item k" is
item k of Lemma D in the target claim.

| source location | what it does | class | group transfer |
|---|---|---|---|
| `prelims.tex` 26--62 | SoS relaxation (1) of UG, axioms `A_I` | L | Booleanity and partition of `X_(u,a)` are label-set facts; constraint polynomials `sum_a X_(u,a) X_(v, b a)` keep degree 2 |
| `prelims.tex` 63--136, 396--456 | pseudoexpectations, reweighing, conditioning, independent samples `mu_1 x mu_2` (Fact `fact:indep`) | B | generic over any finite label set |
| `prelims.tex` 137--280 | SoS Holder, Schweighofer black box, step approximation `p_(beta,nu)`, Fact `fact:bdd-markov` | H | real polynomials of `val_u in [0,1]`; no labels |
| `prelims.tex` 457--465, Fact `fact:z-vars` | shift variables `Z_(u,s)`; partition; crossing edges violate | L | items 1, 2 |
| `prelims.tex` 481--511, Definition `def:shift-symm` | symmetrization, shift-symmetry properties | L | items 3, 4 |
| `affine_johnson.tex` 63--117, Definition `def:shift-partition` | `Phi_(beta,nu) = sum_s (E_u Z_(u,s) p_u p'_u)^2` | L | same formula with group `Z_(u,s)`; invariance is item 8 |
| `affine_johnson.tex` 118--146, Algorithm `alg:j` | main loop: solve SoS, symmetrize, correlate, condition, round, iterate | L+B | item 3 for the symmetrization step; the rest is control flow |
| `affine_johnson.tex` 157--186, Definition `defn:local-dist` | local distributions of `Y_(u,v) = (X_u, X_v, p_u, p_v)` | B | finite random variables with values in `A^2 x {0,1}^2` |
| `affine_johnson.tex` 187--234, Algorithm `alg:low-ent-restated` | Condition&Round: condition on `X_u = 0`, round independently | L | condition on `X_u = e`; item 6 |
| `affine_johnson.tex` 235--265, Algorithm `alg:j-partial` | SubRound on a subgraph | L | restriction of a left-shift game to a subgraph is a left-shift game |
| `affine_johnson.tex` 413--444, Definition `def:res-shift` | shift potential restricted to a subgraph | L | same formula, item 1 |
| `affine_johnson.tex` 445--521, Theorem `thm:structure-johnson`, Lemma `lem:structure-fs-j` | global hypercontractivity applied to `F_s(u) = Z_(u,s) p_u p'_u` | H | `F_s` enter only as degree-bounded functions `V -> R` with `sum_s F_s <= 1` (item 1) |
| `affine_johnson.tex` 522--543, 705--808, Lemmas `lem:ragh-tan-appln`, `lem:ragh-tan` | Raghavendra--Tan global-correlation reduction | B | conditions on `O(log #Sigma / (p tau))` variables; `log #A` instead |
| `affine_johnson.tex` 544--645, Lemma `lem:sp-j-restated` | find a subcube with large potential | H+L | host argument on the `F_s`; the potential identities are items 1, 8 |
| `affine_johnson.tex` 650--666, Claim `claim:subcube-expanse` | subcube expansion | H | host only |
| `affine_johnson.tex` 667--704, Claim `claim:potentials` | restricted potential `>= Phi restricted to C - 4 nu` | L | uses only that `Z_(u,s)` is a partition indicator (line 688), item 1 |
| `affine_johnson.tex` 809--906, Lemma `lem:correlation` | conditioning on `E` does not correlate local tuples | B | mutual information and TV of finite random variables |
| `rounding.tex` 1--53, Lemma `thm:round-j` | large `Phi` implies Condition&Round succeeds | L | line 45, "We note that `Psi(mu) = Psi(mu^sym)`", is item 3; the BBKSS Lemma 3.6 step is item 6 |
| `rounding.tex` 126--136, eq. `relating-potential` | `sum_s Z_(u,s) Z_(v,s) = Ind[X_u - X_v = X'_u - X'_v]` | L | item 5 |
| `rounding.tex` 137--156 | error term `<= 2 TV + 1/#V` | B | sums over label quadruples in `A^4` |
| `rounding.tex` 157--181 | main term: split over `s`, Fact `fact:bdd-markov`, AM-GM, Cauchy--Schwarz, gives `Psi(mu_1) + Psi(mu_2)` | L+B | split over `s = X_v X_u^(-1)`; the swap `X_u - X_v = s` versus `X_v - X_u = s` becomes the bijection `s -> s^(-1)`; the rest is real inequalities |
| `rounding.tex` 182--261 | commented out (old symmetrization text) | -- | not part of the proof |
| `low-comp.tex` 31--280, Theorem `thm:edge-covering-restated`, Claim `claim:dense-subcubes` | edge-covering theorem | H | host only |
| `low-comp.tex` 117 | "any edge that crosses between parts in the shift-partition must be violated by at least one of `X` or `X'`" | L | item 2 |
| `low-comp.tex` 281--390, Lemma `lem:sp-j-low-comp`, Claim `claim:val-intersection-restated` | low-completeness main lemma; parameters at line 387 | H+B | `nu = c^4 / (#Sigma^2 l^(O(r)))`, `p = c^2/(4 r l^i #Sigma)`, `deg(mu) = l^(poly(#Sigma l^r / c))`: all numeric in `#Sigma` |
| `low-comp.tex` 391--end, Theorem `thm:main-johnson-arbit-comp` | assembly of Theorem 1.6 | B | `#Sigma -> #A` |
| `missing-proofs.tex` 1--31, Lemma `lem:subroutine-restated`, Algorithm `alg:partial` | iteration: "Randomize the constraints on edges incident on `R_j`" (line 22) | L | uniform `b_e in A`, item 7 |
| `missing-proofs.tex` 32--95, Claims `claim:it-drop`, `claim:chernoff`, `claim:it-val` | value accounting; "the probability that `F` satisfies `e` is `1/k`" (line 54) | L+B | item 7, then Chernoff on real variables |
| `missing-proofs.tex` 96--end, Claims `claim:bool`, `claim:silly_sos` | SoS facts about Boolean and bounded variables | B | label-free |
| `structure.tex` all | SoS certificate of expansion in `J(n, l)`, the spectrum of `C_(n, l, alpha)` | H | host only; the characters are those of the host, not of the alphabet |
| `generalization.tex` all | Theorems 1.7, 1.8 for Grassmann and HDX hosts | H | swaps the host structure theorem; the label side is reused verbatim (lines 96--104) |

In the table, `#Sigma` and `#A` denote the sizes of the alphabets.

## Why class (H) lines never see the group

The host side of the proof works only with real functions on `V(G)`:

* `F_s(u) = Z_(u,s) p_u p'_u`, for `s` in the alphabet;
* the local values `val_u`;
* indicator functions of subcubes, subspaces and links.

The structure theorem (`thm:structure-johnson`) and the edge-covering theorem
(`thm:edge-covering-restated`) are statements about one real function
`f : V -> [0, 1]` at a time, with SoS certificates in the Boolean variables
`X_(u,a)`. They are applied to each `F_s` separately.

Afterwards, the proof uses only two facts about the family `(F_s)`:

* `sum_s F_s(u) <= 1`, which is item 1;
* `sum_s` appears as a finite sum with `#Sigma` terms.

Neither depends on the group law.

## Why class (L) lines are exactly Lemma D

Every place where the labels are combined algebraically has one of these
forms:

1. a difference of two labels at one vertex (`Z_(u,s)`);
2. a difference of two labels at two vertices (`X_v - X_u`);
3. a global shift;
4. a random constraint.

The table lists each occurrence. Form 1 always goes through items 1, 2, 5
or 8. Form 2 goes through items 4, 5 or 6. Form 3 goes through items 3 or 8.
Form 4 goes through item 7.

The only nontrivial choice is which side each quotient is taken on. The rule
is: invariant under common left shifts for the potential, and invariant under
right translation for the symmetry. Items 2 and 5 are forced by the first
requirement. Items 3, 4 and 6 are forced by the second. The artifact's control
C7 shows that the other side fails.

## Standard of proof, and the caveat for Theorems 1.7 and 1.8

The transfer is black-box on the host side. The group version therefore holds
to exactly the standard of the imported theorem, and no higher.

For Theorem 1.6 (`J(n, l, alpha l)`), the source contains a complete proof,
and the referee above covers all of it.

For Theorems 1.7 (Grassmann) and 1.8 (HDX), the source itself gives only
sketches of the host side. `generalization.tex` line 246 says: "One can
similarly also get the stronger edge-covering theorem for HDXs (analogous to
Theorem~\ref{thm:edge-covering-restated}) and we omit the details here."
`affine-ug-easy-on-globally-hypercontractive-graphs` imports those theorems by
citation, so this route inherits exactly that status. Any gap in those
sketches is a gap on the host side. It would affect the `Z_q` theorem and the
group theorem equally, and it is never alphabet-specific.

## Numeric check of the alphabet steps

`check_bm_group_referee.py` works over `S_3` and `Q_8`. It uses exact rational
arithmetic, real distributions on left-shift games on `K_4`, `beta = 2/3`, and
`p = Ind[val >= beta]` (so `nu = 0`). It checks:

* **C1.** `Psi(mu) = Psi(mu^sym)`. This is `rounding.tex` line 45 in group
  form.
* **C2.** Condition&Round on `mu^sym` is at least `Psi(mu^sym)` (BBKSS
  Lemma 3.6). The slack is `>= 0.07` over 12 trials per group.
* **C3.** `Phi` is invariant under symmetrization and under independent right
  translations of `X` and `X'`.
* **C4.** `lem:relating-ent-j` in group form, under a random reweighting `E`:
  - the expansion identity of eq. `relating-potential` holds exactly;
  - the main term equals `Phi(mu_1 x mu_2)` and is at most
    `(Psi(mu_1) + Psi(mu_2)) / (2 beta^2)`;
  - the full bound with `2 delta + 1/#V` holds.
* **C5, C6, item 5.** The crossing-edge fact, the `1/#A` randomization, and the
  identity of item 5, over the whole group.
* **C7 (control).** With the wrong-sided quotient `X'_u X_u^(-1)`, the
  crossing-edge fact fails: on 108 of 216 triples for `S_3`, and on 192 of 512
  for `Q_8`. The wrong-sided form of item 5 also differs.

Real distributions are a special case of pseudodistributions, so these checks
test the algebra of each step. They do not test SoS degree bookkeeping, and
that bookkeeping is class (B).

## Conclusion

Every line of the Bafna--Minzer proof is class (L), (H) or (B). Class (L)
lines are Lemma D, which is proved for every finite group in the target claim.
Class (H) lines are unchanged. Class (B) lines change only `#Sigma` to `#A`.

So Theorems 1.6--1.8 hold for left-shift games over any finite group `A`,
with `D = l^(poly(#A l^(1/c)))`. The standard of proof is that of the imported
theorems. This establishes
`group-shift-games-easy-on-globally-hypercontractive-graphs`.
