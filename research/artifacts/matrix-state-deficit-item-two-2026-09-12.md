# The strict deficit restates emptiness in both scopes

Lane `w7-matrix-state-deficit`, 2026-09-12. Verification requested from `w4-vf-linear-b`.

It supports:
- `ternary-anti-central-matrix-state-defects-have-a-strict-deficit` (new, OPEN);
- the routes `matrix-state-deficit-gives-nonpositive-unit-class`, `nonpositive-unit-class-makes-matrix-state-deficit-vacuous`,
  `rank-kill-makes-ternary-strict-deficit-vacuous` and `matrix-state-strict-deficit-restricts-to-rank-functions` (new);
- Attempts entries on `ternary-anti-central-disjoint-defects-have-a-strict-deficit`,
  `anti-central-weakly-finite-images-carry-rank-functions` and `rank-condition-rings-carry-sylvester-rank-functions`;
- equivalence and literature lines on `ternary-rank-kill-via-anti-central-defect-deficit` and
  `rank-condition-rings-have-weakly-finite-images`.

Sources, read on main (tips `d54fa7120` to `11c6d1a50`):
- [C3] `research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md`;
- [SEP] `research/artifacts/two-root-certificates-separate-2026-09-12.md`;
- [SG] `research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md`;
- the nodes named below.

## 0. Summary

**The question.** Item 2 of `ternary-anti-central-disjoint-defects-have-a-strict-deficit`, for anti-central matrix
states.
- (a) Build a violator on the weakly finite image `W` of `S_-`, and say which relations it uses.
- (b) Or prove item 2 from relations that no socle-type state can break.
- (c) Does `D` have a nonzero idempotent minor over `W`?
- (d) Is any ring known to have the rank condition but no Sylvester rank function?

**Answers.**
1. **The deficit is a restatement in both scopes (Theorem 2.2).**
   - Over `A_S` the target is equivalent to `A_S = ∅`, which is the kill claim
     `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`.
   - Over `A_mat` it is equivalent to `A_mat = ∅`, which is failure of the rank condition on `S_-`, the
     counterexample `ternary-anti-central-unit-class-is-nonpositive`.
   - In each scope the forward direction is the minimizer argument and the converse is vacuity. The two
     scopes differ by (U1).
2. **(a) The violator is the minimizer (Proposition 3.1).** If `S_-` has the rank condition, a minimizer `d_0` of
   `d(D)` over `A_mat` factors through the largest weakly finite image `W`, and it violates the target for every
   `theta < 1`.
   - Wherever item 1 holds, item 2 fails with `d_0'(D) >= d_0(D)`.
   - The violation is [C3] Theorem 3.1.2 at `k = 1`, read at a minimizer. It uses no nilpotency index, no
     Frobenius step and no socle computation.
   - A violator on `W` exists iff `W != 0`, and whether `W != 0` is the open counterexample question.
3. **Socle-type states test only upper bounds (Remark 3.2).** [SEP] Example 3.3, pulled back to
   `<x_12(1), x_23(1)>`, gives `d(D) = 1 > 2/3` there. It breaks `c_3 <= 2/3`, which is not part of the target.
   It is not a state on `S_-`, and it does not reach item 2.
4. **(b) A proof is a finite certificate (Proposition 4.1).** Proving items 1–2 over `A_mat` is the same as
   exhibiting `XY = I_n` over `S_-`, with `X` of size `n x (n-1)`. No matrix state breaks such an identity. So (b)
   is the counterexample itself, not a step toward it.
5. **(c) Not decided (Section 5).**
   - `D` has a nonzero idempotent minor iff `WD` contains a nonzero idempotent.
   - For every quotient `W` of `S_-`, either `WDW = W`, so `I_1 <~ D^((+)k)` for some `k`, or `W/WDW` is nonzero
     and fails the rank condition.
   - Over `S_-` itself the second case holds.
6. **(d) No example found; the question is posed as open (Section 6).** Hung–Li (arXiv:2201.01432) ask exactly this
   (Question 3.4), note a positive answer for von Neumann regular rings, and ask the stably finite form (Question
   3.5). So `rank-condition-rings-carry-sylvester-rank-functions` is their Question 3.4. Two papers attribute Theorem
   C (`rank-condition-rings-have-weakly-finite-images`) to Malcolmson.

## 1. Setting

The notation is that of [C3] Section 1 and [SEP] Section 1.
- `G = L_(F_3)(1,2)^x` and `eps_- = 2(1 - [z])`.
- `D = N_23 N_12`, `D_A = F_3[iota_A](D)` and `Q_B = F_3[iota_B](eps_-)`.
- `A_S` is the set of anti-central Sylvester matrix rank functions on `F_3[G]`, and `A_mat` the set of anti-central
  matrix states. `A_S ⊆ A_mat`.

A *configuration* is a pair of disjoint nonempty proper cylinders `A`, `B` with proper union. For `d` in `A_mat`,
put `h(d) = d(Q_B D_A)`. When `h(d) > 0`, put `d'(X) = d(F_3[iota_B](X) Q_B D_A)/h(d)`.

**The target in scope `S`** (`S = A_S` or `S = A_mat`). There is `theta < 1` such that every `d` in `S` and every
configuration satisfy:
1. `d(D_A D_B) > 0`;
2. `d'(D) <= theta d(D)`.

For `A_S` this is `ternary-anti-central-disjoint-defects-have-a-strict-deficit`. For `A_mat` it is
`ternary-anti-central-matrix-state-defects-have-a-strict-deficit`.

**Facts used.** They come from [C3] Theorems 2.1 and 3.1 for `A_S`, and from [SEP] Theorem 2.3
(`two-root-gate-lower-bounds-hold-for-matrix-states`) for `A_mat`.
- (F1) `S` is compact. When it is nonempty, `c = min {d(D) : d in S}` is attained and positive.
- (F2) If `h(d) > 0`, then `d'` lies in `S`.
  - `Q_B D_A` commutes with `F_3[iota_B(G)]`: `D_A` because the cylinders are disjoint, and `Q_B` because
    `tau_B = iota_B(z)` is central in `iota_B(G)`. So `d'` is a matrix state (a rank function when `d` is one).
  - `d'(eps_-) = d(Q_B Q_B D_A)/h(d) = 1`.
- (F3) `d(D_B Q_B D_A) >= c h(d)`. This is [C3] 3.1.2 at `k = 1`.
- (F4) `h(d) = 0` forces `d(D_A D_B) = 0`. This is [C3] 3.1.4 at `k = 1`.
- (F5) `A_mat` is nonempty iff `S_-` has the rank condition, iff `(K_0(S_-), [eps_-])` has a state
  (`sylvester-rank-functions-iff-no-triangular-certificate` item 2, [SEP] Theorem 2.3).

## 2. The target is emptiness

**Lemma 2.1 (minimizers violate).** Suppose `S` is nonempty, and let `d_0` in `S` attain `c`. Then at every
configuration, either item 1 fails at `d_0`, or `d_0'(D) >= d_0(D)`. So `d_0` violates the target for every
`theta < 1`.

*Proof.* Suppose item 1 holds at `d_0`. By (F4), `h(d_0) > 0`, so `d_0'` lies in `S` by (F2). By minimality,
`d_0'(D) >= c = d_0(D)`. Since `d_0(D) > 0` by (F1), `d_0'(D) > theta d_0(D)` for every `theta < 1`. QED

**Theorem 2.2 (restatement).**
1. The target holds in scope `A_S` iff `A_S = ∅`, that is, iff
   `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` holds.
2. The target holds in scope `A_mat` iff `A_mat = ∅`, iff `S_-` fails the rank condition, iff
   `ternary-anti-central-unit-class-is-nonpositive` holds. By Theorem C this is also
   `ternary-anti-central-summand-has-no-weakly-finite-image`.

*Proof.*
- **Emptiness gives the target.** If `S = ∅`, the target holds vacuously with any `theta`.
- **The target gives emptiness.** If `S` is nonempty, Lemma 2.1 gives a violator.
- **Part 1.** `A_S = ∅` is the first equivalent form of the kill claim.
- **Part 2, first equivalence.** This is (F5).
- **Part 2, second equivalence.**
  - No state on `(K_0(S_-), [eps_-])` gives `k[eps_-] <= 0`, by part 2 of
    `anti-central-state-obstruction-equals-stable-finiteness`.
  - Conversely, `k[eps_-] + [Q] = 0` with `k >= 1` leaves no state, because `k + s[Q] = 0` is impossible.
  - A matrix state gives a state. It is additive on idempotent matrices, and Murray–von Neumann equivalent
    idempotents are mutual minors: `e = ab` and `f = ba` with `a = eaf` and `b = fbe` give `e = afb` and `f = bea`.
  QED

**Corollary 2.3 (what separates the scopes).**
- **Restriction.** The target in scope `A_mat` gives the target in scope `A_S` with the same `theta`. This holds
  because `A_S ⊆ A_mat` and `d'` has the same formula in both scopes.
- **The converse.** It follows from (U1) (`ternary-anti-central-states-give-sylvester-rank-functions`). The
  counterexample is the kill claim together with (U1)
  (`ternary-counterexample-from-rank-kill-and-state-realization`), and it implies both.
- **Neither scope turns the deficit into a reduction.** A proof of item 2 at every `d` proves emptiness. Its use is
  as the local, quantitative form such a proof would aim at. [SG] Section 4.1 says the same of the binary claim.

**Remark 2.4 (item 2 alone).** Suppose item 2 holds wherever `h(d) > 0`, with no item 1. In either scope, either
`S = ∅`, or every minimizer has `h(d_0) = 0`, and then `d_0(D_A D_B) = 0` at every configuration, by the proof of
Lemma 2.1 and (F4). So the content is in positivity.

## 3. (a) The violator on `W`

**Proposition 3.1.** Suppose `S_-` has the rank condition. Let `J` be the intersection of all ideals `I` of `S_-`
with `S_-/I` weakly finite, and put `W = S_-/J`. So `J = J_omega(S_-)`, the smallest ideal with weakly finite quotient
(`weakly-finite-reflection-ideal-detects-weakly-finite-images`). This `W` is not the quotient of Theorem C, which
is by a maximal ideal among those with rank-condition quotient and is a further image of `W`. Below, `W` always
means `S_-/J_omega`.
1. `W` is the largest weakly finite image of `S_-`, and it is nonzero.
2. A minimizer `d_0` over `A_mat` descends to a matrix state on `W`, and it violates the target for every
   `theta < 1`. Every value in items 1–2 is computed in `W`.
3. A violating matrix state on `W` exists iff `W != 0`, iff `S_-` has the rank condition.

*Proof.*
1. `S_-/J` embeds in the product of the `S_-/I`, and products and subrings of weakly finite rings are weakly finite.
   Theorem C gives a nonzero weakly finite image, and `W` maps onto it.
2. `d_0(eps_+) = 0`, so `d_0` is a matrix state on `S_-`. By [SEP] Lemma 2.1, `S_-/ker d_0` is weakly finite. So
   `J ⊆ ker d_0`, and `d_0` descends (`two-root-gate-lower-bounds-hold-for-matrix-states` item 1). Lemma 2.1 gives
   the violation.
3. A matrix state on `W` pulls back into `A_mat`. If `W = 0`, then `S_-` fails the rank condition by Theorem C, and
   `A_mat = ∅` by (F5). QED

**Which relations it uses.** The violation is minimality together with (F1)–(F4). In `W` these use only:
- **commutation:** `iota_A(G)` and `iota_B(G)` commute, and `tau_B` is central in `iota_B(G)` (F2);
- **anti-centrality of the compression:** `F_3[iota_B](eps_-) = Q_B` and `Q_B^2 = Q_B` (F2);
- **positivity of the minimum:** the two-root criterion ([SEP] Theorem 2.2, through
  `weakly-finite-leavitt-representations-killing-defect-are-trivial`), with fp-simplicity of `G/<z>` and perfection
  of `G` ([C3] Lemma 1.3) (F1);
- **definedness under item 1:** `V`-conjugation and the normal-subgroup step of [C3] 3.1.4 (F4);
- **compactness of `A_mat`,** which is a property of the state space, not a relation in `W`.

It does not use `N_12^3 = 0` or any other nilpotency index, and it uses no Frobenius step, socle or Jordan type. The
state comes from compactness, so it is not explicit.

**Smaller images.** Minimize instead over the matrix states of an arbitrary nonzero weakly finite image `W'`. The
compression along `F_3[iota_B]` need not factor through `W'`, because `iota_B` need not preserve the kernel of
`S_- -> W'`. So the argument runs on the global minimizer. It descends to every `S_-/I` with `I ⊆ ker d_0`. For a
maximal `J'` as in Theorem C it descends only if `J' = ker d_0`.

**Remark 3.2 (socle-type states).** Let `H = <x_12(1), x_23(1)>`, the unitriangular group of order 27. Send both
generators to `1 + u` in `F_3[u]/(u^3)`, and pull back the state `d(M) = dim_(F_3) soc(Im M)` of [SEP] Example 3.3. Then
`D -> u^2` and `d(D) = 1`. Every Sylvester rank function has `N(D) <= N(N_12) <= 2/3` on `F_3[H]` ([C3] Lemma 1.1.4).
- **It uses** only `N_12^3 = N_23^3 = 0` and the abelianization of `H`.
- **It breaks** the upper bound `c_3 <= 2/3`, locally. That bound is not part of the target and is not claimed for
  `A_mat`.
- **It does not reach item 2.**
  - It is a state on `F_3[H]` only. `G` is perfect, so the map to `F_3[C_3]` does not extend. Whether some `d` in
    `A_mat` restricts to it is not decided here.
  - Item 2 needs `Q_B` and `D_A`, which lie outside `F_3[H]`.
  - By Lemma 2.1 the actual violation is global, not local.

## 4. (b) What a proof of item 2 must supply

**Proposition 4.1.** These are equivalent:
1. the target holds in scope `A_mat`;
2. for some `n >= 1` there are matrices `X` of size `n x (n-1)` and `Y` of size `(n-1) x n` over `S_-` with
   `XY = I_n`.

An identity as in 2 excludes every matrix state, socle-type states included, since it would give
`n = d(I_n) = d(X I_(n-1) Y) <= d(I_(n-1)) = n - 1`.

*Proof.* Condition 2 is failure of the rank condition. A failure with `X` of size `n x m`, `m < n - 1`, pads with
zero columns and rows to size `n - 1`. Theorem 2.2.2 finishes. QED

**Consequence.** A proof of item 2 from relations no socle-type state can break is a certificate as in 2. That is the
counterexample, not a step toward it.

Every relation of `S_-` holds in `W`. An argument that proves item 2 from relations of `S_-` and the matrix-state
axioms therefore also applies at `d_0`. By Lemma 2.1 it must then prove `W = 0`.

**Remark 4.2 (where [SEP] Section 4.2's warning lands).** [SEP] warns that item 2 over `A_mat` is an upper bound and
may fail.
- By Proposition 3.1 it fails exactly when `S_-` has the rank condition.
- When it fails, it fails at a minimizer through a lower bound (F3), not through a Jordan bound.
- So if a proof of item 2 over `A_S` exists, it fails to transfer to `A_mat` at a triangular step that does not
  flatten to minors, unless the counterexample holds.

## 5. (c) Idempotent minors of `D`

`<~` is the minor order. A minor of the `1 x 1` matrix `D` has the form `x D y`, with `x` a column and `y` a row. By
[SEP] Section 4.1, (c) is the same as `rho^s(D) > 0` for a faithful state `s`.

**Lemma 5.1.** Over any ring `W` these are equivalent:
1. `D` has a nonzero idempotent minor;
2. `WD` contains a nonzero idempotent;
3. `DW` contains a nonzero idempotent.

*Proof.*
- **2 ⟹ 1.** An idempotent `aD` is the minor `a D 1`.
- **1 ⟹ 2.** Let `e = x D y` be a nonzero idempotent, and put `g = (yx) D`, which lies in `WD`.
  - `g^2 = y e x D`, and `g^3 = y e^2 x D = g^2`. So `g^2` is idempotent.
  - `e = e^3 = x (D g^2) y`, so `g^2 != 0`.
- **1 ⟹ 3.** Put `g = D (yx)`. Then `g^2 = D y e x = g^3`, and `e = e^3 = x g^2 D y`.
- **3 ⟹ 1.** An idempotent `Da` is the minor `1 D a`. QED

**Lemma 5.2 (dichotomy).** Let `W` be any quotient of `S_-`. Then either:
- `WDW = W`, and then `I_1 <~ D^((+)k)` for some `k`; or
- `W/WDW` is nonzero and fails the rank condition.

*Proof.*
- **First case.** Write `1 = sum_(i <= k) a_i D b_i`. Then `1 = [a_1 ... a_k] (D (+) ... (+) D) [b_1 ... b_k]^T`.
- **Second case.** Suppose `W/WDW` is nonzero with the rank condition.
  - It carries a matrix state (`sylvester-rank-functions-iff-no-triangular-certificate` item 2).
  - Pulled back to `F_3[G]`, that state lies in `A_mat`, since `eps_- -> 1`, and it kills `D`.
  - This contradicts [SEP] Theorem 2.3.4 with the empty prefix, which is positivity of `c_3^mat`. QED

**Facts.**
- **Over `S_-` the second case holds.** The evaluation `pi : F_3[G] -> R = L_(F_3)(1,2)`, `[g] -> g`, sends `N_12`
  and `N_23` to the matrix units `e_12` and `e_23`. So:
  - `D -> e_23 e_12 = 0`, `eps_- -> 2(1 - (-1)) = 1` and `Q_C -> p_C`;
  - `S_- D S_-` misses `eps_-` and every `Q_C`, so `S_- D S_- != S_-`, and Lemma 5.2 puts `S_-` in the second case.
- **When it would hold.** If `D = D y D` in `W`, then `yD` is a nonzero idempotent in `WD`. Nilpotence does not
  obstruct this: in `M_2(k)`, `e_22 = e_21 e_12` lies in `M_2(k) e_12`.
- **When it fails.** In [SEP] Example 3.3 every idempotent minor of `u` has entries in `(u)` and vanishes.

**Status: open.** For the largest weakly finite image `W`, neither case of Lemma 5.2 is decided. In the first case,
passing from `D^((+)k)` to `D` is not decided either.

## 6. (d) Literature read

All four sources were read as ar5iv HTML renderings through a fetch tool. The wording is as returned.

1. **T. F. Hung and H. Li, *Malcolmson semigroups*, arXiv:2201.01432.**
   - **Definition 3.1.** The matrix Malcolmson semigroup `W_M(R)`. Its preorder `⪯_M` is generated by minor steps
     `A = CBD` and a step between block matrices.
   - **Proposition 3.2.** "R has a Sylvester rank function if and only if I_{n+1}⋠_M I_n for all n∈ℕ", via states of
     `W_M(R)`. This matches item 1 of `sylvester-rank-functions-iff-no-triangular-certificate`.
   - **Proposition 3.3.** "If R has a Sylvester rank function, then R satisfies the rank condition."
   - **Question 3.4.** "If R satisfies the rank condition, then must R have a Sylvester rank function?" The paper
     adds: "Question 3.4 has an affirmative answer for von Neumann regular rings."
   - **Question 3.5.** "If R is stably finite, then must R have a Sylvester rank function?"
   - "It is a result of Malcolmson that R satisfies the rank condition if and only if R has a stably finite quotient
     ring."
   - After Question 3.5: "a result of Cuntz says that stably finite unital C∗-algebras have dimension functions."
2. **K. Lorensen and J. Öinert, *The rank condition and strong rank conditions for Ore extensions*, arXiv:2505.21030.**
   - "P. Malcolmson proves in [16] that a ring fulfills the rank condition if and only if it possesses a nonzero
     quotient that is stably finite." Reference [16] is P. Malcolmson, *On making rings weakly finite*, Proc. Amer.
     Math. Soc. 80 (1980), 215–218.
   - The paper says nothing about Sylvester rank functions.
3. **A. Jaikin-Zapirain and D. López-Álvarez, arXiv:2012.15844.**
   - Proposition 1.3 (Malcolmson): matrix and module rank functions correspond.
   - Integer-valued rank functions correspond to epic division `R`-rings (Cohn–Malcolmson).
   - It has no discussion of the rank condition and no example.
4. **P. Ara and J. Claramunt, *Sylvester matrix rank functions on crossed products*, arXiv:1902.06476.**
   - Definition 2.2 defines Sylvester matrix rank functions. For regular rings they are the pseudo-rank functions
     (Goodearl, Proposition 16.20).
   - It cites Schofield, Part I, Chapter 7, and gives no example.

**Not read:**
- Malcolmson's 1980 paper;
- Schofield, *Representations of Rings over Skew Fields*, Chapter 7;
- Jaikin-Zapirain's survey;
- López-Álvarez's thesis.

The survey mirror and the theses are PDFs, which the fetch tool could not extract. Local PDF reads are not allowed.

**Conclusion.**
- **No example.** No ring with the rank condition and no Sylvester matrix rank function was found.
- **Posed as open.** Hung–Li pose the question as open and answer it positively for regular rings. So
  `rank-condition-rings-carry-sylvester-rank-functions` is their Question 3.4.
- **Relation to (U1b).** A positive answer to Question 3.5 would give (U1b)
  (`anti-central-weakly-finite-images-carry-rank-functions`).
- **Theorem C.** `rank-condition-rings-have-weakly-finite-images` is credited to Malcolmson by both papers above. The
  local proof stands on its own, since the 1980 paper was not read.

## 7. Where it stops

**Proved on paper.**
- Theorem 2.2: in both scopes the deficit target restates emptiness. Over `A_S` that is the kill claim, and over
  `A_mat` it is the counterexample.
- Proposition 3.1: a violator on `W` exists iff `W != 0`, and the minimizer is one.
- Proposition 4.1, and Lemmas 5.1 and 5.2.

**Refuted.** Nothing. The target is not refuted in either scope, because emptiness is open in both.

**Open.**
- (c) for the largest weakly finite image;
- (U1b), and Hung–Li Questions 3.4 and 3.5;
- the kill claim and the counterexample.

**For lanes attacking item 2.**
- Any argument proving item 2 at every `d` implies emptiness.
- In scope `A_S` that means a triangular certificate for `S_-` exists
  (`sylvester-rank-functions-iff-no-triangular-certificate` item 1).
- In scope `A_mat` it means a minor certificate as in Proposition 4.1 exists.
