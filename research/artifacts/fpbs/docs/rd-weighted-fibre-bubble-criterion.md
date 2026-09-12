# Rapid decay and the weighted critical fibre bubble

Lane `bs-fibre-bubble-general`, 2026-09-12. The setting and notation are those
of `research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md`,
Section 0: `Gamma` finitely generated, `S` a finite symmetric generating set,
`X = Cay(Gamma,S)`, `d = |S|`, `H` normal in `Gamma`, `Q = Gamma/H` with the word
length `|.|` from `pi(S)`, and

    sigma_p(q) = sum_{x in Gamma_q} tau_p(o,x) = E_p|K_o ∩ Gamma_q|,
    b_R(p)     = sum_{|q| = R} sigma_p(q)^2,
    (S_p F)(q) = sum_{q'} sigma_p(q^(-1) q') F(q')      on l2(Q).

That artifact reduces `p_c < p_{2->2}` over a hyperbolic quotient to two
premises: (i) the uniform fibre bubble `sum_R b_R(p_c) < infinity`, and (ii) a
vanishing far-halfspace share. Premise (i) also drives the mean-field
susceptibility bound.

This note gives a different sufficient condition. A polynomially weighted
critical fibre bubble alone gives critical L2 boundedness whenever `Q` has the
Rapid Decay property, with no halfspace estimate and no susceptibility bound.
For amenable `H` the unweighted bubble is necessary for the L2 gap, so the gap is
sandwiched between the two bubbles. Nothing here is refereed or formalized.

## 1. The weighted bubble criterion

**Rapid Decay (RD).** `Q` has RD with exponent `D` if there is `C` such that,
for every `R >= 0` and every finitely supported `f` on `Q` supported in the ball
`B_Q(R)`,

    ||lambda_Q(f)||_{l2 -> l2}  <=  C (1+R)^D ||f||_2 .

Word hyperbolic groups have RD (`hyperbolic-groups-have-property-rd`). Changing
the finite generating set of `Q` changes lengths bi-Lipschitzly, so RD holds for
the length from `pi(S)` with some `C, D`.

**Theorem 1.1.** Let `Q = Gamma/H` have RD with constants `C, D`. Put

    W_D(p) = sum_{q in Q} (1+|q|)^(2D+2) sigma_p(q)^2 = sum_R (1+R)^(2D+2) b_R(p).

If `W_D(p_c) < infinity`, then

    ||T_(p_c)||_{2->2}  <=  ||S_(p_c)||_{2->2}  <=  C (pi/sqrt 6) W_D(p_c)^(1/2)  <  infinity,

and consequently `p_c(X) < p_{2->2}(X) <= p_u(X)`.

*Proof.* Write `sigma = sigma_(p_c)`, which is finite everywhere because
`W_D(p_c) < infinity`.

1. **Convolution form.** By fact (a) of the prior artifact,
   `sigma(q^(-1)) = sigma(q)`. So `S_(p_c) F = F * sigma`, right convolution by
   `sigma`. Conjugating by the unitary `F -> F(.^(-1))` turns it into
   `lambda_Q(sigma)`, so the two operator norms agree.
2. **Sphere splitting.** Put `sigma_R = sigma 1_{|q| = R}`. Spheres of the
   finitely generated group `Q` are finite, so `sigma_R` is finitely supported
   in `B_Q(R)` and `||sigma_R||_2^2 = b_R(p_c)`. RD gives
   `||lambda_Q(sigma_R)|| <= C (1+R)^D b_R(p_c)^(1/2)`.
3. **Summation.** For nonnegative finitely supported `F, G` on `Q`,

       <G, lambda_Q(sigma) F> = sum_R <G, lambda_Q(sigma_R) F>
                             <= C sum_R (1+R)^D b_R^(1/2) ||F|| ||G||.

   By Cauchy–Schwarz,
   `sum_R (1+R)^D b_R^(1/2) <= (sum_R (1+R)^(-2))^(1/2) (sum_R (1+R)^(2D+2) b_R)^(1/2)`
   `= (pi^2/6)^(1/2) W_D^(1/2)`.
   The kernel is nonnegative, so the operator norm is attained on nonnegative
   vectors. Hence `||S_(p_c)|| <= C (pi/sqrt 6) W_D(p_c)^(1/2)`.
4. **Fibre comparison.** `fpbs-fibre-summed-connectivity-operator` (Theorem 1.1
   of the prior artifact) gives `||T_p|| <= ||S_p||` in `[0, infinity]` for every
   `p` and every normal `H`, amenable or not. Take `p = p_c`.
5. **L2 gap.** `tau_p` increases entrywise in `p`, so `||T_p||` is nondecreasing.
   Hutchcroft's Corollary 2.6 (arXiv:1804.10191, imported in the prior artifact)
   gives `||T_p|| >= (1-p)/(d (p_{2->2} - p))` for `p < p_{2->2}`. If
   `p_c = p_{2->2}`, then `||T_(p_c)|| >= sup_{p < p_c} ||T_p|| = infinity`,
   contradicting step 4. So `p_c < p_{2->2}`. Finally `p_{2->2} <= p_u`: in the
   uniqueness phase `tau_p(o,x) >= theta(p)^2 > 0` by Harris–FKG, and such a kernel
   is unbounded on `l2` of an infinite graph. The same conclusion is the imported
   `fpbs-critical-l2-implies-nonuniqueness`. QED.

**Remarks.**
* **What is not used:** amenability of `H`, hyperbolicity beyond RD, the
  susceptibility exponent (Theorem 2.1 of the prior artifact), and the
  far-halfspace share (premise (ii)).
* **Vacuous for amenable `Q`:** if `Q` is amenable, RD forces polynomial growth
  (Jolissaint), and for a nonnegative kernel on an amenable group
  `||S_(p_c)|| = sum_q sigma(q) = chi_(p_c) = infinity`. So `W_D(p_c) = infinity`,
  and the criterion only says something when `Q` is nonamenable.
* **Beyond hyperbolic quotients:** the theorem applies to every quotient with
  RD. Examples as listed in Chatterji, arXiv:1604.06387, Section 1:
  * groups hyperbolic relative to RD subgroups (Drutu–Sapir);
  * mapping class groups (Behrstock–Minsky);
  * cocompact lattices in `SL_3(R)` and `SL_3(C)` (Lafforgue);
  * `A~_2` groups (Ramagge–Robertson–Steger).
  So the same one-premise criterion covers extensions of those groups by infinite
  normal subgroups, which are not acylindrically hyperbolic when the kernel is
  amenable of infinite index.

## 2. The unweighted bubble is necessary for amenable kernels

**Proposition 2.1.** Let `H` be amenable. If `p_c(X) < p_{2->2}(X)`, then

    sum_{q in Q} sigma_(p_c)(q)^2  <=  ||T_(p_c)||_{2->2}^2  <  infinity.

*Proof.* `p_{2->2}` is the supremum of `p` with `||T_p|| < infinity`, and
`||T_p||` is nondecreasing. So `p_c < p_{2->2}` gives `||T_(p_c)|| < infinity`.
For amenable `H`, `||S_(p_c)|| = ||T_(p_c)||` (equality half of
`fpbs-fibre-summed-connectivity-operator`). Also
`sum_q sigma(q)^2 = ||S_(p_c) delta_1||_2^2 <= ||S_(p_c)||^2`. QED.

**Corollary 2.2 (sandwich).** For amenable `H` and a quotient `Q` with RD
exponent `D`,

    W_D(p_c) < infinity   ==>   p_c < p_{2->2}   ==>   sum_R b_R(p_c) < infinity.

Premise (i), the uniform fibre bubble, is therefore necessary for the L2 gap in
the amenable-kernel class. Its polynomially weighted form is sufficient by
itself. By left-continuity and monotonicity of `p -> sigma_p(q)` (prior artifact,
Section 4.4), both sums at `p_c` equal their suprema over `p < p_c`.

## 3. Mean-field consistency

Let `mu` be a symmetric finitely supported step law on `Gamma`, and let the
projected walk on `Q` have step length at most `r_0` and spectral radius
`rho < 1`, as happens for nonamenable `Q` by Kesten. For critical branching
random walk with step law `mu`, the expected occupation of the fibre `Gamma_q` is
the projected Green function `G_Q(1,q) = sum_n p^(n)(1,q)`. Since `|q| <= r_0 n`
on the support of `p^(n)(1,.)`, and by symmetry,

    sum_q (1+|q|)^(2s) G_Q(1,q)^2
      <= sum_{n,m} (1 + r_0 (n+m))^(2s) p^(n+m)(1,1)
      <= sum_k (k+1) (1 + r_0 k)^(2s) rho^k  <  infinity

for every `s`. So the mean-field profile satisfies `W_D < infinity` for every
polynomial weight. This is a heuristic only: comparing critical percolation with
branching random walk is itself a triangle-type input.

## 4. Relation to the tree-projected criterion

In the tree-projected class of the prior artifact (Section 4.3; `Q = F_n`,
`pi(S) \ {1}` inside a free basis and inverses, `H` infinite cyclic), fibres are
cut sets and `b_(R+R') <= b_R b_(R')`.
* If `b_(R_0)(p_c) = 1 - eta` for some `R_0`, then steps 1–3 of the proof of
  Theorem 4.3 there give `b_R(p) <= C (1-eta)^(floor(R/R_0))` uniformly for
  `p < p_c`, and hence at `p_c` by left-continuity.
* So `W_D(p_c) < infinity` for every `D`, and Theorem 1.1 applies. The
  finite-radius criterion there is the cut-set route to the weighted bubble.

Over a one-ended hyperbolic quotient, such as a closed surface group (the
Seifert-fibred bases of Choi–Seo Question 1.6), no fibre separates `X`. BK
does not factor `sigma` through intermediate fibres, and no submultiplicativity
of `b_R` is available.

## 5. Open premise and dead ends

The remaining input for the whole class is the open claim
`fpbs-rd-quotient-weighted-critical-fibre-bubble`: `W_D(p_c) < infinity` for every
`Gamma` with an infinite normal subgroup and non-elementary hyperbolic quotient,
and every `S`.

* **Differential inequality.** Russo plus BK give
  `dT_p/dp <= p^(-1) T_p A T_p` entrywise. Pushed to weighted fibre sums, the
  growth rate of `W_D` involves the weighted operator norm of `S_p`, which is an
  L2-type quantity. The same barrier as the unweighted bubble.
* **From the unweighted bubble.** Square summability of `b_R` does not upgrade
  to polynomially weighted summability without a decay mechanism. The only
  mechanism found is cut-fibre submultiplicativity (Section 4), which needs a
  tree-like projection.
* **Far-halfspace share.** Not needed on this route. For the record, BK at the
  first entry into a fibre-saturated halfspace `pi^(-1)(H_Q)` gives
  `E_p|K_o ∩ pi^(-1)(H_Q)| <= chi_p sum_{q in d_in H_Q} sigma_p(q)`. The inner
  boundary of a halfspace is infinite, so this alone does not give premise (ii).

## 6. Not verified

* RD for hyperbolic groups is imported. Statement and credits are read from the
  LaTeX source of Chatterji, arXiv:1604.06387, Definition 1.1 and the examples
  list of Section 1: Jolissaint 1990 and de la Harpe 1988. The primary papers
  were not re-read.
* Hutchcroft's Corollary 2.6 is imported through the prior artifact.
* No numerics bear on `W_D(p_c)`.
