---
rg: 2
id: fpbs-relative-gap-state-axioms-admit-collapse
kind: claim
title: On every nonamenable Cayley graph and every infinite subgroup the two-point collapse state has infinite fibre mass just above p_c, so no state-level or quotient group-ring argument proves a relative threshold gap, even on critical-fibre-l2 pairs where the gap is a theorem
distinct_from:
  fpbs-two-point-state-axioms-admit-collapse: that builds the witness and kills state-level proofs of p_c < p_u, NC and VIS on the whole group; this reads the same witness on fibres of an infinite subgroup and kills state-level proofs of the relative gap p_c < p_c(N;G), including every argument through the quotient fibre profile sigma_p, the operator S_p on l2(Q) or Kesten's rho_Q < 1, and it shows the infinite-volume Russo-BK axiom cannot replace truncation in the ESTABLISHED critical-fibre-l2 route to the gap.
  fpbs-soft-collapse-kills-relative-gap-proofs: that is an event-level collapse and needs invariant sparse spines (which do not exist on F_2); this is state-level, lives on every nonamenable Cayley graph and every infinite subgroup, and its axioms include Harris supermultiplicativity and the integrated infinite-volume Russo-BK inequality.
  fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2: that proves critical fibre l2 implies the gap by the truncated Russo-BK majorant; this shows that implication is false for state families obeying only the infinite-volume axioms, so the truncation is the load-bearing step there.
  fpbs-percolation-kesten-normal-gap: that is the OPEN gap claim; this is an obstruction for one class of proofs of it, not a proof or disproof.
---

**ESTABLISHED (class-killing obstruction, state level, relative form).** Proof
route `fpbs-relative-gap-state-axioms-admit-collapse-proof`.

**Setting.** `Gamma` is finitely generated and nonamenable, `S` finite
symmetric generating, `G = Cay(Gamma,S)`, `p_c = p_c(G)`. Two-point state
families `g = (g_p)` and the axioms (T1)--(T8) are exactly those of
`fpbs-two-point-state-axioms-admit-collapse`. The collapse witness is

```text
f_p = tau_p                                   (p <= p_c),
f_p = theta(p)^2 + (1 - theta(p)^2) tau_(p_c)   (p >  p_c).
```

For a family `g`, an infinite subgroup `I <= Gamma`, a coset `xI` and `p`, put

```text
chi^I(g_p)        = sum_(y in I)  g_p(y)            in [0, infinity],
sigma^I_(g_p)(xI) = sum_(y in xI) g_p(y),
p_c(I; g)         = sup{ p : chi^I(g_p) < infinity }.
```

For Bernoulli (`g = tau`) these are `chi^I_p`, the fibre profile `sigma_p` and
`p_c(I;G)`. When `I = N` is normal, `S^g_p` is convolution by
`sigma^N_(g_p)` on `l2(Gamma/N)`.

**Theorem.**

1. *(Witness is admissible.)* `f` satisfies (T1)--(T8), and `f_p = tau_p` for
   `p <= p_c`. (Imported.)
2. *(Relative collapse on every fibre.)* For every `p > p_c`, every infinite
   subgroup `I` and every coset `xI`: `sigma^I_(f_p)(xI) = infinity`. Hence
   `chi^I(f_p) = infinity`, `p_c(I; f) = p_c(G)`, and for normal `I = N`,
   `S^f_p` is `+infinity` on every nonzero nonnegative vector.
3. *(Critical data are Bernoulli.)* All data of `f` at `p <= p_c` equal those
   of Bernoulli: `chi^N_(p_c)`, `sigma_(p_c)`, `||S_(p_c)||_(l2(Q))`, the
   diagonal formula data, and the type (i)/(ii)/(iii) of the pair `(G,N)`.
   Group data (`rho_Q`, `rho_Gamma`, cogrowth of `N`) do not depend on `g`.
4. *(Consequence.)* Let a *state-level relative argument* be one whose inputs
   about `p -> tau_p` are (T1)--(T8), together with any function of the
   Bernoulli data at `p <= p_c` and any group-theoretic facts about
   `(Gamma, S, N)`. No such argument proves `p_c(G) < p_c(N;G)` for any pair
   `(G, N)` with `N` infinite, whatever `Gamma/N` is. It would apply verbatim
   to `f`, contradicting 2.
5. *(Truncation is load-bearing on type-(i) pairs.)* Suppose
   `||S_(p_c)||_(l2(Q)) < infinity` (type (i)). By
   `fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2` item 3 Bernoulli then
   has the gap. Yet `f` has the same critical fibre operator and satisfies the
   infinite-volume integrated Russo--BK axiom (T8), and has no gap. So the
   implication "critical fibre l2 implies gap" is not a consequence of
   (T1)--(T8): the passage to finite truncated kernels in its proof (the
   majorant `M^N(delta)` is built from Step 4e of
   `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof`) is the step
   that state information cannot supply. Moreover, on these pairs
   `||T_(p_c)|| <= ||S_(p_c)|| < infinity`, so by item 3 of
   `fpbs-two-point-state-axioms-admit-collapse`, `f` admits no truncation
   system.

**What this kills.** The quotient group-ring class of approaches to the gap:
positive definiteness or Fourier--Stieltjes norms of `sigma_p`, the operator
`S_p` and its spectral data, Kesten's `rho_Q < 1` applied to fibre profiles,
Harris supermultiplicativity, mean-field branching-walk comparison run through
two-point quantities, and the infinite-volume Russo--BK integral. This holds on
**every** pair `(G, N)`, including `F_2 x F_2` along a factor, Kazhdan
groups, Burnside and Tarski products, and the free-group tree pairs where the
gap is a theorem. It strictly extends `fpbs-soft-collapse-kills-relative-gap-proofs`,
whose witness exists only over invariant sparse spines.

* **Invariant.** The uniform atom `inf_x g_p(x)`, which for `f_p` is
  `theta(p)^2 > 0`. Summed over any infinite coset it is infinite. It is
  upper semicontinuous in `p` for the pointwise topology, and (T7) forces only
  `theta(p_c +) = 0`.
* **Failing step.** The continuation from `p_c` to `p_c + delta` for the
  fibre sum `chi^N`. (T3), (T7) and (T8) are the only links between the
  critical state and supercritical states, and (T8) is vacuous above `p_c`
  because its integrand is `+infinity` once `theta(s) > 0`.
* **Required escape.** A proof of the gap must use event-level or
  finite-volume information: finite-radius truncations uniform in `R`,
  pivotal counts, cluster geometry, or realisability of the family as a
  percolation. By `fpbs-soft-collapse-kills-relative-gap-proofs`, on graphs
  with invariant sparse spines even soft event-level inputs are not enough.

**Not claimed.**

* `f` is not asserted to be the two-point function of an invariant percolation.
* It is not decided whether a state family obeying (T1)--(T8) can have
  `p_c < p_(2->2)` in a window (so `||G_p|| < infinity` just above `p_c`) and
  still `chi^N(g_p) = infinity` along a nonamenable normal `N`. Such a family
  would show that the gap along nonamenable `N` is not a state-level
  consequence of `p_c < p_(2->2)`. The witness `f` does not do this, since
  `||G_p|| = infinity` for `p > p_c`.
