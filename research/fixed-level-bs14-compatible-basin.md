---
rg: 2
id: fixed-level-bs14-compatible-basin
kind: claim
title: One-parameter finite Iwahori shadows still need a compatible basin
distinct_from:
  bs14-long-cycles-admit-bounded-period-shadowing: that constructs the bounded-cycle BS core in the same dimension; this observes that its single unipotent power row already makes the full Iwahori endpoint finite and audits whether the resulting pointwise stability can be diagonalized.
  bs14-full-commutant-finite-period-preconditioner: that additionally quantizes return monodromy and imposes an `r`-power row; neither operation is needed to make the fixed-level Iwahori quotient finite.
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for the final uniform repair; this gives an exact sufficient fixed-level formulation and the quantifier fence on a naive proof.
  bs14-exact-representation-variety-is-hs-locally-rigid: that aligns two exact BS cores with a uniform modulus; this concerns the extra involution over one preconditioned core.
  one-unipotent-quotients-are-bounded-congruence: that identifies every finite target up to the one fixed congruence kernel; this asks for the remaining quantitative repair across those moving congruence levels.
  regular-bs14-cores-admit-dyadic-one-power-shadows: that improves the regular-branch preconditioner to the single level 4^K-1 at square-root logarithmic cost; this states the basin comparison which remains after either preconditioner.
  bs14-one-power-level-is-a-native-short-commutator: that replaces the exponentially written power row by one native BS commutator of length 2K+2; this asks for the quantitative repair basin after that exact syntactic compression.
  native-bs-level-has-strict-square-root-counterpackets: that caps any family-wide strict same-dimensional native-row basin at the K^-1/2 scale along K=p-1; this keeps the flexible o(d)-padding formulation which those counterpackets do not refute and makes no dyadic-only strict claim.
  induced-rounding-needs-rms-section-fillings: that builds the canonical induced-space repair and reduces its success to sub-square-root RMS relative fillings; this keeps the abstract basin formulation independent of a chosen repair mechanism.
---

For `K>=2`, set

```text
N_K=lcm_(1<=m<=K)(4^m-1).                             (FLB1)
```

Every core produced by `bs14-long-cycles-admit-bounded-period-shadowing`
satisfies

```text
S_K^N_K=1.                                             (FLB2)
```

The fixed-level relative problem is therefore the arbitrary-multiplicity
matrix representation problem for the one-power quotient

```text
Gamma_K=<x,r,s | x^2,(xr)^2,(xs^2)^3,(xrs)^3,
                   r s r^(-1)s^(-4),s^N_K>.           (FLB3)
```

The group `Gamma_K` is finite.  Indeed the full presentation before the
power row is `PSL_2(Z[1/2])`, and the normal closure of the nontrivial
unipotent power `s^N` has finite index by the S-arithmetic normal-subgroup
theorem.  Therefore finite-group Hilbert--Schmidt stability supplies, for
every fixed `K`, a flexible modulus `f_K` on some radius `delta_K>0`.  This
closes the fixed-level arbitrary-multiplicity problem unconditionally; the
modulus is not uniform in `K`.

Let

```text
alpha_K
 =C_0(sqrt(8/K)+pi sqrt(2/(9K)))
 =C_*/sqrt(K)                                         (FLB4)
```

be the word-Lipschitz defect introduced in the four `x`-relations by the
bounded-cycle shadowing.  For the fixed-level moduli above, a cofinal
sequence `K_j` proves `bs14-relative-involution-extension-stability`
provided

```text
alpha_j < delta_j/2,
alpha_j -> 0,
f_j(2 alpha_j) -> 0.                                  (FLB5)
```

Indeed, for an original defect `epsilon` small relative to `alpha_j`, word
Lipschitzness puts the preconditioned tuple inside the `2alpha_j` ball;
fixed-level repair then costs `f_j(2alpha_j)`, and the preconditioning cost
also tends to zero.

However, the now-established flexible stability of every fixed `Gamma_K`
does not imply `(FLB5)`.  It only says each `delta_K>0` and `f_K(t)->0`
with `K` fixed.  Those radii may shrink faster than `alpha_K`; for example
the abstract schedules

```text
alpha_j=1/j,                 delta_j=exp(-j)           (FLB6)
```

satisfy both pointwise statements and admit no usable diagonal.  The
original microstate defect tending to zero cannot remove the fixed
preconditioning error `alpha_j`.

Under the compatibility hypotheses `(FLB5)`, this bypass would prove the
qualitative flexible endpoint, not the sharper quadratic padding estimate
`(FBR2)` in `bs14-flexible-cross-packet-boundary-reconciliation`.  Without
`(FLB5)`, no endpoint follows from the pointwise fixed-level statements.

Therefore the fixed-period strategy has isolated the sole surviving
uniformity problem.  The whole short-support endpoint is finite and stable.
In fact `one-unipotent-quotients-are-bounded-congruence`
shows that it is a bounded extension of `PSL_2(Z/N_K)`, and
`bounded-cycle-level-has-only-polylogarithmic-error` shows that the injected
error is only polylogarithmically small in the quotient size.

For a regular microstate sequence there is a sharper, sequence-dependent
choice.  By `regular-bs14-cores-admit-dyadic-one-power-shadows`, after a slow
diagonal one may instead take

```text
K=2^q,             N=4^K-1,                          (FLB7)
alpha_K=O(K^(-1/2))
       =O((log |Gamma/<<s^N>>|)^(-1/2)).             (FLB8)
```

The compatibility condition `(FLB5)` then applies with these single-level
quotients and the improved error `(FLB8)`.  This removes the universal LCM
tax and changes the sharp regular-branch target from inverse fourth-root to
inverse square-root logarithmic scale.  It does not manufacture a basin:
even a radius `N^(-c)` or `|Gamma/<<s^N>>|^(-c)` is exponentially smaller
than `(FLB8)`.

Hence a generic finite-group estimate losing any power of the level or group
order cannot certify `(FLB5)` on either staircase; the needed input is a
uniform/polylogarithmic congruence-family theorem or a special relative repair
over the exact core.
The power row in the sharper regular branch is not itself syntactically
exponential: `bs14-one-power-level-is-a-native-short-commutator` identifies it,
over the exact BS core, with

```text
[r^K,s]=1,                                             (FLB9)
```

a word of length `2K+2` which the dyadic shadow satisfies exactly.  This
removes a presentation-length distraction, but not the basin comparison.
Moving a perturbed core to an exact one changes `(FLB9)` by a bound linear in
`K`, and deriving the equivalence from a raw defective BS row again incurs
power-conditioning loss.
Moreover `repeated-squaring-and-tau-do-not-supply-the-moving-basin` shows
that compressing `s^N` to logarithmically many short rows and invoking
property `(tau)` still does not produce that theorem.  Short rows can be
exponentially ill-conditioned, while Selberg averaging controls an
intertwiner only after the two congruence representations have already been
authenticated.
What is still needed is either a lower bound on its basin and modulus in
terms of `K`, or a preconditioner whose error is adapted to that basin.  The
earlier monodromy parameter `M` and the row `r^L=1` do not address this
remaining comparison and may be deleted.  Pointwise finite-group stability
is logically insufficient for the one-parameter moving staircase.
