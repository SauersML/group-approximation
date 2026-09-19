---
rg: 2
id: jnvwy-canonical-halt-strategy-is-affine-unsafe
kind: claim
title: The canonical JNVWY HALT strategy becomes affine-unsafe after one compression
distinct_from:
  dfnqxy-halt-completeness-support-is-not-canonically-specified: that observes that the primary theorem does not choose one completeness chain; this chooses an effective chain and computes an explicit odd-xor violation in it.
  jnvwy-low-degree-pcp-reflects-affine-unsafety: that proves later answer reduction cannot erase an existing violation; this constructs the violation in the preceding introspection sampling test.
  dfnqxy-pcpp-contract-allows-nonlinear-proof-views: that introduces a nonlinear proof bit in a permissible final PCPP; this obstruction is already present before any PCP proof is chosen.
---

**ESTABLISHED FOR THE CANONICAL HONEST COMPLETENESS CHAIN.**  Fix the
JNVWY HALT verifier of arXiv:2001.04383v3 and let `C_0` be the universal
output index in Theorem 12.6.  If the machine first halts at time `T>C_0`,
there is an effective coherent choice of the downward-induction strategy in
Claim 12.7, but the strategy so obtained at level `C_0` has an
affine-unsafe positive joint-answer support.  The violation occurs already
in the first compression below the trivial accepting level and is independent
of all PCP witness choices.

## An effective coherent choice really exists

Starting at any level `n>=T`, use the strategy from Lemma 12.4: both players
always answer the fixed zero string.  Along the finite dependency chain

```text
n_0=C_0,  n_(j+1)=2^(n_j),
```

stop at the first `n_k>=T`.  Going from the already chosen strategy at
`n_(j+1)` to level `n_j`, use in order the honest introspection strategy in
Section 8.5, the explicit oracularization strategy in Section 9, the answer
reduction strategy in Section 10.6, detyping, anchoring, and tensor-product
parallel repetition.  Every existential finite choice in Theorem 10.25 can be
made computable by taking the lexicographically first satisfying triple
`(u_3,u_4,u_5)` and then the lexicographically first coefficient tables
`(c_1,...,c_(m'))` satisfying equation (14).  All search spaces are finite and
nonempty by perfect completeness.  Thus this is one coherent strategy, not an
appeal to an unchosen existential strategy.

## The nonlinear sampler component

The fixed sampler `ComputeSampler(lambda)` is the sampler of one application
of `Compress`; see Lemma 12.3.  Its answer-reduction sampler contains, as a
direct summand, the axis-line PCP sampler from equation (30):

```text
L_A(u,s,v)=(L^lnf_(e_(chi(s)))(u),s,0).                 (CHA1)
```

Here `q=2^k`, `m=2^j>=4`, `m|q`, and `chi(s)` is the unique integer satisfying

```text
s=(chi(s)-1)q/m+r,  0<=r<q/m.                           (CHA2)
```

The canonical projection `L^lnf_(e_i)` simply deletes coordinate `i`.
Put `s_2=q/m`, interpreted through the paper's fixed binary basis of `F_q`,
and in the `u,s,v` registers put

```text
xi_0=0,  xi_1=(e_2,0,0),  xi_2=(0,s_2,0).              (CHA3)
```

Since `chi(0)=1` and `chi(s_2)=2`,

```text
L_A(xi_1)+L_A(xi_2)=(e_2,s_2,0),
L_A(xi_1+xi_2)       =(0,s_2,0).                        (CHA4)
```

Thus `L_A` is not linear over `F_2`.

This nonlinear component survives every sampler transformation used to define
`ComputeSampler`.  In the answer-reduced typed sampler it is literally a
direct summand.  In each detyping, fix one graph-sampler prefix activating the
chosen axis-line type; repeating that same prefix three times preserves it
under odd xor, while Definition 5.21 applies `L_A` to the remaining register.
In anchoring fix the `Game` prefix, and in parallel repetition put the three
varying seeds in one coordinate and identical seeds in all other coordinates.
The direct-sum formula in Section 11.3 preserves `(CHA4)`.  Consequently one
of the two untyped CL maps `L` of `ComputeSampler(lambda)` has seeds
`z_0,z_1,z_2` such that

```text
L(z_0)+L(z_1)+L(z_2) != L(z_0+z_1+z_2).                (CHA5)
```

All three seeds have positive probability because the sampler seed is uniform.

## Odd-xor violation in the honest introspection strategy

Consider the first compression on the dependency chain, from the trivial
zero-answer strategy at level `n_k` to the strategy at `n_(k-1)`.  On the
typed question pair

```text
(Intro,role) -- (Sample,role),                           (CHA6)
```

the honest strategy in Section 8.5 has, for every sampler seed `z`, the joint
answer

```text
((L(z),0),(z,0)).                                       (CHA7)
```

with positive probability.  This follows directly from the EPR `Z`
measurement: `Sample` reads the full `z`, `Intro` reads its coarse value
`L(z)`, and the source answer is the fixed zero string.  The sampling test in
Figure 16 accepts exactly when the displayed graph equation holds.

Apply `(CHA7)` to the three seeds from `(CHA5)`.  Their odd xor is

```text
((L(z_0)+L(z_1)+L(z_2),0),(z_0+z_1+z_2,0)),             (CHA8)
```

which the same sampling test rejects by `(CHA5)`.  Hence this positive support
is not affine-safe.

Oracularization and the characteristic-two low-degree answer reduction cannot
erase this witness by `jnvwy-low-degree-pcp-reflects-affine-unsafety`;
anchoring and repetition preserve it by fixing every other coordinate to one
positive answer.  At each earlier recursion step, the `Intro--Intro` game test
embeds the already bad source question and answers: the source question is
repeated three times and so survives odd xor, while its rejected odd-xor answer
is still rejected.  The same reflection argument then passes the witness
through the rest of that compression.  Induction down the chain gives the
claimed violation at `C_0`.

If `T<=C_0`, the output decider accepts immediately and the singleton zero
strategy is affine-safe.  Thus this result does not say that every HALT input
or every possible perfect strategy is unsafe.  It proves the sharper fact
needed for source bookkeeping: the most direct coherent realization of Claim
12.7 cannot supply the affine-safe HALT model required by
`affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain` whenever the
recursive compression is actually used.  A positive proof must change the
completeness strategy or the introspection sampler; choosing different PCP
proofs cannot repair this chain.
