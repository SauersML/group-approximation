---
rg: 2
id: revealing-cl-controls-breaks-compression
kind: claim
title: Conditioning or revealing CL controls linearizes fibers but breaks recursive compression
distinct_from:
  jnvwy-canonical-halt-strategy-is-affine-unsafe: that exhibits the odd-xor violation produced by the unrepaired sampler; this proves why exposing its local control is not a polynomial-size repair after repetition.
  jnvwy-perfect-introspection-forces-full-seed-support: that proves every perfect model of the unchanged introspection verifier has full seed support; this audits three proposed modifications intended to split that support into affine fibers.
  dfnqxy-halt-completeness-support-is-not-canonically-specified: that leaves open a different perfect HALT strategy; this audits one proposed modification of the JNVWY introspection construction itself.
  affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain: that gives a conditional endpoint from affine-safe HALT supports; this identifies the new introspection theorem that would be needed to obtain those supports by control revelation.
---

**ESTABLISHED NO-GO FOR THE NAIVE UPSTREAM AFFINE-PROFILE MOVE.**  The nonlinear
axis-line component isolated in
`jnvwy-canonical-halt-strategy-is-affine-unsafe` is linear on each fiber of
its small control.  There are three evident ways to expose one such fiber,
and none is a sound use of the published JNVWY introspection theorem:

1. narrowing the existing `SAMPLE` answer relation to one control fiber keeps
   soundness monotone but destroys exact completeness;
2. conditioning the source question distribution on the fiber preserves a
   perfect strategy but is not soundness monotone; and
3. promoting the fiber label to a premeasurement question can preserve an
   honest strategy, but removes the single parent `SAMPLE` PVM used in the
   introspection decoder.  After anchored repetition it also requires an
   exponentially long control profile.

Thus finite affine-profile enumeration cannot simply be moved upstream across
introspection.  A new coherent conditioned-introspection theorem would be
needed.

## One axis-line coordinate can be repaired

Use the notation of equation (49) of arXiv:2001.04383v3:

```text
L_A(u,s,v)=(L^lnf_(e_(chi(s)))(u),s,0),                (RCL1)
```

where `q=2^k`, `m=2^j`, and `chi(s)` records the interval of length `q/m`
containing the integer representative of `s`.  In the paper's fixed binary
basis, a fiber `chi(s)=i` is an affine subspace: it fixes the high `j` bits of
`s` and leaves the low `k-j` bits free.  On this fiber the selected deletion
map is fixed, so `(u,s,v) -> (L^lnf_(e_i)(u),s,0)` is the restriction of one
linear map.  Thus sending either all of `s` or just `chi(s)` in the verifier's
question makes the honest graph support affine in this one coordinate.

For a general conditionally linear function, the same statement holds after
fixing the successive prefix controls on which its constituent linear maps
depend.  The number of possible fibers is finite and effectively enumerable.
Finiteness is therefore not the obstruction; completeness, soundness, and
recursive question complexity are.

## Predicate narrowing to a fixed fiber kills exact completeness

Let `V` be the introspection seed space and let `S_z` denote the `SAMPLE` PVM
after marginalizing the auxiliary answer.  The exact acceptance-equation
argument in `jnvwy-perfect-introspection-forces-full-seed-support` proves for
every perfect PCC, synchronous commuting, or Connes-embeddable tracial model
that

```text
tau(S_z)=1/|V|  for every z in V.                       (RCL2)
```

It uses the exact Pauli acceptance equations to obtain the full Weyl table,
tracial conjugacy to make every Pauli-Z atom equitracial, and exact
Pauli--Sample consistency to transfer that trace to `S_z`.  This exact
argument is needed because the published robust error bound does not vanish
at zero game error for fixed parameters.  If
`F_i={z: chi(s(z))=i}`, then equation (50) gives

```text
Pr[z in F_i]=|F_i|/|V|=1/m.                             (RCL3)
```

Equivalently, the coarse projection
`P_i=sum_(z in F_i) S_z` has state expectation `1/m`, not `1`.
Consequently a branch which retains the original `SAMPLE` question and merely
rejects all outcomes outside `F_i` has success probability at most `1/m` in
the sampling check of every exact strategy covered by the introspection
rigidity theorem.  It cannot be a perfect HALT branch.  Fixing an `r`-bit
proper CL prefix gives the identical obstruction with mass `2^(-r)`.

This distinguishes the proposed move from
`finite-affine-profile-or-removes-pcpp-section-gate`.  There, predicate
narrowing retains an entire unknown perfect answer support.  Here the honest
support is a uniform union of control fibers, and no one proper fiber contains
it.

## Conditioning the question distribution loses NONHALT soundness

One can instead replace the seed distribution by its conditional distribution
on `F_i`.  A strategy perfect for the original source game remains perfect for
every positive-probability conditional game, so HALT completeness is harmless.
But game value is not monotone under conditioning.  If

```text
mu=sum_i p_i mu_i,
```

then separate near-perfect strategies for the games with distributions
`mu_i` need not be restrictions of one strategy for `mu`.  The standard CHSH
game is already a finite counterexample: its quantum value is strictly below
one, while conditioning on any single question pair gives a game with value
one.  Hence a finite OR of conditioned branches can be perfect although the
unconditioned source has a fixed NONHALT gap.

Forcing all conditioned branches to use one coherent measurement family would
repair this particular logical implication, but the union of their supports
is then the original nonlinear graph.  Proving that a compiled family has the
required cross-fiber coherence is precisely an additional soundness theorem,
not a consequence of pointwise narrowing.

## A public control question removes the parent PVM

Another proposal is to give `i` (or the full successive CL-control profile) to
the players before they answer.  The players may then use a different PVM
`{B_z^(i)}_(z in F_i)` for each `i`.  This is not the interface proved sound in
JNVWY.  Equations (79) and (80) of Lemma 8.20 reconstruct one question-
independent `SAMPLE` PVM `{B_z}` and identify each `INTRO` measurement with a
coarse-graining of that same PVM.  Merely forgetting the new question produces
the operators

```text
p_i B_z^(i),
```

which form a POVM after summing over `i` but are not, in general, orthogonal
projections and do not satisfy (79)--(80).  If one instead requires the public-
`i` PVMs to be literal restrictions of a common parent `{S_z}`, then their
sum on branch `i` is `P_i`, whose state mass is `1/m` by (RCL3), rather than
the identity.  Thus literal parent-PVM coherence brings back the completeness
obstruction above.  Any dilation or corner construction that evades this
dichotomy needs a new proof that the Pauli and hiding tests decode one source
strategy; Theorem 8.3 does not provide it.

## Distinct repeated profiles cannot share one affine-safe question

Let `A=L^lnf_(e_1)` and `B=L^lnf_(e_2)`.  Restrict every repetition coordinate
to controls selecting only `A` or `B`.  Consider any proposed external
question value whose conditional honest support contains two distinct
profiles `alpha,beta in {A,B}^K`.  Choose a coordinate `r` where they differ,
and orient the notation so that `alpha_r=A`, `beta_r=B`.  In coordinate `r`
take payload `e_2`, while fixing all other payloads to zero.  The conditional
support then contains the three graph points

```text
(alpha,0,0),  (alpha,e_2,A(e_2)),  (beta,0,0).          (RCL4)
```

Their odd xor has control profile `beta`, payload `e_2`, and claimed output
`A(e_2)`.  But `A(e_2)=e_2` and `B(e_2)=0`, so this xor is rejected by the
graph test for profile `beta`.  Hence no affine-safe conditional support can
mix `alpha` and `beta`.

It follows that a classical control-revelation repair must distinguish all
`2^K` profiles even after this two-choice restriction.  Its question needs at
least `K` control bits.  Revealing one randomly selected control, a checksum,
or any label with fewer than `K` bits leaves two profiles in one fiber and the
same witness applies.

## This violates the introspection/compression complexity theorem

Section 11.3 defines anchored repetition using

```text
K(N)=(lambda N)^((1+c') tau)                           (RCL5)
```

(up to the harmless renaming of the repetition exponent in the summary of
`Compress`).  In one recursive compression at output index `n`, introspection
is applied to the source verifier at `N=2^n`.  Therefore the required exposed
profile has length

```text
K(2^n)=(lambda 2^n)^((1+c') tau)=2^(Omega(n)).         (RCL6)
```

The Introspection Theorem requires
`TIME_(sampler^intro)(n)=poly(n,lambda,ell)`.  A sampler cannot even write the
profile in that time.  Thus the modified verifier is not the question-reduced
normal-form verifier asserted by that theorem, and the recursive Compression
Theorem no longer has polynomial verifier complexity.  For each fixed `n` the
enumeration is of course finite and computable; that weaker fact does not make
it a verifier family to which recursive compression applies.

Turning profiles into types is not an alternative.  The detyping construction
uses ambient dimension `4|type|+s` and its soundness loss is
`16^|type|`.  A type for every repeated control profile makes both parameters
exponential (indeed the soundness factor is doubly exponential in `K`).

## Exact missing replacement

The narrow repair would require a new **affine-fiber introspection lemma**.
For the repeated source sampler it would have to

1. use only `poly(n,lambda,ell)` question bits and sampling time;
2. introspect the full product CL distribution needed by the source verifier;
3. make every honest `Intro--Sample` support an accepted affine fiber; and
4. retain the robust soundness and entanglement extraction of the
   Introspection Theorem.

The counting argument above rules out obtaining such a lemma merely by
classically revealing `s`, `chi(s)`, or any lossless encoding of the existing
coordinatewise controls.  A successful repair must replace the repeated
sampler/encoding or prove affine safety by a different perfect strategy; it
is not a local change to the verifier's question format.

Primary-source interfaces used here are JNVWY arXiv:2001.04383v3, Definition
7.3 and equations (49)--(51) for the axis and diagonal CL controls, Theorem
8.3 for the completeness/soundness and complexity contract, and Lemma 8.20,
equations (79)--(80), for the robust reconstruction interface of the single
`SAMPLE` PVM and its `INTRO` coarse-grainings.  Exact seed uniformity is
obtained separately from the zero-error acceptance equations, as recorded in
`jnvwy-perfect-introspection-forces-full-seed-support`.
