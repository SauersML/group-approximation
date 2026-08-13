# Perfect completeness versus Fourier damping in the LCS long-code test

Date: 2026-08-13

## 1. Scope

Taller--Vidick's test samples a mask

\[
 \mu:\{\pm1\}^{W}\longrightarrow\{\pm1\},
 \qquad
 g'=fg\mu,
 \tag{PCM1}
\]

and tests one linear equation involving the three long-code queries attached
to `f`, `g`, and `g'`.  For the honest dictator indexed by an assignment
`phi`, the equation is satisfied exactly when

\[
 \mu(\phi)=1.
 \tag{PCM2}
\]

Independent noise with
`P(mu(phi)=-1)=epsilon` therefore gives completeness `1-epsilon`.  In the
soundness proof it gives the Fourier multiplier

\[
 \mathbb E_\mu\chi_\beta(\mu)
   =(1-2\epsilon)^{|\beta|},
 \tag{PCM3}
\]

whose exponential decay pays for choosing one element uniformly from the
decoded Fourier set `beta`.

This note records why changing only the mask distribution cannot make this
test perfectly complete while retaining the same decoding mechanism.  It
does not rule out a different perfect-completeness LCS compiler.

## 2. Full-support honest strategies force degenerate noise

Let `C` be the set of satisfying assignments for the sampled source
constraint and let `P_phi`, `phi in C`, be the projections in the honest
perfect strategy.  Put

\[
 S=\{\phi\in C:\tau(P_\phi)>0\}.
 \tag{PCM4}
\]

For an arbitrary distribution `D` on masks, the honest loss is

\[
 \mathbb E_{\mu\sim D}
 \sum_{\phi\in S:\,\mu(\phi)=-1}\tau(P_\phi).
 \tag{PCM5}
\]

Every summand is nonnegative.  Hence perfect completeness is equivalent to

\[
 \mu(\phi)=1
 \quad\text{for every }\phi\in S,
 \quad D\text{-almost surely}.
 \tag{PCM6}
\]

In particular, if the honest measurement has full support on `C`, then
`mu|_C=1` almost surely.  For every Fourier set `beta subset C`, this gives

\[
 \mathbb E_{\mu\sim D}\chi_\beta(\mu)=1.
 \tag{PCM7}
\]

Thus perfect completeness deletes the damping on precisely the Fourier
coefficients which survive conditioning upon `C`.  Setting `epsilon=0` is
not merely a singularity in the published estimate: within this test
family it restores every high-degree character as an undamped exact
solution.

## 3. Tailored noise outside the honest support

The only distributional repair left by `(PCM6)` is to put noise outside
`S`.  Suppose, most favorably, that the mask bits on `C minus S` are
independent with mean

\[
 q=1-2\epsilon\in(0,1)
 \tag{PCM8}
\]

and are identically `1` on `S`.  Then

\[
 \mathbb E_\mu\chi_\beta(\mu)
   =q^{|\beta\setminus S|}.
 \tag{PCM9}
\]

Write `m=|S|` and `r=|beta minus S|`.  Since `beta` is nonempty,

\[
 |\beta|\le m+r.
 \tag{PCM10}
\]

Consequently the published Fourier decoder still gives a positive constant,
but only the constant

\[
 c_{m,q}^{,2}
 :=\inf_{r\ge0}\frac{q^{-2r}}{m+r}
 =\left(\sup_{r\ge0}(m+r)q^{2r}\right)^{-1}.
 \tag{PCM11}
\]

Indeed

\[
 |\beta|^{-1/2}
 \ge c_{m,q}\,q^{|\beta\setminus S|}.
 \tag{PCM12}
\]

The constant is positive because exponential decay dominates `m+r`.
However the case `beta subset S` already forces

\[
 c_{m,q}^{,2}\le\frac1m.
 \tag{PCM13}
\]

This is not an artifact of the estimate.  When `beta=S`, the decoder in
Taller--Vidick measures `beta` and chooses one of its elements uniformly.
Without damping on `S`, its worst-case agreement probability is exactly
`1/m`.

## 4. The random-guessing floor closes the repair

First delete, nonuniformly, every answer projection which is zero in the
chosen perfect commuting strategy.  This preserves perfect completeness and
can only decrease the finite-dimensional value.  Let `m` be the largest
remaining answer-support size on the projection game's pair-question side;
the support on a single-question side has size at most `m` because it is a
marginal of a supported pair measurement.

The restricted projection game has a classical strategy of value at least
`1/m`.  For every pair-question choose one supported answer.  Perfectness
implies that it has at least one compatible supported answer to either
single question: summing the joint overlaps against the complete marginal
PVM gives the positive trace of the chosen projection, and every losing
overlap is zero.  The single-question player now answers uniformly from at
most `m` supported labels.  The compatible label is hit with probability at
least `1/m` on every sampled edge.

In the `u`-fold repeated source used by the long-code compiler, the largest
honest pair-answer support is at most `m^u`, while the same random-guessing
argument gives source value at least `m^{-u}`.

The tailored-noise decoder can therefore force at most

\[
 \omega_q(G^{\otimes u})\ge \frac{\delta^2}{m^u},
 \tag{PCM14}
\]

up to the fixed consistency constants.  The source game itself has the
matching universal lower bound `m^{-u}`.  Parallel repetition can
drive both quantities down, but it cannot turn the non-strict baseline
comparison into the strict inequality needed for soundness.  Any constant
loss in the consistency estimates makes the comparison worse.

Hence:

> **Mask-only no-go.**  In the distorted long-code architecture, a mask
> distribution which is perfectly complete for a full-support honest
> strategy has no Fourier damping on the conditioned spectrum.  If noise is
> restricted to the complement of a smaller honest support, the surviving
> decoder is bounded by the source game's random-guessing floor.  Changing
> only the mask distribution cannot yield a perfectly complete constant-gap
> LCS reduction by the published decoder.

## 5. Correction variables and the same obstruction

One can add a fourth answer intended to equal `mu(phi)` and replace the
failing equation by

\[
 f(\phi|_U)g(\phi)g'(\phi)\mu(\phi)=1.
 \tag{PCM15}
\]

The honest strategy is then perfect: on a query containing `(W,mu)`, the
player measures `phi` and returns `mu(phi)`.  But an arbitrary Fourier
character `chi_beta` also satisfies `(PCM15)` exactly, because

\[
 \chi_\beta(f)\chi_\beta(g)
 \chi_\beta(fg\mu)\chi_\beta(\mu)=1.
 \tag{PCM16}
\]

Thus the correction answer restores the entire high-degree character
space.  Testing that correction answer is a dictator merely repeats the
same problem.  More generally, the exact solutions of homogeneous XOR
constraints are closed under pointwise multiplication; once all dictators
are accepted perfectly, their odd products cannot be excluded by further
homogeneous linear equations alone.

## 6. Consequence for the active program

The `epsilon=0` endpoint cannot be obtained by any of the following local
changes to the Taller--Vidick test:

1. set the mask to `1`;
2. put noise only outside the support of one honest strategy;
3. expose the mask evaluation as an additional linear answer; or
4. recurse on a linear test of that additional answer.

A successful construction must add a genuinely non-XOR source-specific
rigidity mechanism and then compile that mechanism into solution-group
relations, or bypass the long-code architecture altogether.  The remaining
one-instance target is still the exact perfect-linearization program in
`HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md`; the independent explicit target is
the reduced-Fourier Leavitt gate `(RPC128)`.
