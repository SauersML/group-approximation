# Noisy direction decoding refutes the affine orientation-glue lemma

Date: 2026-09-07. Status: a complete mathematical counterexample to the
repository's proposed analytic lemma, with finite exact regression checks.
This is **not a proof or a disproof of the Unique Games Conjecture**, and no
Lean verification or priority claim is made.

## 1. Statement and quantifiers

Let `Omega = F_2^(2m)`, `N = 4^m`, and let `D_b` identify coordinates in
the pairs `{x,x+b}` for every nonzero `b`. For each fixed `0 < rho < 1`,
there are folded Boolean functions

```text
f_N : {-1,1}^Omega -> {-1,1},       f_N(-Y) = -f_N(Y),
```

and selected cosets `C_b` in **every** nonzero direction such that, for all
sufficiently large `m`, with `g_N = T_rho f_N`,

```text
Inf_C_b^{<=1}(g_N|D_b) >= rho^2/4              for every b != 0,    (1)
|{b != 0 : C_b intersects Q}| <= 2|Q|         for every Q.          (2)
```

The same explicitly defined `f_N` works for all fixed positive `rho`, with
the dimension threshold depending on `rho`. Here `T_rho f(X)` is the
expectation of `f(Y)` when independently `Y_x=X_x Z_x` and
`Pr[Z_x=1]=(1+rho)/2`. Influence is the sum of squared Fourier coefficients
containing the indicated coordinate, truncated to the stated degree, under
the uniform measure on the quotient cube.

In particular, fix `rho=1/2`, `d=1`, `delta=1/16`, and `alpha=1`. If the
glue lemma supplied constants `L` and `gamma>0`, take a sufficiently large
power of four with `N-1>2L/gamma`. All its hypotheses hold, whereas every
set of size at most `L` hits a fraction at most `2L/(N-1)<gamma`. This
contradicts its conclusion with the parameters fixed before the dimension.

## 2. A selector with bounded incidence

Identify `Omega` with `F_4^m`, and write `omega^2+omega+1=0`. Let
`J(x)=omega x`. Equivalently, on each binary coordinate pair set

```text
J(a,b) = (b,a+b).
```

Thus `J^2+J+I=0`, and both `J` and `J+I=J^2` are bijections. Choose

```text
q_b = Jb,                 C_b = {Jb, Jb+b} = {Jb,J^2b}.           (3)
```

The difference of the endpoints is `b`, as required. Every nonzero point
is an endpoint for exactly two different directions, and zero is an
endpoint for none. Counting incidences proves (2), including sets
containing zero.

There is also an exact description of all intersections. The nonzero
vectors split into orbits `{b,Jb,J^2b}` of size three. The three selected
cosets in an orbit are the three edges of the triangle on that orbit.
Different orbits have disjoint endpoints. Consequently

```text
Pr_(b,c uniform nonzero)[C_b intersects C_c] = 3/(N-1).            (4)
```

For distinct nonzero `b,c`, the three cosets `C_b,C_c,C_(b+c)` never
share a point: if the first two intersect, their directions lie in one
orbit and the three cosets are the three edges of its triangle. This
also rules out the stronger three-line star certificate.

## 3. One Boolean function learns the noisy direction

For a Boolean vector `Y`, define its score in direction `c != 0` by

```text
A_c(Y) = (1/N) sum_(x in Omega) Y_x Y_(x+c).
```

Let `bhat(Y)` maximize these scores, breaking ties by the ordinary order
of their binary encodings. Define the single ambient function

```text
f_N(Y) = Y_(J bhat(Y)).                                          (5)
```

This definition has no access to the direction on which it will later be
restricted. It is Boolean on every input, including ties and atypical
inputs. The scores are unchanged by `Y -> -Y`; hence (5) is folded and
balanced under the ambient uniform measure.

Fix a planted direction `b`. Sample `X` uniformly from `D_b` and obtain
`Y` from `X` with the independent noise above. Different `b`-pairs are
independent. Inside one pair, both signs have mean zero and

```text
E[Y_x Y_(x+b)] = rho^2.
```

Let `M=N/2`. The true score `A_b` is the average of `M` independent
variables in `[-1,1]` with mean `rho^2`. Therefore

```text
Pr[A_b <= rho^2/2] <= exp(-N rho^4/16).                           (6)
```

For `c != 0,b`, partition `Omega` into the `N/4` cosets of `<b,c>`.
On a coset represented by `x`, put

```text
W_x = (Y_x Y_(x+c) + Y_(x+b) Y_(x+b+c))/2.
```

These block variables lie in `[-1,1]`, are independent across cosets,
and have mean zero: each summand connects two independent, mean-zero
`b`-pairs. Directly counting the two copies of each undirected `c`-edge
in the score shows that `A_c` is the average of these `N/4` variables.
Thus

```text
Pr[A_c >= rho^2/2] <= exp(-N rho^4/32).                           (7)
```

No independence between scores in different directions is asserted or
needed. A union bound over the `N-2` wrong directions gives, uniformly
for each fixed planted `b`,

```text
Pr[bhat(Y) != b]
  <= exp(-N rho^4/16) + (N-2) exp(-N rho^4/32)
  <= (N-1) exp(-N rho^4/32) =: e_N.                              (8)
```

The sufficient event is strict separation of the true score above
`rho^2/2` from every wrong score below it; ties are included in the error
bound. Fixed positive `rho` implies `e_N -> 0`.

For completeness, the bounded-variable concentration inequality used in
(6)--(7) follows as follows. If `V` is supported on an interval of length
two, the second derivative of `log E exp(tV)` is a variance under an
exponential tilt, at most one. (For a variable in `[a,b]`, subtract its
mean in `E[(V-a)(b-V)]>=0` to get variance at most `(b-a)^2/4`.)
Integrating twice at zero gives
`E exp(t(V-EV)) <= exp(t^2/2)`. Multiply this bound for `s` independent
variables, apply Markov's inequality, and minimize at `t=u` to obtain
`Pr[s^(-1) sum(V_i-EV_i) >= u] <= exp(-s u^2/2)`. Apply the same argument
to `-V_i` for the lower tail. Substitution of `s=N/2` or `N/4` and
`u=rho^2/2` gives precisely (6) and (7).

## 4. Noise precedes restriction, and a heavy coefficient survives

On the event of correct decoding, (5) equals `Y_(q_b)`. Since both
quantities are signs, their absolute difference is at most twice the
error indicator. Write `h_b=(T_rho f_N)|D_b`. Conditional on `X`,
`E[Y_(q_b)|X]=rho X_(q_b)`, so Jensen's inequality and (8) give

```text
E_(X uniform D_b) |h_b(X)-rho X_(q_b)| <= 2 e_N.                 (9)
```

This is the actual operation in the proposed glue lemma: apply ambient
noise first, then restrict. It is not the generally different operation
of restricting `f_N` and then applying quotient noise.

The quotient singleton character for `C_b` is `X_(q_b)`, with square one.
Multiplying (9) by that character inside the expectation yields

```text
|hat h_b({C_b}) - rho| <= 2 e_N.                                (10)
```

For large enough `N`, `e_N <= rho/4`. Hence the coefficient is at least
`rho/2`, and its square gives (1). This conclusion holds for every
direction, using one and the same ambient function.

An explicit sufficient threshold for the fixed counterexample is
`rho=1/2`, `N=4^m >= 16384`. At `N=16384`, (8) is less than
`16384 exp(-32) < 2^14/2^32 = 2^-18 < 1/8`, using `e>2`.
The function `(N-1)exp(-N/512)` decreases for `N>513`, so all larger
powers of four also satisfy `e_N<rho/4`. No numerical approximation of an
exponential is necessary for this threshold certificate.

## 5. What is refuted, and what remains open

Equations (1)--(2) refute `affine-orientation-glue-lemma` as stated.
Equation (4) refutes the positive-density pair-concurrency conclusion
in `affine-orientation-triangle-defect-is-small`, even if its requested
near-one density is weakened to any fixed positive density.

The conditional star-degree averaging theorem remains valid; its analytic
hypothesis is what fails. The quadratic special case is also untouched:
(5) is nonlinear in all the direction scores and has no fixed ambient
degree bound. This is neither a linear superposition of the previous
pair memorizers nor a counterexample to their sup-norm lower bound.
Folding and fixed positive noise do not repair the proposed lemma, since
the construction already satisfies both requirements.

The statement `glue-lemma-implies-rich-2to1-hardness` must not be mistaken
for a usable reduction after its antecedent has been refuted. Its old
conditional route cannot establish hardness. A replacement needs a
different analytic hypothesis together with an actual reduction; neither
is supplied by this counterexample.

## 6. Literature and novelty boundary

Checked on 2026-09-07:

* [Braverman--Khot--Minzer, *On Rich 2-to-1 Games*, ITCS 2021](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2021.27),
  Definition 5 and Theorem 8: richness uses all perfect pairings, and its
  hardness conjecture is equivalent to UGC. Section 1.3 distinguishes
  the linear-pairing family from that larger family and proposes enriching
  the former. Our construction concerns only the linear-pairing family.
  It does not contradict their theorem or their analytic results for
  uniformly random pairings.
* [Dawar--Molnar, *Undefinability of Approximation of 2-to-2 Games*, v2](https://arxiv.org/html/2504.03523v2),
  revised 2026-03-01, still identifies UGC as an open problem. Logical
  undefinability results are not a proof of its NP-hardness assertion.

Repository lexical and Cairn searches found the linear memorizers and
their nonlinear escape route, but no noisy direction classifier. Searches
for linear pairings with noise/influence, Rich 2-to-1 counterexamples, and
noisy hidden-shift autocorrelation did not identify this exact construction.
That search is not a priority certificate. This document claims an explicit
proof against a precisely identified repository statement, not a new
resolution of a published open problem. No independent code or supplement
establishing this construction was identified; exhaustive prior-art review
has not been completed.

## 7. Reproduction and certificate scope

Run from the repository root:

```sh
python3 scripts/check_unique_games_noisy_direction.py --check
```

The standard-library-only checker exhausts all ambient Boolean inputs for
`N=4,16`, computes ambient noise with exact integer arithmetic, and then
extracts every selected quotient coefficient. It independently evaluates
the planted distribution to check the decoding-error/coefficient estimate.
It checks the block means, all small hitting sets for `N=16`, the selector's
incidence identities up to `N=16384`, folding, and the rational sufficient
threshold above. The deterministic output is stored beside this proof.

These checks detect implementation and normalization errors. The universal
counterexample is established by Sections 1--4, not by finite exhaustion,
sampling, or a claim that Cairn verifies mathematical arguments.
