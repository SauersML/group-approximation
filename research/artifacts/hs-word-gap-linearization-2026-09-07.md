# A fixed Hilbert--Schmidt word gap already gives linear domination

2026-09-07. **Status:** the reduction below is proved. No group-specific
gap, nontrivial hyperlinear-radical element, or nonhyperlinear group is
constructed. This is an elementary specialization of the tensor-power
method already used in `GroupApproximation/Domination/Core.lean`; it is
not a claim of a new amplification method or a Lean verification result.

## 1. Statement with the scalar phase retained

Let S be a finite alphabet, R a finite set of words in the free group F(S),
and w another word. No presentation or nontriviality assumption is needed
for this lemma. For a unitary tuple U in U(d)^S, d >= 1, set

```text
e_v(U) = ||v(U)-I||_(2,d)^2 = 2-2 Re tr_d(v(U)),
delta_R(U) = max_(r in R) ||r(U)-I||_(2,d).
```

The maximum over an empty set is defined to be zero. All traces and HS
norms are normalized by the dimension of their own matrix algebra.

Suppose eta > 0 and, in **every** dimension,

```text
||w(U)-I||_2 >= 1  ==>  delta_R(U) >= eta.             (GAP)
```

Then in every dimension and for every tuple,

```text
||w(U)-I||_2 <= (2/eta) delta_R(U).                    (LIN)
```

Conversely, (LIN) with any positive constant C in place of 2/eta implies
(GAP) with eta=1/C. Thus existence of a fixed gap at distance one and
existence of a global linear bound are equivalent. The constants in the
two conversions need not be optimal.

This is an ordinary HS bound: it controls a nontrivial scalar w(U) as well
as a nonscalar matrix. The projective defect 1-|tr(w(U))|^2 used in the
existing character-domination interface vanishes on every scalar matrix.

## 2. A word-compatible real, nonnegative trace

For each generator s define the 4d-dimensional unitary

```text
T(U)_s = U_s (+) conjugate(U_s) (+) I_d (+) I_d.
```

Here conjugate means entrywise complex conjugation, not taking the adjoint
of each generator. Entrywise conjugation, direct sum, and tensor power
preserve multiplication and inverse. Therefore, for every free-group word v,

```text
v(T(U)) = v(U) (+) conjugate(v(U)) (+) I_d (+) I_d,
tr_(4d)(v(T(U))) = (1+Re tr_d(v(U)))/2
                 = 1-e_v(U)/4 in [0,1].              (TRACE)
```

The two identity blocks are essential for this particular formula. Using
only U tensor conjugate(U) would erase a scalar phase; using only
U (+) conjugate(U) could leave a negative trace.

Let A_k(U)_s = T(U)_s^(tensor k), for an integer k >= 1. Its dimension is
(4d)^k, and word evaluation commutes with this construction. Normalized
trace is multiplicative on tensor products, so exactly

```text
e_v(A_k(U)) = 2[1-(1-e_v(U)/4)^k].                    (POWER)
```

In particular, Bernoulli's inequality gives

```text
e_v(A_k(U)) <= (k/2)e_v(U),
delta_R(A_k(U))^2 <= (k/2)delta_R(U)^2.                (ERROR)
```

The second inequality also holds when R is empty. There are no word-length
constants: these are identities for evaluated words, not successive
estimates for approximate multiplication.

## 3. Proof of linearization, with no asymptotic choice

Fix U, and put a=e_w(U). If a=0, (LIN) is immediate. Otherwise 0<a<=4.
Choose

```text
t = a/4 in (0,1],       k = ceil(1/t) = ceil(4/a).
```

We have kt>=1 and ka<=4+a<=8. For 0<=t<=1,

```text
(1-t)^k <= 1/(1+kt).                                  (B)
```

For t<1, apply Bernoulli to
`(1-t)^(-k) = (1+t/(1-t))^k >= 1+kt/(1-t) >= 1+kt`
and invert positive numbers. For t=1 the left side is zero. Consequently
`(1-t)^k<=1/2`, and (POWER) gives

```text
e_w(A_k(U)) >= 1.
```

Apply (GAP) at the actual amplified dimension (4d)^k and then (ERROR):

```text
eta^2 <= delta_R(A_k(U))^2
      <= (k/2)delta_R(U)^2
      <= (4/a)delta_R(U)^2.
```

Multiplying by a and taking nonnegative square roots proves (LIN).
The proof handles a=4 and delta_R(U)=0; it never divides by the relator
defect. Crucially, the gap hypothesis is dimension independent. A gap
known only up to some dimension cannot be applied at (4d)^k.

## 4. The repository's whole-tuple gap

For a finite presentation Q=<S|R>, put

```text
D_2(U)=max_(s in S)||U_s-I||_2,       d_2(U)=delta_R(U).
```

The open assertion `saturated-group-hs-relator-defect-gap` is
`D_2(U)>=1 ==> d_2(U)>=eta`. For any generator s, the premise
`||U_s-I||_2>=1` implies `D_2(U)>=1`. Apply the lemma with w=s, then take
the maximum over S. This proves

```text
(HSG) ==> D_2(U) <= (2/eta)d_2(U) for every U.         (TUPLE)
```

The reverse follows with eta=1/C from any bound D_2<=C d_2. Together
with `padding-makes-local-hs-rigidity-global`, three formulations are
equivalent: a fixed separated-tuple gap, global linear collapse to the
trivial tuple, and linear collapse in any fixed neighbourhood of that
tuple. This does not establish any of them for the saturated group.

For the usual contradiction with hyperlinearity, it suffices that Q is
nontrivial. At least one generator is then nontrivial, and its canonical
microstates have distance tending to sqrt(2) from I. Infinitude and
torsion-freeness do not imply that *every* generator in an arbitrary
presentation is nontrivial; redundant identity generators are allowed.

## 5. Checks and prior context

`experiments/hs_word_gap_amplification_check.py` replays (TRACE), (POWER),
and (ERROR) by evaluating words on explicit finite monomial matrices with
Gaussian-unit entries. It includes noncommuting generators, inverse words,
scalar i and -1, identity padding, and tensor powers. A separate exact
rational grid checks the scalar bounds and the ceiling choice in section 3.
These finite checks do not test or prove (GAP) for any candidate group;
the proof of the implication is sections 2--3.

The repository already contains qualitative-to-linear tensor arguments in
`character-domination-collapse-equivalences` and
`matrix-phase-linear-from-affine-tensors-proof`. The contribution here is
the explicit, scalar-sensitive transform (TRACE), the constant 2/eta,
and its application to the existing (HSG) formulation, without importing
an operator-norm statement. Classical amplification background is also
available in [Pestov, An introduction to hyperlinear and sofic groups](https://www.math.cmu.edu/~eschimme/Appalachian/PestovNotes.pdf).

For the status of the larger question, the April 2026 revision of
[Taller--Vidick, Approximating the quantum value of an LCS game is RE-hard](https://arxiv.org/abs/2507.22444v2)
still distinguishes near-perfect completeness from the perfect-completeness
result that would imply nonhyperlinear existence. This literature check
was made on 2026-09-07. Nothing in the present amplification removes
that missing hypothesis.
