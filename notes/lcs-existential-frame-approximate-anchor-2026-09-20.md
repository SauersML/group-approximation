# Approximate-only anchors do not authenticate the signed-six frame

Date: 2026-09-20. Bounded follow-up to
`lcs-existential-frame-signed-six-sector-2026-09-20.md`. No computation,
build, remote job, or commit was run. The distinction between value one
and attained finite-dimensional perfection is retained throughout.

The tested escape is specific: attach a signed group with approximate
matrix models but no exact finite-dimensional negative representations,
and use it to select the natural six-dimensional finite-frame type in
every matrix-ultraproduct model. The following explicit amplification
rules out that type-selection interface even when the infinite anchor is
coupled to the whole presentation. It does not rule out every use of an
approximate-only anchor or every non-word decoder.

## 1. What the approximate-only input really supplies

The primary [Slofstra v2 paper](https://arxiv.org/html/1703.08618) was read
again, including Proposition 5.1, Lemma 3.9, and Proposition 3.4. Its fixed
solution group Sigma has a central involution J which is trivial in
every exact finite-dimensional representation, but survives approximate
representations. Lemma 3.9 supplies arbitrarily accurate normalized-HS
matrix approximations with J exactly -I and generator involutions exact.
This gives perfect value without exact finite-dimensional attainment.

Repository checks also covered `slofstra-involution-not-sofic-radical`,
`slofstra-natural-negative-corner-image-is-sofic`,
`perfect-decoding-does-not-imply-quantum-value-gap-citation`, and the full
`ce-affine-quotient-audit-2026-09-20.md` argument. In particular the general
idea of regularizing a CE image by trace amplification is prior work
here. The formulas below specialize it to the actual new frame candidate
and its explicit forbidden projection; no new canonical theorem is proposed.

## 2. Explicit attachment: all exact models disappear, but not the ghosts

Let T(G) be the marked presentation from the signed-six note for a finite
loopfree graph G. That note supplies an exact matrix representation pi_G
with J=-I for every G, including uncolourable graphs, and including the
full commuting transported frame packets.

Form the commuting central product

    Q(G)=(Sigma x T(G)) / <(J_Sigma,J_T)>.             (1)

Equivalently identify the two central signs and require all generators
from the two presentations to commute. If sigma_n is a marked matrix
approximation of Sigma, represent the two families by

    s -> sigma_n(s) tensor I,
    t -> I tensor pi_G(t).                            (2)

Both copies of the common sign act as -I. All mixed commutations and all
T(G) relations are exact; only Sigma's original relations have error.
For each fixed graph those errors tend to zero. The same conclusion holds
for any fixed positive weighted energy on this finite presentation.

On the other hand Q(G) has NO exact finite-dimensional representation
with J=-I: its restriction to Sigma would contradict Proposition 5.1.
Thus this construction really has the proposed approximate-only status,
for every graph, while its matrix-energy infimum is zero for every graph.
Deleting exact finite models has not created any soundness distinction.

The presentation remains linear-plus-conjugacy: Sigma is a fixed LCS,
the other packet already has that syntax, and mixed commutations are
conjugacies. Since Sigma is fixed, its relations and mixed checks add
only constant-size bundles per existing role. This observation concerns
local access, not a hardness reduction.

## 3. A coupled approximate-only selector also fails the whole-type test

The preceding example used a commuting attachment. Now allow arbitrary
ordinary relations coupling the infinite anchor, frame, transporters, and
source-specific auxiliaries. Let Gamma be that complete signed group.
Assume only that it has ONE CE tracial representation rho with J=-I in
which the signed-permutation frame

    K=(C_2)^6 semidirect S_6

has the natural six-dimensional character, with arbitrary multiplicity.
This is precisely the designated-sector model used for completeness in
the preceding frame construction. No exact finite-dimensional model of
Gamma is assumed, and no extension of all honest source models is assumed.

Choose unitary matrix lifts rho_n of this CE model, of dimension d_n, so
that the defining relator defects tend to zero and every fixed-word trace
converges to the trace of rho. If the presentation's generators are
involutions they can be chosen as exact self-adjoint involutions: round
unitary lifts spectrally, which changes them by vanishing normalized
2-norm. Set the marked lift J exactly -I. These choices do not turn the
other relators into exact equalities.

For an integer m>=0 define, on free-group words g,

    B_n(g)=I_(d_n^2) direct-sum
                     (rho_n(g) tensor conjugate(rho_n(g))),
    R_(n,m)(g)=rho_n(g) tensor B_n(g)^(tensor m).       (3)

The trivial and conjugate-tensor summands of B_n have EQUAL dimension.
Consequently this is an ordinary direct-sum/tensor amplification whose
normalized character is

    chi_(n,m)(g)=chi_n(g)
                       ((1+|chi_n(g)|^2)/2)^m.         (4)

It preserves the marked scalar exactly: B_n(J)=I and R_(n,m)(J)=-I.
It also preserves exact involutivity of every generator. For each defining
relator r, if `||rho_n(r)-I||_2<=epsilon_n`, then

    ||B_n(r)-I||_2<=2 epsilon_n,
    ||R_(n,m)(r)-I||_2<=(2m+1) epsilon_n.             (5)

These are the tensor-product telescoping bounds. They apply to EVERY
relator of the full coupled presentation, not just to anchor relators.
For fixed m the new defects still tend to zero. With a common relator
energy convention their squared weighted sum increases by at most
`(2m+1)^2`; changing a row into its finitely many defining relators only
changes a fixed presentation constant.

Thus R_(n,m) yields another CE model of the SAME marked group for each m.
In particular additional source-dependent word relations which hold in
the starting CE model cannot prohibit this construction.

## 4. An exact positive forbidden-pattern mass

In K use the same three A_a as in the signed-six note: A_a flips the two
coordinates whose first colour is a. They commute and satisfy

    A_0 A_1 A_2=J.

On the J=-I sector the joint triple-minus projection is

    b=product_(a=0,1,2) (I-A_a)/2
     =(I-A_0-A_1-A_2)/4.                              (6)

The second equality follows by expanding the product and replacing
`A_a A_b` by `-A_c`. In the natural six-dimensional frame b=0 and

    chi(A_a)=1/3.

Taking n to the CE limit in (4) gives

    chi_m(A_a)=(1/3)(5/9)^m,
    tau_m(b)=(1-(5/9)^m)/4.                           (7)

Already m=1 gives `tau_1(b)=1/9`. The full presentation has vanishing
relation defects, while the forbidden anchor projection has squared
2-norm 1/9 in the limit. No estimate forcing b to vanish with the target
energy can hold for this interface. At finite n the polynomial in (6)
need only be an approximate projection; all its moments converge to the
displayed projection moments in the tracial ultraproduct. No unsupported
finite-dimensional exactification is used.

This is not the old requirement to extend three distinct scalar source
solutions. It starts from ONE chosen CE model of one fully coupled
presentation, even a presentation with no exact negative matrix models.
What fails is the assertion that all its matrix-ultraproduct models must
retain that chosen finite-frame type.

## 5. The limiting anchor is precisely the unwanted regular sector

For completeness the entire frame character can be read off. A signed
permutation matrix of size six has normalized trace at most 2/3 in
absolute value unless it equals I or -I. Indeed a nonidentity permutation
has at most four fixed coordinates; and a diagonal sign matrix other
than +/-I has absolute trace at most four. Therefore (4) gives

    |chi_m(k)| <= (2/3)(13/18)^m
                      for k in K minus {I,J},
    chi_m(I)=1,   chi_m(J)=-1.                        (8)

As m grows the restriction to K converges to the normalized character of
the J-negative regular corner. This is exactly the sector used in the
signed-six countermodel, not a finite-quotient argument requiring an
exact finite-dimensional representation of Gamma. A diagonal choice of
n and m, with `(2m+1)epsilon_n -> 0` and the required finite-word traces
accurate, realizes the limiting character by matrix microstates.

The natural irreducible type has normalized mass

    6^2 / (|K|/2) = 1/640                             (9)

in that limiting frame restriction. This is POSITIVE, not zero. Therefore
the calculation does not rule out a separately proved positive-weight
proper-corner extraction, or a non-word replacement decoder. The
isotypic projection in (9) commutes with K, but it need not commute with
the transporters, source observables, or the rest of Gamma. No common
reducing property or globally consistent compression follows from (9).

## 6. Scope and outcome

The absence of exact finite-dimensional negative representations is a
real feature of Slofstra's anchor and survives (1). It does not provide
the missing nonlinear frame authentication: (2) retains the global graph
countermodels as approximate models, while (3)--(7) defeat whole-type
selection even for arbitrary coupled word presentations possessing the
specified natural-frame CE model.

This is a quantitative specialization of the repository's existing
CE image/trace-amplification machinery, not a new general impossibility
theorem. It leaves open a source-specific approximate construction using
genuinely different readouts or a proved consistent type-corner decoder.
No HALT-positive source or perfect-completeness LCS hardness reduction is
obtained.
