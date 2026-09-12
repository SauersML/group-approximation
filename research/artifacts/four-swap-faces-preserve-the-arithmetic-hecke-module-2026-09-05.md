# Four swap faces preserve the arithmetic Hecke bimodule

This is a consequence of the full canonical double-swap relations, not
merely of a balanced projection and one overlap moment. It identifies
what the compressed arithmetic actor supplies and why that correspondence
alone does not provide a genuine finite-dimensional spectral seed.

## 1. Hypotheses and the four-face Gram identity

Let Lambda=SL_3(Z), Gamma=SL_3(Z[1/p]), and
h=diag(p,1,1/p), with p prime. In the canonical group algebra of

    E=Gamma *_Lambda (Lambda x C_2),

write s for the involution, B=L(Lambda), and q_a=(1+a s)/2 for
a in {+1,-1}. The same calculations hold in any trace-preserving
embedding satisfying (NBI1) in
`sl3-outliers-carry-no-balanced-free-involution`, since its prescribed
amalgamated-free moments are those of this group algebra.

For b1,b2,c1,c2 in C[Lambda] and signs a,b,c,d, one has

    tau((b1 q_a h q_b b2)^* (c1 q_c h q_d c2))
      = (delta_(a,c) delta_(b,d)/4)
          tau((b1 h b2)^* (c1 h c2)).                 (FH1)

Here group elements denote their canonical unitaries. In particular,
this identity retains every arithmetic relation between h and Lambda.

To prove it, let H_h be the closed B-bimodule span of Lambda h Lambda
inside L^2(L(Gamma)). For e,f in {0,1}, define

    J_(e,f)(xi)=s^e xi s^f.

Each J is an isometric B-bimodule map because s commutes with B.
Their four ranges are mutually orthogonal. Indeed, for group elements
g,k in Lambda h Lambda, compare s^e g s^f and s^e' k s^f'.
If just one of e,f differs, the inner product has a word of odd s-parity
and hence zero trace. If both differ, cyclicity reduces its trace to
that of s g^-1 s k. Since g,k are outside Lambda, this is a nontrivial
reduced amalgam word, again of trace zero. When neither differs, the
inner product is the original one. Linearity proves the assertion on
H_h.

Since

    q_a xi q_b=(1/4) sum_(e,f) a^e b^f J_(e,f)(xi),

orthogonality and the two-sign character identity give (FH1).
Consequently

    xi -> 2 q_a xi q_b

is a B-bimodule isometry of H_h onto the corresponding compressed
Hecke module. All four compressed modules are orthogonal.

## 2. What the actual h covariance intertwines

Put C=Lambda cap h Lambda h^-1 and phi(c)=h^-1 c h in Lambda.
For every c in C, the full arithmetic group relation gives

    u_c (q_a h q_b)=(q_a h q_b) u_(phi(c)).           (FH2)

Thus the compressed actor really is a nonzero intertwiner between
restrictions to the two commensurable subgroups. Equation (FH1) shows
that its correspondence is exactly the original h correspondence,
with its norm scaled by one half. It does not replace either of the
two source restrictions by a genuine finite-dimensional representation.

In particular, C and Lambda cap h^-1 Lambda h have finite index:
both contain the principal congruence subgroup of level p^2. As a left
Lambda representation, H_h is a finite direct sum of copies of the
left regular representation, one for each left Lambda orbit in
Lambda h Lambda. The number is

    [Lambda : Lambda cap h^-1 Lambda h].

The analogous right-module statement holds with the conjugate
intersection. By (FH1), each compressed face has precisely this same
decomposition.

## 3. A uniform obstruction to an L2 finite-dimensional seed

The regular representation of the infinite group Lambda has no
nonzero finite-dimensional invariant subspace. More quantitatively,
fix a finite Kazhdan set S and constant kappa for Lambda. For every
genuine finite-dimensional unitary representation pi, the tensor
representation pi tensor lambda_Lambda is a multiple of lambda_Lambda
by the explicit regular absorption unitary. It has no fixed vectors.
Consequently, for every vector z in pi tensor H_h,

    (1/|S|) sum_(g in S)
      ||(pi(g) tensor lambda(g)) z-z||^2
        >= (kappa^2/|S|) ||z||^2.                   (FH3)

The same estimate holds for all four compressed faces, their direct
sum, and the right-action version used for rectangular intertwiners.
There is no factor depending on dim(pi). In particular none of these
L2 correspondences contains a genuine finite-dimensional Lambda
submodule. Taking the polar decomposition of the compressed actor
can identify subspaces of the two restrictions in (FH2); it does not
change this L2 fact into a finite-dimensional target representation.

This is a failed bridge, not an exclusion of matrix microstates.
Growing finite-quotient hosts and coordinate constructions need not
arise from a vector in this fixed L2 correspondence. Neither (FH1)
nor (FH3) proves that such coordinate constructions are impossible.
To use the residual spectral exclusion, one still needs bounded
rectangular maps into genuine finite-dimensional targets with positive
normalized mass and small covariance error. Formula (FH2) provides
maps between two approximate restrictions instead.

## 4. Why four equal faces do not create a dimension contradiction

The four B-bimodules above form four copies of H_h. Left multiplication
by q_+ selects two of them, right multiplication by q_+ selects two,
and their joint compression selects one. This is consistent with
the trace-one-half projection and the four equal overlaps.

The elementary finite-matrix capacity calculation is consistent too.
If q has rank d_+ in M_d and d_-=d-d_+, the complex dimensions of
the four matrix corners are

    dim(q_a M_d q_b)=d_a d_b.

For balanced q these are asymptotically d^2/4 each. A fixed collection
of r orthonormal group elements from Lambda h Lambda gives, through
(FH1), r orthonormal L2 vectors in each compressed face after scaling
by two. In a hypothetical canonical matrix approximation their Gram
matrices converge to these fixed Gram matrices. This records a finite
dimension requirement in each corner, not an inconsistency between
the four corners. It gives no positive normalized-HS loss.

A growing collection would require uniform control of its Gram matrix
and the corresponding word defects; canonical convergence supplies
only each fixed collection. An exact finite-dimensional base could
supply additional representation multiplicity information, which is
the already excluded exact face. No such extra information on lattice
outliers follows from (FH1).

The arithmetic h covariance therefore yields a precise, nonzero
finite-index correspondence. Turning that correspondence into a
positive genuine finite-dimensional spectral seed remains unproved.
