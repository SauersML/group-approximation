# A sharp obstruction in the quantum extension attack

Research derivation, 2026-09-07. These are conditional structural theorems
for split cellular maps, not a proof of Gottschalk's conjecture. The
argument below distinguishes a local completely positive map from an
algebra homomorphism. Confusing those maps would falsely close the proof.

## 1. Setup and results

Let G be infinite and A,B finite nonempty alphabets. Let

    tau:B^G -> A^G,    sigma:A^G -> B^G,    sigma tau=id

be cellular maps. As in the
[decoder-fiber proof](gottschalk-decoder-fibers-2026-09-07.md), the group
action is (h.x)(g)=x(h^{-1}g). Memories N for tau and M for sigma contain
the identity; a memory N means that the output at g reads gN.

Choose a constant b in B^G and put c=tau(b), also constant. Let C_b and
C_c be the configurations differing from b and c at finitely many sites,
and let H_b=ell^2(C_b), H_c=ell^2(C_c). The map

    V:H_b -> H_c,    V|x>=|tau(x)>

is an isometry. Write P=VV*. For a finite F subset G, let A_F be the full
matrix algebra acting on the A-spins in F and identically outside F.
The norm closure of the union of these finite-region algebras in B(H_c)
is the quasilocal spin algebra A_G. Define B_G on H_b in the same way.
For countable G these are the usual uniformly hyperfinite spin algebras;
the finite-region definition also works for uncountable G.

**Theorem.**

1. The compression Phi(O)=V*OV restricts to a unital completely positive
   contraction A_G -> B_G. It has the explicit locality bound

       Phi(A_F) subset B_(F M^{-1} N^{-1} N).                 (2)

2. If tau is not onto, its range projection satisfies the sharp bound

       dist(P,A_G)=1/2.                                    (3)

3. If tau is not onto, some finite-region unitary Q satisfies

       ||Phi(Q*Q)-Phi(Q*)Phi(Q)||=1.                        (4)

   Thus Phi has a maximal multiplicative defect. If tau is onto, Phi is
   an isomorphism of the quasilocal algebras, with a local inverse.
4. A unital *-homomorphism A_G -> B_G extending the diagonal pullback
   f -> f composed with tau exists if and only if tau is onto. No
   locality assumption on that hypothetical homomorphism is needed.

Parts 1 and 3 also hold for finite G. Infinitude is essential in (3): for
finite G the entire algebra B(H_c) is a finite-region algebra.

## 2. The finite-support range and the compression

Locality gives tau(C_b) subset C_c and sigma(C_c) subset C_b. Injectivity
of tau follows from sigma tau=id, so its linear extension V is an
isometry. The closed image Y=tau(B^G) satisfies

    tau(C_b)=Y intersect C_c.                              (5)

Indeed if y belongs to the right side, sigma(y) is in C_b and
tau sigma(y)=y. Thus P is the diagonal projection onto the configurations
in (5).

The formula Phi(O)=V*OV is unital because V*V=I. At each matrix level it
is compression by a direct sum of copies of V, so it preserves positive
operators at every matrix level; this is complete positivity. Its norm
is at most one by the operator norm inequality. No claim that V is onto
has been used.

To prove locality, let O act only on F. For finite configurations x,y,

    <x|Phi(O)|y>
      = O_(tau(x)|F,tau(y)|F)
        times 1_{tau(x)|G\F=tau(y)|G\F}.                  (6)

If the second factor is nonzero, applying the decoder shows that x,y
can differ only on D=F M^{-1}. This step uses sigma tau=id, not an
inverse on arbitrary output configurations.

When x,y agree off D, their encoded outputs agree off D N^{-1}.
Consequently the equality test in (6) need only be made on
(D N^{-1})\F. Its input coordinates lie in D N^{-1} N. The first
factor in (6) reads only FN, also contained in D N^{-1} N since both
memories contain the identity. Put L=D N^{-1} N.

The matrix in (6) therefore vanishes unless x,y agree off D subset L,
and otherwise its entries depend only on x|L,y|L. Explicitly it is a
matrix on B^L with zero entries when the two L-patterns disagree on L\D,
tensored with the identity on the complement. This proves (2). Extending
by norm continuity gives the asserted map on the quasilocal algebra.

On diagonal finite-region observables the map is exactly

    Phi(D_f)=D_(f composed with tau),                       (7)

so it is multiplicative on the diagonal subalgebra. That fact says
nothing by itself about off-diagonal matrix units.

## 3. A sharp distance from the range projection to local operators

Suppose Y is proper. There exists u in C_c\Y. For example the localized
reverse-error construction in Section 2 of the decoder-fiber proof gives
R(u) != u for R=tau sigma, and Fix(R)=Y. Alternatively choose a finite
cylinder disjoint from Y and fill its unspecified sites by c.

Given a finite F, choose h with the support of h.u relative to c
disjoint from F. This is possible because G is infinite and the two
sets in question are finite. Invariance of Y implies h.u is outside Y,
whereas c is in Y. Thus

    P|c>=|c>,    P|h.u>=0,

and the two basis configurations agree on F. For any operator O in A_F,
including one with off-diagonal entries, their diagonal expectations of
O are the same complex number a. Hence

    ||P-O|| >= max(|1-a|,|a|) >= 1/2.

This bound passes to the norm closure A_G. Conversely I/2 belongs to A_G
and ||P-I/2||=1/2, because P is a nonzero proper orthogonal projection.
This proves (3).

In particular O -> VOV* cannot take all input local observables into
A_G: it sends the identity to P. A finite-algebra argument cannot simply
place this range projection in A_G. Passing instead to B(H_c) allows
proper isometries and removes the finiteness that argument needs.

## 4. The multiplicative defect is witnessed by a local unitary

Let u be as in Section 3, and let F contain its finite support relative
to c. Choose Q in A_F to transpose the distinct patterns c|F and u|F
in the standard basis, fixing all the other patterns. This is a unitary
and Q|c>=|u>. By (5), V*|u>=0. Therefore

    Phi(Q)|b>=0,    Phi(Q*Q)=I.

Since Phi(Q) is a contraction, I-Phi(Q*)Phi(Q) is a positive contraction.
It has eigenvalue one on |b>, proving (4) exactly.

The general identity behind the calculation is

    Phi(O*O)-Phi(O*)Phi(O) = V*O*(I-P)OV.                  (8)

It explains both positivity and the failure of multiplicativity. Local
compression alone does not remove I-P from this expression.

If tau is onto, (5) makes V unitary and its inverse is the quantization
of sigma on finite configurations. Conjugation is then multiplicative.
Applying Section 2 with the maps exchanged shows that the inverse
conjugation also preserves locality. This proves the remaining assertion
of part 3.

## 5. Why extending the diagonal to matrix units is the missing theorem

If Y is proper, compactness supplies a nonempty cylinder specified by a
pattern p on some finite F and disjoint from Y. Its characteristic
projection e_pp is one of the diagonal minimal projections in A_F.
Equation (7) sends e_pp to zero.

Suppose a unital *-homomorphism alpha extended (7). For the standard
matrix units e_ij of A_F, indexed by patterns i,j on F, we would have

    alpha(e_ii)=alpha(e_ip e_pp e_pi)=0

for every i. Summing over i gives alpha(I)=0, contrary to unitality.
Thus no such extension exists when tau is strict. When tau is onto,
the isomorphism Phi constructed above is such an extension. This proves
part 4 without appealing to an unproved classification result for
infinite operator algebras.

In particular, the always-available local completely positive map from
Section 2 is not the missing homomorphism. Saying that it is would
contradict the explicit local unitary in Section 4. Universal existence
of the homomorphism for injective equal-alphabet CA is equivalent to
the surjunctivity conclusion and remains an open Cairn prerequisite.

## 6. Nonlinear free-group example and exact replay

Let G=F(s,t), B={0,1}, and A={0,1}^2. On bits set

    tau(x)(g)=(x(gt), x(g) AND x(gs)),
    sigma(a,b)(g)=a(gt^{-1}).

Then sigma tau=id, with N={e,s,t}, M={e,t^{-1}}. This is a nonlinear
rectangular section, not a counterexample to the square-alphabet
conjecture. All-zero configurations give the reference backgrounds.

Let Q flip the first output bit at e. Flipping it changes the decoded
input only at t. Re-encoding preserves the second track exactly when
the input bits at ts and ts^{-1} are both zero. Thus, with X_t the
input-bit flip and P_{k,0} the diagonal zero-bit projection at k,

    Phi(Q)=X_t P_(ts,0) P_(ts^{-1},0),
    Phi(Q*Q)-Phi(Q*)Phi(Q)=I-P_(ts,0)P_(ts^{-1},0).          (9)

The group elements here are distinct. The projections commute with X_t,
so (9) is a nonzero orthogonal projection and has norm one. A flip of
the second output bit at e has compression zero on every basis input:
the unchanged first track already determines the entire input and the
second track becomes inconsistent with it.

The companion replay checks the split identity and these exact action
formulas on every bit assignment in the three-site window, with varied
outside contexts, using reduced words in the infinite free group. It
checks the predicted kernel and multiplicative defect; it does not
substitute finite-dimensional experiments for (2), (3), or (8).

## 7. Literature boundary

Arrighi and Nesme, [*Quantization of cellular automata*](https://arxiv.org/abs/0903.0258),
study quantization on finite configurations of Z^d and distinguish
isometries, unitaries, and quantum locality. Their Theorem 2.1 is stated
in that lattice setting. It is not an all-group surjunctivity theorem.
In its converse proof, nonreversibility supplies the absence of a local
inverse detector. A hypothetical injective strict group CA already has
such a detector by compactness; importing that step to an arbitrary
group would assume the disputed conclusion.

The compression, matrix-unit, and norm arguments here are elementary
operator theory. The precise ordered memory bound and sharp defect
calculations are recorded as derived results, with no claim of external
priority or Lean verification. The proposed algebraic shortcut has been
audited; its missing extension has not been constructed.
