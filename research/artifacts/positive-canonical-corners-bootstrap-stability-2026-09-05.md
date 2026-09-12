# Positive canonical corners bootstrap to full flexible HS stability

Audited analytic implication, 2026-09-05. This replaces full spectral
coverage by a weaker sufficient condition: recovery of some positive
fraction of each canonical approximate sequence. The fraction need not
be uniform. The implication does not establish the recovery hypothesis.

## 1. Precise hypothesis and conclusion

Let G be a countable, finitely generated, ICC, residually finite Kazhdan
group, with finite symmetric generating set S. In particular G may be
SL_5(Z). Normalize matrix HS norms by the dimension of their domain.

A canonical asymptotic sequence consists of maps
U_j:G->U(d_j) with pointwise vanishing multiplicative defects and

    tr_(d_j)(U_j(g)) -> delta_(g,e).

Equivalently one may use generator tuples with the corresponding fixed
word conditions. Assume the following positive-corner property:

For every such sequence there exist an infinite subsequence, projections
P_j in M_(d_j), and unitary tuples V_(j,s) on P_j C^(d_j), such that,
on that subsequence, with r_j=rank P_j,

    liminf_j r_j/d_j > 0,
    max_s ||[P_j,U_j(s)]||_(2,d_j) -> 0,
    max_s ||V_(j,s)-P_j U_j(s) P_j||_(2,r_j) -> 0.       (PCB1)

Moreover the V_j admit flexible exact corrections: there are genuine
representations rho_j:G->U(D_j), D_j>=r_j, with

    (D_j-r_j)/r_j -> 0,
    max_s ||rho_j(s)-(V_(j,s) direct_sum I_(D_j-r_j))||_(2,D_j)
      -> 0.                                           (PCB2)

No positive constant in the first line of (PCB1) is required to work
for different sequences, or even for their different subsequences.
The property only promises some infinite subsequence. A zero-rank
projection is excluded by its positive lower density.

Then G is flexibly HS-stable for every asymptotic sequence, including
ones whose limiting characters are not canonical. This conclusion uses
ICC for the corner bootstrap and residual finiteness and property (T)
for the final existing ucp regularization argument.

## 2. Polar compression and canonical corners

Suppose P_j has rank fraction tending to p>0 and asymptotically commutes
with the generators of a canonical sequence. Compress each generator to
P_j C^(d_j), and extend its polar partial isometry to a unitary V_(j,s).
Choose inverse generators compatibly. If W:P_j C^(d_j)->C^(d_j) is
inclusion and the singular values of P_j U_j(s)P_j are lambda_i in [0,1],
then

    ||U_j(s)W-WV_(j,s)||_HS^2
      =2 sum_i(1-lambda_i)
      <=2 sum_i(1-lambda_i^2)
      =||[P_j,U_j(s)]||_HS^2.                          (PCB3)

The equality of the two off-diagonal HS masses follows from unitarity.
Thus the normalized intertwining error tends to zero after division by
sqrt(r_j), since r_j/d_j tends to p>0. Telescoping fixed words proves
that the compressed tuples are asymptotic representations.

They are also canonical. In a tracial matrix ultraproduct, the original
tuple gives a trace-preserving copy N of L(G): its group trace is
canonical, so the associated GNS von Neumann algebra is L(G). The class
P of the projections commutes with N. The trace-preserving conditional
expectation E_N satisfies

    E_N(P) in Z(N),
    E_N(P)=p I,                                       (PCB4)

because ICC makes N a factor. Consequently

    tau(P U(g))=p delta_(g,e).

Together with (PCB3), this gives canonical normalized traces on the
compressed corner. The conclusion holds in the ordinary sequential
sense: every free ultrafilter gives the same limit, and a bounded scalar
sequence with that property converges. The same argument applies to
I-P_j whenever its limiting rank fraction is positive.

An alternative unitary tuple satisfying the last line of (PCB1) has the
same asymptotic and canonical properties, by fixed-word telescoping.
No adjoint action of the approximate tuple is treated as genuine here.
The genuine group representation appears only after passage to the
ultraproduct; the conditional-expectation argument is qualitative.

## 3. Combining disjoint corrected corners

Two orthogonal, asymptotically reducing corners of positive limiting
rank, each satisfying (PCB1)--(PCB2), can be combined into one such
corner. Use their direct-sum unitary tuples and direct-sum exact
corrections. Approximate reduction makes the off-diagonal blocks tend
to zero in the ambient normalized HS norm. Restriction to any positive
limiting rank rescales that norm by a bounded factor. Thus the combined
tuple is close to the compression onto the sum of the projections.

The sum of their padding dimensions is o(d_j), and the direct-sum
correction error also tends to zero. Indeed squared HS errors add on
orthogonal blocks; dividing by total dimension weights them by their
rank fractions. The same statements hold for any fixed finite number
of corners.

If a correctable corner has rank fraction tending to one, add the
trivial representation on its original orthogonal complement. The
polar block decomposition differs from the original tuple by o(1),
and replacing the complementary unitary block by identity costs at most

    2 sqrt((d_j-r_j)/d_j) -> 0.

The total dimension is d_j+o(d_j). This is a full flexible correction.

## 4. The uniform-fraction finite iteration

If (PCB1) holds with one constant c>0 for every input sequence, an
elementary finite iteration suffices. After a subsequence makes the
rank fractions converge, apply the property to the complementary
canonical sequence from Section 2. Continue on positive-density
remainders. After n steps their remaining fraction is at most
(1-c)^n. Every fixed number of steps introduces only o(1) error and
o(d_j) padding. Replacing that last block by the trivial representation
costs at most 2(1-c)^(n/2) in the limit.

Given a fixed positive tolerance, choose n first and then pass far
enough along the resulting subsequence. This contradicts any sequence
uniformly separated from flexible exact corrections. It is unnecessary
to assume a uniform error modulus or carry out infinitely many
corrections at a fixed matrix size.

## 5. A nonuniform positive fraction also suffices

Suppose, for contradiction, that canonical flexible stability fails.
There is a canonical sequence and eta>0 such that no member admits an
exact correction with both relative padding and generator error less
than eta. Passing to a subsequence preserves this property.

Call p in [0,1] recoverable if, along some infinite subsequence of this
bad sequence, there are asymptotically reducing and flexibly correctable
corners whose rank fractions converge to p. Include p=0 by convention.
Let a be the supremum of the recoverable numbers.

If a>0, this supremum is attained along a subsequence. To see this, choose
recoverable p_n tending to a. From the corresponding nth sequence
choose one index larger than all previously chosen indices, with rank
fraction within 1/n of p_n and with commutator, compression, correction,
and relative padding errors all below 1/n. This diagonal sequence
witnesses recoverability of a. There is no requirement that the
subsequences witnessing the different p_n be nested.

If a=1, Section 3 gives a full correction on this subsequence,
contradicting its defining eta separation. If a<1, take its complementary
corner. Its limiting fraction is 1-a>0, and Section 2 shows that its
polar compressed tuple is canonical. Apply (PCB1)--(PCB2) to this
sequence. Along a further subsequence it supplies a correctable corner
of relative fraction at least some c'>0. Refine once more so that this
relative rank fraction converges to a number c''>=c'>0.

View this new projection inside the original complementary subspace.
It asymptotically commutes with the original tuple: the old projection
was approximately reducing, its compressed tuple differs by o(1) from
the chosen unitary compression, and the new projection approximately
commutes with that tuple. The new corner's unitary compression and
correction are likewise valid in the original space, because its rank
has positive limiting ambient density.

Section 3 therefore combines the old and new corners into a recoverable
corner with limiting fraction

    a+(1-a)c'' > a,

contradicting the definition of a. The case a=0 is covered by applying
the hypothesis to the entire original space and omitting the empty
old block. This proves canonical flexible stability under the stated
nonuniform, subsequence-only positive-corner hypothesis.

The contradiction argument is what upgrades a subsequence conclusion
to correction of every canonical sequence: any failure of convergence
to exact corrections would have supplied an eta-separated bad
subsequence of the kind just ruled out.

## 6. From canonical sequences to arbitrary sequences

Use the existing Cairn result
`residual-finite-regularization-removes-the-weak-ucp-quantifier` and its
`maximally-entangled-ucp-untensoring-proof`. The key formulas are recalled
here to make the dimensional normalization explicit.

Residual finiteness supplies exact representations
sigma_j:G->U(e_j) with canonical limiting characters. For any
asymptotic sequence A_j:G->U(d_j), the tensor sequence

    A_j(g) tensor sigma_j(g)

is canonical. Its flexible exact corrections, proved above, compress
to ucp maps Psi_j:C*(G)->M_(d_j e_j) close to this tensor tuple.
Compression loses at most the factor sqrt(D_j/(d_j e_j))=1+o(1),
because flexible padding is o(d_j e_j).

Let Omega_j=e_j^(-1/2) sum_l e_l tensor conjugate(e_l). Tensor a
Stinespring representation of Psi_j with conjugate(sigma_j), then
compress along xi -> xi tensor Omega_j. This defines a ucp map
Theta_j:C*(G)->M_(d_j), satisfying on each g

    Theta_j(u_g)-A_j(g)
      =(id tensor tr_(e_j))
        ((Psi_j(u_g)-A_j(g) tensor sigma_j(g))
          (I tensor sigma_j(g)^*)).

Normalized partial trace is an L2 contraction, so

    ||Theta_j(u_g)-A_j(g)||_(2,d_j)
      <=||Psi_j(u_g)-A_j(g) tensor sigma_j(g)||_(2,d_j e_j).

There is no factor involving e_j. These are full-group-algebra ucp
maps. The established Kazhdan Stinespring-corner argument turns their
vanishing generator errors into full flexible exact corrections of A_j.

Thus a proof of (PCB1)--(PCB2) for every canonical sequence would prove
full flexible HS stability of SL_5(Z). The spectral second-moment
construction is one proposed way of producing these positive corners;
the present argument proves the bootstrap once the positive-corner
data are available, and does not assume those data follow from QRC.
