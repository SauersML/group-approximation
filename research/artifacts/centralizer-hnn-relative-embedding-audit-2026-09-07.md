# Centralizer HNN hyperlinearity is exactly relative embeddability

Date: 2026-09-07. This proves a criterion for the existing candidate groups;
it does not establish a nonhyperlinear group. The proof uses the valid
commuting-square lemma in the primary source, independently of the issue
with its printed plain-double argument identified below.

## The equivalence

For countable groups C <= A put B=L(C), M=L(A), and

    H = A *_C (C x Z),
    Dplus = (A x Z) *_C A.

The following are equivalent:

1. H is hyperlinear.
2. B <= M is relatively embeddable over the scalar algebra C (RE/C).
3. Dplus is hyperlinear.
4. B <= M is RE/N1 for some Connes-embeddable finite von Neumann algebra N1.

Here the scalar algebra C in RE/C means the complex numbers, whereas the
group C is the associated subgroup. No amenability, factor, finite-index,
or relative-Haar assumption on the group inclusion is required.

The implications 2 => 3 and 3 => 2 are the enlarged-amalgam case of
[Gao, with appendix by Marius Junge and David Gao,
arXiv:2012.07940v3](https://arxiv.org/html/2012.07940v3#S7), Theorem 7.1,
with scalar coefficient N1. The implication 3 => 1 also follows from
Britton normal form: embed A in the second vertex and take the stable
letter from the Z factor of the first vertex. Below is a direct proof of
1 => 2, which is the previously missing implication in Cairn.

## The centralizer conditional expectation

In P=L(H), let t be the stable letter and u=lambda(t). The homomorphism
H -> Z taking t to 1 and A to 0 shows that u is Haar. Also u commutes
with B. Let Q={u}' intersect P, with its trace-preserving expectation E_Q.
We claim

    E_Q(x)=E_B(x)                  for every x in M.       (HRE1)

For c in C this holds because u commutes with lambda(c). If a in A-C,
the elements t^j a t^(-j), j in Z, are pairwise distinct. Otherwise, for
some nonzero k one would have t^k a t^(-k)=a; the resulting word is
Britton-reduced and nontrivial. Consequently the corresponding group
unitaries are orthonormal in L2(P), and

    ||(1/n) sum_(j=0)^(n-1) u^j lambda(a) u^(-j)||_2^2
        = 1/n.                                           (HRE2)

The Hilbert-space mean ergodic theorem identifies the L2 limit of these
averages with E_Q(lambda(a)), so it is zero. Linearity and L2 density of
the group algebra in M prove (HRE1). In particular B is contained in Q
and the square with corners B,M,Q,P is a commuting square.

If H is hyperlinear, P embeds trace preservingly in R^omega. Apply
Gao's Lemma 7.2 with N=B, M=M, Mhat=P, scalar N1, and this actual central
Haar unitary u. Every hypothesis has just been verified, so B <= M is
RE/C. The reverse implication 2 => 1 can equally be obtained from the
existing star-amalgam and amenable-shift construction.

Finally, 2 => 4 follows by choosing N1 to be the scalars. For 4 => 1,
Gao's Theorem 1.1 embeds the countable star amalgam of copies of M over B
into an ultrapower of R tensor N1. This target is Connes embeddable when
N1 is. The kernel of H -> Z is precisely that star amalgam at the group
level; hyperlinearity passes to its semidirect extension by Z using the
explicit finite-interval construction in
`relatively-embeddable-pair-hnn-hyperlinear-proof`. This proves all four
equivalences. In fact RE/C tensors to RE/N1 for every finite N1; a CE
coefficient is needed only for the converse back to matrix embeddability.

## The printed plain-double proof has a different issue

The same primary source, Theorem 7.1, additionally states a plain-double
converse assuming a unitary v in M with E_B(v^k)=0 for all nonzero k.
On printed page 35, its proof chooses v from the first copy of M and
displays a square whose bottom arrow is

    B -> {v}' intersect (M *_B M).                        (HRE3)

This arrow requires v to commute with B. Vanishing B-expectations of its
powers do not imply that requirement. The calculation on that page proves
vanishing expectation for the other copy's M minus B, but does not prove
that the expectation fixes B. Both clauses are necessary for the square.

For the arithmetic choice in Cairn this is an explicit failure. Let

    C=SL_3(Z), A=SL_3(Z[1/p]),
    h=diag(p,1,p^(-1)), c=I+E_12.

Then h^k is outside C for k != 0, but

    h c h^(-1)=I+p E_12 != c.                            (HRE4)

Thus lambda(h) does not commute with L(C), in the first vertex or in the
double (whose vertex inclusion is injective). The printed square is not
available for this v. This identifies a gap in that argument and in a
source-only replay of it. It is not a counterexample to the theorem's
statement. A different proof may establish the group specialization.

The HNN argument above has no such defect: its stable letter centralizes
B by the defining relations. The enlarged-amalgam proof in Theorem 7.1
also uses a genuinely central tensor-factor Haar unitary. Neither needs
the questionable plain-double square.

## Consequences for the research target

Nonhyperlinearity of H and failure of RE/C are the same assertion for
each fixed pair. The previous description of the latter as a strictly
weaker goal was incorrect. These equivalent formulations still require a
proof that the chosen inclusion is not relatively embeddable. This audit
supplies the equivalence and corrects its scope, not that missing proof.

Verification: the printed Theorem 7.1, Lemma 7.2, and final commuting-square
diagram were checked in the version-3 PDF, including page 35. The proof
above was independently checked by two agents. It is a mathematical
proof recorded in Cairn, not a Lean kernel certification.
