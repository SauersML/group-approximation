# Samelson orders n·C(n−1,i−1) and independent commutator pairs

Date: 11 September 2026, from the `lix-sweep` lane. This is a complete
argument that has not been independently reviewed. It extends
[the nonabelian component-group proof](stw59-nonabelian-unitary-component-groups-2026-09-11.md)
(cited below as NCG), and the notation there is kept.

## 1. The general Samelson order

**Proposition A.** Let n>=2 and 1<=i<=n, and put j=n+1−i. Let a_i and a_j
be generators of π_{2i−1}U(n)≅Z and π_{2j−1}U(n)≅Z. Then the Samelson
product ⟨a_i,a_j⟩ in π_{2n}U(n)≅Z/n! has order exactly

    N(n,i) = n!/((i−1)!(j−1)!) = n·C(n−1,i−1).

The case i=1 is NCG Proposition 2. The value agrees with Bott's formula
⟨a_i,a_j⟩=(i−1)!(j−1)!·(generator) (Comment. Math. Helv. 34, 1960), but the
proof below does not use that formula.

**Proof.** Let x_{2i} and x_{2j} be the adjoint generators in π_*BU(n). As
in NCG §1 the question is when the map (x_{2i}, k·x_{2j}) on S^{2i}∨S^{2j}
extends over P=S^{2i}×S^{2j}. Both degrees are at most 2n, so these
classes are stable, and a rank-n bundle on S^{2p} with 2p<=2n is
determined by its K-class. Write a and b for the pulled-back integral
generators, so H^*(P)=Z{1,a,b,ab}. This covers the case i=j, where a and
b share a degree.

*Necessity.* On S^{2p}, c_p=(−1)^{p−1}(p−1)!·ch_p. So an extension E has
c(E)=1+A+B, with A=ε(i−1)!a and B=σk(j−1)!b; there is no ab term because
c_{n+1} vanishes in rank n. Since a²=b²=0, log c(E)=A+B−AB. In degree
2n+2 this gives (−1)^n·n!·ch_{n+1}(E)=−εσk(i−1)!(j−1)!·ab, so

    ch_{n+1}(E) = ±(k/N)·ab.

The suspension of P splits into three spheres, so ch is integral on
K^0(P), and hence N divides k.

*Sufficiency.* Let κ and κ' be the pulled-back Bott classes, with
ch=a and ch=b, and γ=κκ', with ch=ab and c(γ)=1+(−1)^n n!·ab. Then

    c(κ+Nκ'+sγ) = 1+(−1)^{i−1}(i−1)!a + N(−1)^{j−1}(j−1)!b
                  + (−1)^n·n!·(s−1)·ab,

because N(i−1)!(j−1)!=n! and i+j−2=n−1. Take s=1, which kills c_{n+1}.
As in NCG §1, a trivial line splits off in every rank >=n+2, and in rank
n+1 the only obstruction is the Euler class c_{n+1}=0. So the class is a
rank-n bundle, with restrictions ±x_{2i} and ±N·x_{2j}. Therefore
N·[x_{2i},x_{2j}]=0, and the order is exactly N. □

Examples: N(2,·)=2 and N(3,2)=6=3!, so the commutator coming from S³×S³
generates the whole group π_6U(3). Also N(5,3)=30 and N(4,2)=12.

## 2. Wedged odd-sphere arms

Fix a finite list (n_α,i_α), α=1..s, with n_α>=2 and 1<=i_α<=n_α, and
put j_α=n_α+1−i_α and N_α=N(n_α,i_α). Let R=max n_α and e_α=R−n_α, and set

    M_α = S^{2i_α−1} × S^{2j_α−1} × CP^{e_α},
    E_α = 1^{n_α} ⊕ L_α^{⊕e_α}.

Wedge the arms at based zero-cells to get X_0. Glue the bundles at the
wedge point by unitary identifications, exactly as in §3 of the
finite-abelian proof. Then set X=X_0×Y, E=pr^*E_0⊕H, r=R+m, and
G(E)=U(Γ(End E)).

**Theorem B.**

(a) There is an exact sequence 1 → ⊕_α Z/n_α! → π_0G(E) → K^1(X) → 1, whose
kernel is central. The coordinate α of the kernel is detected by
restriction to M_α×Y.

(b) Let u_α and v_α be a_{i_α}∘pr and a_{j_α}∘pr on arm α, direct sum
1_H, and the identity on every other arm. Their commutator has order N_α,
and it lies in coordinate α of the kernel. For α≠β, both u_α and v_α
commute pointwise with both u_β and v_β.

(c) Adding a tautological block by extension by the identity is injective
on π_0, an isomorphism on kernels, and pr^* on K^1.

**Proof.**

*(a)* Top cohomology H^{2r}(X;Z) ≅ ⊕_α H^{2r}(M_α×Y) ≅ Z^s through the arm
inclusions. The reduced cohomology of a wedge is the sum over the arms, and
Y has free cohomology in even degrees.

As in NCG Theorem 3(a), the gauge sequence gives
Z^s → π_0G(E) → K^1(X) → 0. The map on K^1 is onto because
π_0S(F)=0 in this dimension.

The Euler image is computed armwise. On each arm the pair restricts to the
NCG Theorem 3 pair over S^{2i−1}×S^{2j−1}×(CP^{e_α}×Y). There the collapse
to S^{2n_α} has degree one and the image is n_α!Z, by §3 below. This gives
the inclusion im ⊆ ⊕ n_α!Z.

For equality, take the attaining class q^*κ on M_α. It has virtual rank
zero. Collapse the other arms to the wedge point, pull the class back to
X_0×Y, and call the result β̂_α. It vanishes on every other arm, so
Λ(β̂_α) = (0,..,±n_α!,..,0). As in the finite-abelian proof §4, this
excludes hidden relations. Centrality is the argument of NCG 3(a), now
with s top-cell integers.

*(b)* Pointwise, the commutator on arm α is the NCG commutator map. It
factors through the collapse to ⟨a_{i_α},a_{j_α}⟩∘pr⊕1. Restricting to
M_α×Y maps the kernel onto its coordinate α, and by §3 below the class
there has order N_α. On every other arm the commutator is the identity.
Pointwise commutation across arms holds because distinct arms meet only
at the wedge point, where every generator is 1.

*(c)* A product zero count multiplies each coordinate by ±1, as in §5 of
the finite-abelian proof. The five-lemma argument of NCG 3(d) then applies
verbatim. □
