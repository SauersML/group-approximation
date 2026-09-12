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
