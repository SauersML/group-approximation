# The nilpotency class of a block component group is at most the excess plus two

Date: 12 September 2026, lane `ex-unitary-class-three`. This is a complete
argument that has not been independently reviewed. It generalizes Proposition D of
`stw59-samelson-orders-and-wedged-arms-2026-09-11.md` (class at most two
when dim X <= 2·rank), and it complements the class-three construction in
`class-three-spin-bordism-trapping-2026-09-12.md`.

## Statement

Let X be a connected finite CW complex of dimension d, E -> X a Hermitian
bundle of rank r, and G(E) = U(Gamma(End E)). Write
Pi(E) = G(E)/G_0(E) = pi_0 G(E), and put e = d − 2r (the *excess*).

**Theorem.** If e >= 0, then Pi(E) is nilpotent of class at most e + 2. If
e < 0, then Pi(E) ≅ K^1(X) is abelian.

**Corollary 1.** Suppose A is a unital inductive limit, with injective
connecting maps, of finite direct sums of such blocks. Suppose every block
at every stage has excess at most e. Then U(A)/U_0(A) is nilpotent of class
at most e + 2. Every unital AH algebra of this kind has a *locally
nilpotent* unitary component group.

**Corollary 2.** C(T^2 x S^3, M_2) has component group of class exactly
three: here d = 5 and r = 2, so e = 1, and `u2-triple-samelson-class-three-stage`
gives the lower bound.

**Corollary 3.** Consider a simple AH limit whose component group has
gamma_c != 1, and suppose it is presented as in Corollary 1. Then its
blocks have excess at least c − 2 cofinally. The Toms trapping tower of
`simple-ah-algebra-with-class-three-component-group` has excess
5 + 4r_i − 2(r_i + 2) = 2r_i + 1, which is unbounded.

## Proof

**Step 0: stable range.** Suppose Y is a finite CW complex, F -> Y has rank
s, and dim Y < 2s. Then the stabilization Pi(F) -> Pi(F (+) 1) is an
isomorphism. The fibration G(F) -> G(F (+) 1) -> S(F (+) 1) has as base the
space of unit sections, with fibre S^{2s+1}. Since
dim Y <= 2s − 1 < 2s + 1 − 1, obstruction theory gives
pi_0 S(F (+) 1) = pi_1 S(F (+) 1) = 0: the coefficients pi_k(S^{2s+1}) and
pi_{k+1}(S^{2s+1}) vanish for k <= dim Y. Iterating, and using
K_1(Gamma(End F)) ≅ K^1(Y) (Morita equivalence and stabilization), gives
Pi(F) ≅ K^1(Y). This is the Stiefel stable-range lemma used by the
peer proof `equal-dimension-class-two-proof`.

**Step 1: the skeletal filtration.** For k >= 1 let F_k be the kernel of
restriction Pi(E) -> Pi(E|_{X^{(k−1)}}), with X^{(0)} a point set. Each F_k is
a normal subgroup. F_1 = Pi(E), because U(n) is connected, and
F_{d+1} = 1. By the homotopy extension property for sections of fibre
bundles over CW pairs, every class in F_k has a representative identically
1 on X^{(k−1)}.

**Step 2: the filtration is central.** We claim [Pi(E), F_k] ⊆ F_{k+1}.

Let g be in G(E), and let n in F_k be identically 1 on X^{(k−1)}. Over each
closed k-cell the pulled-back bundle is trivial, and n is a map
(D^k, ∂D^k) -> (U(r), 1). A radial deformation rel X^{(k−1)} makes n
identically 1 outside a small closed ball B_e in the interior of each k-cell.
It is a homotopy of sections over X^{(k)}, and it changes [g, n]|_{X^{(k)}}
only by a homotopy.

Now [g, n] ≡ 1 wherever n ≡ 1, and on B_e it depends only on g|_{B_e}. The
ball is contractible, so g|_{B_e} is homotopic to the constant c_e = g(center).
Along this homotopy n ≡ 1 near ∂B_e, so the commutator stays 1 there. Finally,
U(r) is connected, so a path c_t from 1 to c_e deforms
[c_e, n] = c_e n c_e* n* rel ∂B_e to n n* = 1. Hence [g, n]|_{X^{(k)}} is
homotopic to 1, that is [g, n] in F_{k+1}. The subgroup F_{k+1} is normal,
so the whole commutator subgroup lies in it.

**Step 3: commutators lie deep.** The map kappa: Pi(E) -> K^1(X) is a
homomorphism to an abelian group, so gamma_2 ⊆ N := ker kappa. If n is in N,
then its image in K^1(X^{(2r−1)}) is zero by naturality. By Step 0 with
Y = X^{(2r−1)}, s = r and dim Y < 2r, the element n is trivial in
Pi(E|_{X^{(2r−1)}}). So N ⊆ F_{2r}.

**Step 4: count.** By Steps 2 and 3, induction gives
gamma_c ⊆ F_{2r+c−2} for c >= 2. Since F_{d+1} = 1, gamma_c = 1 once
2r + c − 2 >= d + 1, that is c >= e + 3. So the class is at most e + 2.

If e < 0, Step 0 with Y = X gives Pi(E) ≅ K^1(X). □

**Corollary 1.** Finite products keep the bound. The component group of the
limit is the direct limit of the stage groups. Surjectivity comes from
polar approximation, and injectivity modulo U_0 from finite-stage path
detection (Toms arXiv:2609.09535v1 Lemma 7.1). A direct limit of groups of
class <= e + 2 has class <= e + 2, since gamma_c commutes with direct
limits. With no excess bound, each stage group is still nilpotent, of class
at most max(1, d − 2r + 2). Every finitely generated subgroup of the limit
lies in the image of one stage, so the limit is locally nilpotent. □

## Remarks

- The bound uses only one input about unitaries: stabilization is an
  isomorphism below twice the rank. Everything else is Whitehead-type
  skeletal filtration.
- *Class exactly three in a simple algebra* is open. The trapping tower has
  unbounded excess. The excess-one CP towers would give class at most three
  by the Theorem, but persistence of eta squared there is open
  (`eta-squared-survives-twisted-excess-tower`).
- *Nilpotency of the trapping limit* is open. Its stage groups have classes
  bounded only by 2r_i + 3.
