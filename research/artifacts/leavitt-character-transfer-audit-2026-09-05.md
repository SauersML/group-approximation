# Character transfer to the elementary Leavitt group: exact scope

Analytic audit, 2026-09-05. No computation. This audit does not prove
nonhyperlinearity of an elementary Leavitt group.

## 1. The valid terminal implication

Let G be countable. Suppose every normalized positive-definite class
function on G has the form

    chi = a * 1 + (1-a) * delta_e,  0 <= a <= 1.                 (CT1)

If G admits any non-Connes-embeddable tracial representation, then G is
nonhyperlinear. Indeed, if its canonical trace delta_e were embeddable,
every trace in (CT1) would be embeddable. To see this directly, combine
matrix microstates for delta_e with scalar identity blocks, choosing block
proportions converging to a and 1-a. Thus (CT1) and an actual bad trace on
G would close the endpoint.

More generally, it suffices that every extremal character other than the
regular character is embeddable. Embeddable traces form a weak-star closed
convex set: finite direct sums prove convexity, and diagonal selection of
finite moment microstates proves closedness. Choquet decomposition then
gives the same conclusion.

Neither statement constructs a bad trace on G from a bad trace on an
unrelated algebra. In particular, a quotient of C*(G) with a bad trace
supplies a bad character, but constructing that quotient with its trace
is a substantive additional input.

## 2. What is actually known for the Leavitt candidate

For R=L_2(F_2), the current Cairn claim
`degree-zero-leavitt-core-characters-are-dirac-haar-mixtures` establishes
(CT1) for K=EL_n(R_0), n>=3. Here R_0 is the degree-zero matrix tower.
Consequently every character of EL_n(R) restricts to such a mixture on K.
It does not establish (CT1) on EL_n(R).

The current `monomial-root-elements-are-conjugate-in-the-leavitt-group`
extends the single constant a to monomial root elements, but is stated
for EL_12(R)=GL_12(R). It neither classifies arbitrary group words nor
asserts this rank-specific equality for EL_3 or EL_5. In particular,
mixed-degree coefficients and products of root elements remain outside
the resulting character classification.

The relevant primary sources do not fill that gap:

* [Lavi--Levit](https://arxiv.org/abs/2007.15547) assumes a commutative
  Noetherian coefficient ring and a stable-range bound. The Leavitt ring
  is outside that hypothesis. Moreover, induction from finite-dimensional
  representations of subgroups is not a claim that every ambient factor
  representation is finite-dimensional.
* [Peterson--Thom](https://arxiv.org/abs/1303.4007) treats infinite fields
  and localizations of orders in number fields, not this coefficient ring.
* [Dudko--Medynets](https://arxiv.org/abs/1212.1230), Corollary 3.6(2),
  gives (CT1) for Thompson V. Containing V does not transfer its character
  classification to an arbitrary overgroup.
* [Dogon--Vigdorovich](https://arxiv.org/html/2506.20843v2), Section 6,
  characterizes hyperfinite HS stability using von Neumann amenable
  characters. This is not a classification of all embeddable characters.
  A nonamenable group can have an embeddable, nonhyperfinite regular factor.

The existing `steinberg-hyperfinite-hs-stable-proof` makes precisely this
last distinction: property (T) and the absence of nontrivial finite-
dimensional representations restrict amenable characters of St_5(R).
They do not exclude its canonical character from being embeddable.

## 3. Tracial extension fails already inside EL_3

Let R be any nonzero unital F_p-algebra and n>=3. Inside EL_n(R), set

    a=x_12(1), b=x_13(1), H=<a,b> ~= (F_p)^2.

These commute and are independent, as is visible in their two matrix
entries. Put zeta=exp(2*pi*i/p) and define the one-dimensional character

    psi(a^u b^v)=zeta^v.

Let w=x_23(1)x_32(-1)x_23(1). Its 2,3 block is
[[0,1],[-1,0]], and direct multiplication gives

    w a w^{-1}=b^{-1}.

An ambient character extending psi would therefore satisfy
1=psi(a)=psi(b^{-1})=zeta^{-1}, a contradiction. This works for p=2
as well, where the right side is -1.

Thus the inclusion C*(H) -> C*(EL_n(R)) does not admit extension of every
tracial state, even though ordinary state extension is available. This is
an exact obstruction for EL_3 and EL_5 themselves and uses no full-rank
Leavitt conjugacy theorem. It refutes automatic tracial extension, not the
possibility of a specially compatible bad trace.

## 4. A rigid core with regular restriction does not detect bad traces

Let K=EL_3((L_2(F_2))_0), the same countable locally finite core. Let
(M,tau) be any separable nonembeddable tracial von Neumann algebra and
choose countably many unitaries u_j generating it. The homomorphism from
the countable free group F_infty sending its generators to u_j defines a
nonembeddable character psi. Put

    G=K x F_infty,
    chi(k,g)=delta_e(k) psi(g).                              (CT2)

This is a character, realized on L(K) tensor M. Its GNS algebra contains
the trace-preserving copy 1 tensor M, so chi is not embeddable. Yet G is
hyperlinear: every finite set in K belongs to a finite subgroup, every
finite word set in F_infty is separated by a finite quotient, and tensor
products of their regular matrices give canonical microstates for G.
Both the canonical character of G and the bad character (CT2) restrict
to exactly delta_e on K.

Therefore even the complete classification of all characters on this
particular rigid core, together with a canonical restriction to it, cannot
turn a bad ambient trace into a bad canonical trace. Here K is normal but
does not normally generate G; this countermodel makes no claim against a
future theorem using the extra simplicity or normal-generation structure
of the full Leavitt group.

An arbitrary nonembeddable action is still further removed: its crossed-
product trace restricts to the canonical trace on the acting group, but a
nonembeddable crossed product need not have a nonembeddable group subalgebra.
For example, a trivial action on M produces M tensor L(G); its badness can
come entirely from M even when G is finite.

## 5. Remaining concrete obligation

A character route can close by proving a full-group statement such as
(CT1) and constructing a compatible nonembeddable character of that same
group. Current core rigidity, monomial conjugacy, absence of finite-
dimensional representations, and hyperfinite stability provide neither
the full classification nor the trace construction. Sections 3 and 4
show why dropping either obligation is invalid.
