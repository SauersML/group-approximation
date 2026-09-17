---
rg: 2
id: symbol-blind-automata-reduce-to-defect-counting-proof
kind: route
title: Selector normal form, partition criterion, window-faithful colourings and falling-factorial independence
target: symbol-blind-automata-reduce-to-defect-counting
requires:
  - bijective-ca-preserve-uniform-bernoulli-measure
---

Throughout, G acts on configurations by (hx)(g) = x(h^{-1}g). Automata commute
with this action. Set partitions of G carry the induced action hP = {hC}.
For a partition P and g in G, pi_g P is the partition of M with m ~ m' iff gm
and gm' lie in one class. The same notation pi_g x for a configuration uses
ker x.

## 1. Normal form

Let f:[q]^M -> [q] be the local rule, so f(s o a) = s(f(a)) for every
permutation s of [q].

Suppose f(a) is not among the values a(m). The values of a use at most |M|
symbols. Since q >= |M|+2, at least two symbols are unused, f(a) and some c.
The transposition s = (f(a) c) fixes a, so

    f(a) = f(s o a) = s(f(a)) = c,

a contradiction. Hence f(a) = a(m) for some m, so f selects a class of the
partition ker a of M.

If a and a' have the same partition, then a' = s o a for some permutation s
(extend the bijection between their value sets). So f(a') = s(f(a)) selects
the same class. Thus the selected class depends only on the partition. Let
sigma(partition) be any element of it; the formula in the claim follows. The
formula makes sense for every q and defines tau_q for all q simultaneously.

Now let s0 = sigma(discrete) and rho(y)(g) = y(g s0^{-1}). Right
multiplication commutes with the left action, so rho is a bijective automaton.
The composite rho o tau_q is again a selector:

    (rho o tau)(x)(g) = x(g s0^{-1} sigma(pi_{g s0^{-1}} x)).

As a function of the window s0^{-1}M at g, this sends the discrete partition
to e. Injectivity, surjectivity and measure preservation are unchanged by
rho. From now on assume sigma(discrete) = e (with memory replaced by
s0^{-1}M, which contains e and has size |M|).

## 2. Partition criterion

For x in [q]^G, psi_x = psi_{ker x} and tau(x) = x o psi_x. So

    ker tau(x) = {(g,h) : x(psi g) = x(psi h)} = psi^* ker x = T(ker x).

Fix P in Part_{<=q}(G) and let X_P be the configurations with kernel P. Then
tau(X_P) lies in X_{T(P)}, and on X_P the map is c -> c o psibar. Here c is an
injective colouring of classes(P) and psibar: classes(T P) -> classes(P) is
induced by psi_P. psibar is well defined and injective by the definition of
T(P).

Let m be the number of classes of P missed by psibar. An image c o psibar
fixes c on the k(P)-m hit classes. The number of injective extensions to the
missed classes is (q-k(P)+m)_m, so the map on X_P is injective iff m = 0, or
m = 1 and k(P) = q. In both injective cases |X_P| = |X_{T P}|, so the map is
a bijection onto X_{T P}. The sets X_P partition [q]^G.

- tau_q is injective iff T is injective on Part_{<=q}(G) and every psibar_P
  is onto, except possibly when k(P) = q and exactly one class is missed.
  (If T(P) = T(P') with P != P' and both restricted maps injective, the two
  images equal X_{T P}, which is nonempty.) The exceptional case never arises
  below, because every later argument leaves a spare symbol.
- Surjectivity. tau_q is onto iff every X_Q, Q in Part_{<=q}, meets the
  image. For Q = T(P), every injective colouring d of classes(Q) extends: set
  c = d o psibar^{-1} on the hit classes, and colour the k(P)-k(Q) <= q-k(Q)
  remaining classes with distinct unused colours. So X_Q lies in the image
  iff Q is in T(Part_{<=q}).

Downward transfer. [q']^G ⊂ [q]^G for q' <= q, and tau_{q'} is the
restriction, so injectivity descends. Bijectivity descends except through the
exceptional case. By section 4 it holds at every q once it holds at infinitely
many q.

## 3. Sparse-defect transfer

Assume sigma(discrete) = e and tau_q is injective for every q. For P in FD(G),
let supp P be the union of its non-singleton classes and N(P) = (supp P)M^{-1}.
If g is not in N(P), the window gM meets supp P nowhere. So pi_g P is discrete
and psi_P(g) = g. Equivariance: pi_{hg}(hP) = pi_g P, hence psi_{hP}(hg) =
h psi_P(g) and T(hP) = hT(P).

**Window-faithful colourings.** Let P be in FD(G) and D a finite set with
supp P ⊂ D. Colour the classes of P meeting D injectively from a palette A1
with |A1| = #classes meeting D.

Let Gamma be the graph on G \ D with u ~ v iff u != v and v ∈ uM^{-1}M. Its
degree is at most |M^{-1}M|-1. Every finite subgraph is greedily
|M^{-1}M|-colourable, so Gamma is |M^{-1}M|-colourable (compactness); use a
palette A2 disjoint from A1.

The resulting x satisfies pi_g x = pi_g P for every g. Take distinct u, v in
gM. If both are in D, colours agree iff the classes agree. If exactly one is
in D, the palettes differ and the other point is a singleton class. If
neither is in D, they are adjacent in Gamma. Moreover ker(x|_D) = P|_D, and
psi_x = psi_P, so tau(x) = x o psi_P.

**psibar_P is onto.** Suppose psi_P misses a class C of P. C cannot be {u}
with u outside N(P), since psi_P(u) = u. Let D = supp P ∪ N(P) ∪ C and build
x as above. Let q = |A1|+|A2|+1, with spare symbol c*.

Let x' recolour C by c*. Then x' is still window-faithful to P, so
psi_{x'} = psi_P. Since psi_P(G) misses C,

    tau(x') = x' o psi_P = x o psi_P = tau(x),

while x' != x. This contradicts injectivity of tau_q.

**Defect is preserved and T(FD) ⊂ FD.** Let B = supp P ∪ N(P) ∪ N(P)M, a
finite set.

- psi_P maps N(P) into N(P)M and is the identity elsewhere. So psi_P(B) ⊂ B,
  psi_P^{-1}(B) = B, and psi_P is the identity off B.
- The classes of T(P) contained in B are psi_P^{-1}(C) for the classes C ⊂ B.
  All other classes of T(P) are singletons {u} with u outside B.
- psibar is bijective, so the numbers of classes of P|_B and T(P)|_B agree.
  Hence defect(T P) = |B| - #classes = defect(P), and supp T(P) ⊂ B.

**T is injective on FD.** Let P != P' in FD with T(P) = T(P') = Q. Define

    beta = psibar_P o psibar_{P'}^{-1}: classes(P') -> classes(P),

a bijection. Let N = supp P ∪ supp P' ∪ N(P) ∪ N(P') and D = N ∪ NM.

For u outside D:

- u is a singleton in both P and P';
- psi_P(u) = psi_{P'}(u) = u;
- no g != u has psi_{P'}(g) = u, since that needs g ∈ N(P') and u ∈ gM ⊂ D.

So {u} is a class of Q, and beta({u}) = {u}. Since beta is a bijection that
fixes these singletons, it maps the P'-classes meeting D onto the P-classes
meeting D.

Build x for P with this D. Define x'(u) = x(beta(class of u in P')), the
A1-colour of that class, for u in D, and x'(u) = x(u) off D. The colouring of
the P'-classes meeting D is injective (beta is injective) and lies in A1. Off
D, x' is the same proper A2-colouring. So x' is window-faithful to P' and
psi_{x'} = psi_{P'}.

For any g, let K be the Q-class of g. By definition beta sends the P'-class of
psi_{P'}(g) to the P-class of psi_P(g). Both colours are the colour of that
class (including singletons off D), so tau(x')(g) = x(psi_P(g)) = tau(x)(g).

Finally x' != x: otherwise ker x'|_D = ker x|_D, i.e. P'|_D = P|_D. Both
supports lie in D, which forces P = P'.

**Pairs.** A defect-1 partition is one pair {a,b}. Call it visible if b ∈
aM^{-1}M. An invisible pair has only discrete windows, so psi = id and
T(P) = P.

Let P be visible. T(P) has defect 1, so it is a pair. If T(P) were an
invisible pair p, then T(p) = p = T(P) with P != p, contradicting injectivity.
So T maps visible pairs into visible pairs.

Visible pairs form finitely many G-orbits (represented by {e,s},
s ∈ M^{-1}M \ {e}). An injective equivariant map sends orbits injectively to
orbits, and on each orbit Gp -> G T(p) it is onto, because it is equivariant.
With finitely many orbits the orbit map is a bijection. Hence T is bijective
on defect-1 partitions; call the induced pair bijection phi.

## 4. Polynomial rigidity

**Locality.** For g, h in F, g ~_{T P} h iff psi_P(g) ~_P psi_P(h). Here
psi_P(g) depends on P|_{gM}, and both points lie in FM = E. So T(P)|_F depends
only on P|_E, which defines t_E: Part(E) -> Part(F). For the identity
selector, t_E(P) = P|_F.

**Preimage count.** Fix y in [q]^F with kernel pi and k classes. A
configuration x on E with kernel P_E satisfies tau(x)|_F = y iff
t_E(P_E) = pi and x on the classes hit by psi(F) equals the colours y assigns
through the bijection classes(pi) -> hit classes. The hit map is injective by
the definition of t_E.

The remaining k(P_E)-k classes take distinct colours outside y's k colours.
Grouping by the defect j = |E| - k(P_E),

    #{x ∈ [q]^E : tau(x)|_F = y} = sum_j N_j^T(F,pi) (q-k)_{|E|-j-k}.

tau_q preserves the uniform measure mu_q iff every cylinder satisfies
mu_q(tau^{-1}[y]) = q^{-|F|}. That is, the count equals q^{|E|-|F|}, which is
the same formula evaluated for the identity selector.

The falling factorials (q-k)_n, n >= 0, are monic of distinct degrees, hence
linearly independent. Both sides are polynomials in q.

- (a) => (c): agreement at infinitely many q is agreement as polynomials, so
  N_j^T = N_j^{id} for every j.
- (c) => (b): immediate.
- (b) => (a): trivial.

**Bijectivity.** Suppose tau_q is bijective for every q (or infinitely many
q). By bijective-ca-preserve-uniform-bernoulli-measure it preserves mu_q, so
(a) and hence (c) hold.

Conversely, suppose tau_q is injective for all q and (c) holds. Then (b)
holds, so tau_q([q]^G) is a compact set of mu_q-measure 1. It is therefore
closed with full measure and contains the support of mu_q, which is
everything. So tau_q is surjective, hence bijective, for every q.

The same argument shows: bijectivity at infinitely many q gives (c), hence
surjectivity at every q; injectivity at every q descends from the larger
alphabets.

## 5. Orders 0 and 1

Assume tau_q is injective for every q and sigma(discrete) = e. If a
partition P of E has defect j, its extension Q = T(P) has defect j, so
Q|_F has defect <= j. Hence N_j(F,pi) = 0 for j < defect(pi), for T and for
id alike.

**j = 0.** The only defect-0 partition is the discrete one, and T(discrete) =
discrete. So N_0^T(F,pi) = [pi discrete] = N_0^{id}(F,pi).

**j = 1.** The defect-1 partitions of E are the pairs p ⊂ E. By section 3,
T(P_p) = P_{phi(p)}, and P_{phi(p)}|_F is either discrete or the pair
phi(p) ⊂ F.

- pi = a pair {u,v} ⊂ F: then N_1^T(F,pi) = [phi^{-1}{u,v} ⊂ E]. If
  p = phi^{-1}{u,v} were not inside E, then P_p|_E would be discrete. By
  locality T(P_p)|_F = T(discrete)|_F would be discrete, not pi. Hence
  N_1^T = 1 = N_1^{id}.
- pi discrete: N_1^T = C(|E|,2) - C(|F|,2) = N_1^{id}.
- Every other pi: 0 in both.

## What is not proved

Orders j >= 2 (symbol-blind-defect-counting-identities). The natural inputs
are:

- surjectivity of T on each FD sector of defect >= 2; only injectivity,
  defect conservation and the pair case are proved;
- a boundary cancellation in the regularized count N_j^T - N_j^{id} =
  #{P ∈ FD_j(W) : T(P)|_F = pi} - #{P ∈ FD_j(W) : P|_F = pi}.

The regularized count is independent of the finite set W ⊇ E once the lower
orders agree, because the number of defect-j extensions of a partition of E
into W depends only on |W|, |E| and its defect.

Upward transfer of injectivity from one q >= |M|+2 to all q is also not
proved. The obstacle is recolouring with a bounded palette.
