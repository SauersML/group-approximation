---
rg: 2
id: symbol-blind-automata-on-pointed-memory-are-permutive-proof
kind: route
title: A minimal unhit singleton forces selection of the identity, a joined pair forces the join map to be a permutation, and solving in reverse order counts preimages
target: symbol-blind-automata-on-pointed-memory-are-permutive
requires:
  - symbol-blind-automata-reduce-to-defect-counting
artifacts:
  - experiments/symbol-blind-automata-2026-09-17/fd_sector_vs_measure.py
  - experiments/symbol-blind-automata-2026-09-17/fd_sector_results.txt
  - experiments/symbol-blind-automata-2026-09-17/pair_graph_over_z.py
  - experiments/symbol-blind-automata-2026-09-17/pair_graph_results.txt
---

Notation as in the claim. For a configuration x write psi_x(g) = g sigma(pi_g x),
so tau_q(x) = x o psi_x. Write K = M^{-1}M.

## 0. The order and two colouring facts

**The order.** Say g ≺ h if h = g m_1 ... m_r with r >= 1 and every m_i in
M \ {e}. This relation is transitive. It is irreflexive exactly because M is
pointed. So ≺ is a strict partial order, and every finite nonempty set has
≺-minimal and ≺-maximal elements.

- Every m in M \ {e} satisfies e ≺ m.
- If psi_x(g) != g, then psi_x(g) = gm with m != e, so g ≺ psi_x(g).

**Window-faithful colourings** (section 3 of the reduction proof). Let D be
finite. Let P be a partition of G whose non-singleton classes lie in D. Colour
the classes of P meeting D injectively from a palette A1. Colour G \ D
properly for the graph u ~ v iff u != v and v ∈ uK, using a palette A2
disjoint from A1 with |A2| = |K|. This graph has degree at most |K|-1, so such
a colouring exists (greedy on finite subgraphs, then compactness).

The result x satisfies pi_g x = pi_g P for every g, and hence psi_x = psi_P.

**Recolouring lemma.** Let u be a singleton class of P, and let x' be x with
u recoloured by a colour of A1 used nowhere on D. Then x' is window-faithful to
the same P. If no g has psi_P(g) = u, then tau(x') = x' o psi_P = x o psi_P =
tau(x). So x and x', which differ only at u, have the same image.

## 1. Pre-injective at q >= |M|+|K| implies P1

Suppose some partition P_0 of M has {e} as a class and sigma(P_0) = s != e.
P_0 is not discrete, so it has at most |M|-1 classes.

Let P be the partition of G that equals P_0 on M, with every other point a
singleton. Take D = M. Let S = {g : psi_P(g) != g}. S is finite: if g is
outside MM^{-1}, the window gM meets M in at most one point, so pi_g P is
discrete and psi_P(g) = g. Also e ∈ S.

Choose g_0 in S, ≺-minimal among the elements of S that are ≼ e.

- **g_0 is a singleton class of P.** Either g_0 = e, which is a singleton by
  hypothesis, or g_0 ≺ e. In the second case g_0 is not in M \ {e}: otherwise
  e ≺ g_0 ≺ e. So g_0 is outside the support M \ {e} of the non-singleton
  classes.
- **g_0 is unhit.** psi_P(g_0) != g_0 because g_0 ∈ S. If g != g_0 and
  psi_P(g) = g_0, then g ∈ S and g ≺ g_0 ≼ e, which contradicts minimality.

Colour with |A1| = #classes of P_0 + 1 <= |M| (one spare colour) and
|A2| = |K|, so q >= |M| + |K| suffices. The recolouring lemma at u = g_0
gives two configurations differing at one point with equal images. So tau_q is
not pre-injective.

## 2. Pre-injective at q >= |M|+|K| implies P2

Assume P1. Let rho be a partition of M \ {e} with classes C_1..C_k, and
suppose tau_rho(i) = tau_rho(j) = l with i != j.

Colour M \ {e} injectively on the classes of rho from A1, with |A1| = k <= |M|-1.
Colour G \ M properly from A2 as in section 0. Let x(e) be the colour of C_i,
and x'(e) the colour of C_j. Otherwise x' = x. So x and x' differ only at e.

The outputs agree at every g:

- **g outside M^{-1}.** The window gM does not contain e, so the windows and
  the outputs agree.
- **g = e.** The window partitions are rho with e joined to C_i, and rho with
  e joined to C_j. The selected points lie in C_l or C_l ∪ {e}. In both
  configurations every point of that class carries the colour of C_l. So
  tau(x)(e) = tau(x')(e).
- **g in M^{-1} \ {e}.** Here g^{-1} ∈ M \ {e}, so g ≺ e, and g is not in M
  (it is not e, and not in M \ {e} since e ≺ m for those). So x(g) = x'(g) is
  an A2 colour, distinct from every other colour in gM. So {e} is a class of
  pi_g x and of pi_g x'. By P1 both outputs are x(g).

So tau(x) = tau(x') with x != x', and tau_q is not pre-injective. Hence
tau_rho is injective, and so a permutation.

**P1 and P2 are e-permutivity.** Fix the values on M \ {e}, with kernel rho and
value set V, |V| = k. For x_e outside V, {e} is a class, and P1 gives output
x_e: a bijection of [q] \ V. For x_e equal to the value of C_j, the output is
the value of C_{tau_rho(j)}: a bijection of V. Conversely, if P1 fails, the
output is constant on [q] \ V, which has at least two elements when q >= |M|+1.
If P2 fails, two inputs in V collide. The count of e-permutive selectors
follows: sigma is forced on partitions where {e} is a class, and is free up to
a permutation tau_rho for each rho.

## 3. e-permutive implies pre-injective at every q

Let x != x' differ exactly on a finite nonempty set Z. Take d ≺-maximal in Z.

- For m ∈ M \ {e} we have d ≺ dm, so dm is not in Z and x(dm) = x'(dm).
- x(d) != x'(d).

By e-permutivity the local rule at d separates them: tau(x)(d) != tau(x')(d).

This proves 2 => 3. 3 => 1 is trivial, and sections 1 and 2 give 1 => 2.

## 4. Uniform preimage counts

Let F be finite, E = FM and y ∈ [q]^F. List F as f_1, ..., f_n with f_i
before f_j whenever f_i ≻ f_j (a linear extension of the reverse order).

Choose x on E \ F arbitrarily: q^{|E|-|F|} ways. Then for i = 1..n choose x(f_i):

- **The window is already set.** Each point f_i m with m != e is either
  outside F, or in F and ≻ f_i, hence listed earlier.
- **Exactly one value works.** By e-permutivity exactly one value of x(f_i)
  gives tau(x)(f_i) = y(f_i).
- **Earlier outputs are unchanged.** Suppose some earlier f_j has f_i in its
  window, f_i = f_j m with m != e. Then f_i ≻ f_j, so f_i precedes f_j,
  a contradiction.

Every x on E with tau(x)|_F = y arises exactly once this way. So the count is
q^{|FM|-|F|}.

- **Surjective.** Every finite pattern has a preimage, and the image is closed,
  so tau_q is onto.
- **Measure preserving.** The cylinder counts give statement (b) of part 4 of
  symbol-blind-automata-reduce-to-defect-counting, so the identities (c) hold
  at every order.
- **Corollaries.** Injective at one q >= |M|+|K| implies pre-injective, which
  implies all of the above.

## 5. Sharpness checks

- **Minority rule on {0,1,2}.** Direct evaluation gives the Z/6 collision.
  `python3 fd_sector_vs_measure.py minority` prints it. The rule factors through
  Z -> Z/6, so it is not injective over Z. By section 3 it is pre-injective at
  every q.
- **Centred minority rule on {0,-1,1}.** Evaluate f(l,c,r) on the windows of
  the two segments 0 1 0 0 1 0 and 0 1 2 2 1 0, at the four central cells.
  - First segment: windows (0,1,0), (1,0,0), (0,0,1), (0,1,0) give 1,1,1,1.
  - Second segment: windows (0,1,2), (1,2,2), (2,2,1), (2,1,0) give 1,1,1,1.
  - The two outer cells agree, and every other window sees only agreeing cells.

  So the rule is not pre-injective at q = 3. It is e-permutive, so section 3
  fails without pointedness. The step that breaks is the existence of a
  ≺-maximal changed cell.
- **Sections 1 and 2 also need pointedness.** The selector R29 of the claim
  lives on M = {0,-1,1,2}. It is permutive in no coordinate, yet
  `pair_graph_over_z.py` shows it is pre-injective at every q. There P1 fails,
  and the ≺-minimal unhit singleton of section 1 does not exist.
- **Exact decider.** Over Z, `pair_graph_over_z.py` builds the pair graph on
  equality patterns of two sliding windows.
  - Not pre-injective iff some path goes from the diagonal, off it, and back.
  - Not injective iff some off-diagonal state is reachable from a cycle and
    reaches a cycle.
  - A quotient path lifts by choosing fresh symbols, so q = 2..2w decides
    every q.

  On pointed memories it confirms the theorem for every e-permutive selector.

## Remark: the finite-defect checks follow from pre-injectivity

Section 3 of the reduction proof derives three facts from injectivity at every q:

- psibar_P is onto;
- the defect is preserved;
- T is injective on FD(G).

Each contradiction there compares configurations x != x' that differ only on
a finite set D. So pre-injectivity at every q suffices, and a rule failing
the census's fd checks is not pre-injective at some q. Pre-injectivity is
also the hypothesis of the Myhill direction. For general automata that
direction holds exactly over amenable groups (Bartholdi, with an appendix by
Kielak, J. Eur. Math. Soc. 21 (2019)). So no argument that ignores the
symbol-blind structure can prove the defect-counting identities from
pre-injectivity. Sections 1 and 2 use that structure through recolouring.
