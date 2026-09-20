# The positive natural-type corner does not synchronize the signed-six source

Date: 2026-09-20. Bounded symbolic follow-up to the signed-six frame and
approximate-only-anchor notes of this date. No computation, build, or
commit was performed. All conclusions below concern their explicit
countermodel and specified natural-type corner interface. The general
HALT-positive source and perfect-completeness LCS targets remain open.

## 1. Setup and the exact question

Let K be the six-dimensional signed-permutation group

    K=(C_2)^6 semidirect S_6,     |K|=46080,

and let eta be its natural irreducible representation of dimension six.
The distinguished central sign J acts as -I in eta. The marked regular
corner H_- has dimension 23040. Denote its eta-isotypic projection by q0.
The regular representation contains eta with multiplicity six, so

    rank(q0)=36,
    w=tr(q0)=36/23040=1/640.                          (1)

Thus the earlier trace amplification really retains a positive natural
type; it does not make its weight vanish. The question tested here is
whether that type can support one globally consistent source decoder.

Use the exact graph countermodel from
`lcs-existential-frame-signed-six-sector-2026-09-20.md`:

    H_-=C^O_L tensor C^O_R tensor T,   dim T=1440,
    O={100,010,001,111},
    H=H_- tensor (tensor_i C^O_i) tensor (tensor_e T_e),
    dim T_e=1440.                                    (2)

The source reflections C_(i,a) read the bits in vertex register C^O_i.
For e=(i,j), W_e swaps L with i, R with j, and T with T_e. The copied
finite group K_e is W_e K W_e. Its complete generator family commutes
with the global K and has the correct shared source reflections.

Put

    q_e=W_e q0 W_e.                                  (3)

Each q_e is the natural-isotypic projection of the full copied group,
and each has exactly the same positive weight w as q0.

The repository's existing common-corner and finite-type intersection
nodes were checked before writing this note. Those establish broader
compatibility obstructions in different ambient constructions. The
calculation here gives the actual intersections and a leakage inequality
for this concrete newly tested model; it is not a new canonical node.

## 2. The block form of every edge corner

The six natural basis vectors are labelled by the allowed ordered pairs
of distinct colours. In eta the commuting A and B triples have exactly
these six joint one-hot patterns, each with multiplicity one. Since eta
occurs six times in H_-, q0 has the following block form in (2):

    q0 restricted to pattern (r,c) is
      a rank-six projection on T,  if r,c are distinct one-hot patterns;
      zero,                        otherwise.         (4)

The full joint (A,B) block has dimension 1440, explaining both its
selected rank six and the total selected rank 36. Centrality of the
isotypic projection makes q0 commute with A and B, so no off-diagonal
blocks between different joint patterns have been omitted.

Transporting (4), q_e is diagonal in the endpoint registers i,j, with a
rank-six reservoir projection for each allowed endpoint pair. It is zero
on every forbidden endpoint pair. It acts trivially on all other vertex
registers and all other reservoirs. Consequently

    [q_e,C_(i,a)]=0  for EVERY vertex i and colour a,
    [q_e,q_f]=0      for all edges e,f.               (5)

For the second assertion, the possibly shared vertex registers are
diagonal in the same fixed O bases; on each joint vertex block the two
edge projections act on distinct private reservoirs. The edge frames
themselves need not commute. Equation (5) is an assertion about their
selected isotypic projections in this explicit model.

## 3. Compressing only to q0 does not improve the source

All source reflections act outside H_-, so q0 commutes with them and
is independent of their joint normalized-trace distribution. On q0 H,
with its normalized corner trace, every vertex still has the four odd
patterns with probability 1/4. Thus for

    p_(i,a)=(I-C_(i,a))/2

one has exactly

    ||sum_a q0 p_(i,a) q0-q0||_(2,q0)^2=1,
    ||q0 p_(i,a) p_(i,b) q0||_(2,q0)^2=1/4  (a!=b).  (6)

The corner is nonzero, has dimension-independent weight, and even
reduces all the literal source observables. Those facts alone do not
make their compressed triples into PVMs.

There is also a direct transport cost. Since q_e acts entirely outside
H_-, q0 and q_e are independent commuting projections of trace w. Hence

    tr(q0 q_e)=w^2,
    ||(I-q_e)q0||_2^2=w(1-w),
    ||[W_e,q0]||_2^2=2w(1-w).                        (7)

The last equality uses `W_e q0 W_e=q_e`. Relative to the mass of q0,
its leakage from the transported natural type is 639/640, not a small
error controlled by target relation defects (which are zero here).

## 4. The joint selected corner is zero on K4

Decompose H according to a complete assignment of odd patterns
`r=(r_1,r_2,r_3,r_4) in O^4` to the four source registers. For every
such assignment at least one edge of K4 has a forbidden pair:

- If a vertex has pattern 111, every incident edge is forbidden.
- Otherwise all four vertices have one-hot patterns, so two receive
  the same one of three colours, and their edge is forbidden.

On that block the corresponding q_e is zero. Every other q_f is a
projection bounded above by I. There are six edges, so on every block

    sum_(e in E(K4)) q_e <=5I.

Therefore, as a full operator inequality,

    sum_e (I-q_e)>=I,
    meet_e q_e=product_e q_e=0.                      (8)

No nonzero projection can be simultaneously contained in all six
transported natural types. This does not require the proposed projection
to reduce the source words or the transporters: containment alone fails.

## 5. Quantitative leakage for arbitrary projections

Let P be ANY orthogonal projection on H, not assumed to preserve vertex
blocks or commute with any q_e. Multiplying (8) by P and taking trace
gives

    sum_e ||(I-q_e)P||_2^2 >= tr(P).                  (9)

In particular every nonzero P has at least one edge whose squared
leakage divided by tr(P) is at least 1/6. A common-corner decoder cannot
make these relative errors tend to zero by choosing a smaller but still
positive projection, or by mixing the source-pattern blocks.

There is a useful form involving the global natural type and the actual
transport words. Since q_e=W_e q0 W_e,

    ||(I-q_e)P||_2
      =||(I-q0)W_e P||_2
      <=||(I-q0)P||_2+||[W_e,P]||_2.                 (10)

Minkowski's inequality in the six edge coordinates, together with (9),
therefore gives

    sqrt(tr(P))
      <=sqrt(6)||(I-q0)P||_2
        +(sum_e ||[W_e,P]||_2^2)^(1/2).              (11)

For P<=q0 this becomes

    sum_e ||[W_e,P]||_2^2>=tr(P).                    (12)

Thus no nonzero subcorner of q0 reduces all the transporters. More
generally there is no positive-weight sequence that is asymptotically
contained in q0 and asymptotically reduces these six fixed transporters:
equation (11) forces its trace to zero. The inequality concerns these
specified frame projections and transporters, not arbitrary non-word
replacement observables.

## 6. Even satisfiable graph families lose joint-corner weight

The explicit model also shows why local weights do not give a uniform
global weight on larger YES instances. Let G have n vertices, m edges,
and no isolated vertices. By (4)--(5), the common edge corner is supported
exactly on proper three-colourings of G. On each such vertex assignment,
the m private reservoir projections have rank six each. Hence

    tr(product_e q_e)
      = (# proper 3-colourings of G)/4^n * (1/240)^m. (13)

The factor 1/240 is 6/1440. The global natural corner is independent,
so adding q0 multiplies (13) by w. For m disjoint edges, the number of
proper colourings is 6^m and n=2m, giving

    tr(product_e q_e)=w^m,
    tr(q0 product_e q_e)=w^(m+1).                    (14)

These graphs are classically satisfiable, but every projection contained
in all their chosen natural-type corners has at most the displayed mass.
This is a failure of a family-uniform retained-weight bound for this
specific simultaneous-type extraction, not a statement that those YES
instances lack other exact source models.

## 7. Approximate-only attachment preserves the obstruction exactly

The preceding note attaches Slofstra's fixed approximate-only solution
group Sigma by a commuting central product. Its matrix approximations
are `sigma_n tensor pi_G`, with the finite graph-frame model pi_G exact.
Here all the frame projections and transporters are simply

    I tensor q0,  I tensor q_e,  I tensor W_e.

Consequently (6)--(14) hold with the same normalized constants in EVERY
coordinate of that approximate-only sequence. They do not merely hold
after taking an ultralimit. At the same time all target relation defects
tend to zero, and no exact finite-dimensional negative representation
of the attached presentation exists. The primary input remains
[Slofstra, Proposition 5.1 and Lemma 3.9](https://arxiv.org/html/1703.08618),
whose exact/approximate distinction was checked in the preceding audit.

Thus this failure is not repaired by abandoning finite-dimensional
attainment. The positive 1/640 local type mass is real, but its transported
copies do not support one consistent source corner in this example.
This settles the requested test of the existing candidate. It does not
settle a different source-specific coupling, a nonreducing channel with
new output observables, or the full perfect-completeness hardness goal.
