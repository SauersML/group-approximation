# gq-ring-alt board

**Approach** (family: group rings / Leavitt units). Target (team-lead 09-18): decide (Q,+) <= U = L_(F_2)(1,2)^x.
Signature: "relative commutant units give T-bar in U". Status: NOT decided; sandwiched between two open questions.

**Established** (agent-verified only, not refereed):
- 53773cee9: unit-roots-divide-centralizer-rank; thompson-units-have-few-roots-in-leavitt-unit-group.
- 4a7f060bf: leavitt-germ-traces-satisfy-frobenius (Tr(x^2)=F(Tr x) over F_2; Z[1/2]-span in [R,R]; c not a square);
  tbar-embeds-in-laurent-leavitt-unit-group (T-bar, hence Q, in (L_k(1,2) (x) k[t^+-1])^x, any k).
- Routes: rationals-in-leavitt-units-via-diagonal-copy (inf-order unit ~ phi(unit) => Q <= U);
  diagonal-copy-nonconjugacy-from-no-rationals (Q not in U => no such unit => Ara-Cortinas 5.7 negative over F_2).

**Needs**: an infinite-order unit in some relative commutant C_u (u with components of both Z-signs; core and
triangular u are dead), or an invariant excluding one.

**Dead**: mod-2 reduction of the integral <V,t> construction (t has order 2; constant matrices over F_2 are torsion);
GL_n(Q) through commutative Leavitt subalgebras (BS(1,2) impossible in GL_m(A), A commutative char p).

**Sparks**: HH_0 Frobenius works for any F_2 Steinberg algebra with torsion-free abelian isotropy (e.g. L (x) L,
nV groupoids): a trace test for 2-divisibility there too.
