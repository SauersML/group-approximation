# Idea lane bh-tm-encoding: Turing-machine encodings in Cantor homeomorphism groups

Target: `boone-higman-conjecture`. Lens: realize an arbitrary finitely
generated group with solvable word problem inside a finitely presented group
of Cantor homeomorphisms whose germs run the input's word-problem algorithm.

Status: ideation only. No node changes status. Nothing here is claimed solved.

## Summary

| # | Approach | Verdict |
|---|---|---|
| 1 | Fixed machine hosts (nV, circuit groups, Turing-machine groups, VA) | killed as universal hosts |
| 2 | Unbounded-time germs as first-return maps on clopen sets | killed (compactness) |
| 3 | Linearize the machine and use a linear actor | killed as universal actors |
| 4 | Machine-generated shell enumerations with singular induced germs | unclear |
| 5 | Renormalized machine germs defined by a self-referential relator | killed in the disjoint-support form; unclear with feedback |

Constraints forced by the kill tests, in order:

- **C1.** No fixed host works. The target's word-problem complexity has to rise
  with the input's.
- **C2.** Germs can't be finite-state or rational, and the actor can't be linear.
- **C3.** Running unbounded time inside one group element forces singular points,
  so the finite germ extension regime of the shell route is necessary, not a
  design choice.
- **C4.** In that regime a successful enumeration needs a mixed near relation
  and unbounded generator displacement.

## 1. Fixed machine hosts

**Idea.** Put every input inside one natural finitely presented group that can
simulate Turing machines. Candidates:
- the Brin--Thompson groups nV;
- Birget's circuit-simulating Thompson--Higman groups;
- the finitely generated group of elementary Turing machines of
  Barbieri--Kari--Salo;
- Belk--Hyde--Matucci's finitely presented simple group VA, which contains
  every countable abelian group.

**Would prove.** A universal finitely presented simple host, and hence
Boone--Higman.

**Kill test.** One host has one word-problem time bound. Compare that bound with
`uniform-wp-bound-excludes-bh-universal-targets` (the complexity wall on main).

**Result.** Killed.
- Any single finitely presented simple group has decidable word problem with
  some recursive time bound. The wall then gives a finitely presented residually
  finite decidable input that embeds in no member of the class.
- Birget proves the word problem of nV is coNP-complete for n >= 2
  (arXiv:1902.03852, abstract checked), so the wall applies with an explicit
  ceiling.
- For the rational group, `rational-homeomorphism-subgroups-have-exponential-wp`
  gives the ceiling directly. Belk--Bleak (arXiv:1405.0982, abstract checked)
  show that 2V already contains enough machine dynamics to make its torsion
  problem undecidable, but that does not raise its word-problem ceiling.

**Constraint.** C1.

## 2. Unbounded-time germs as first-return maps on clopen sets

**Idea.** Simulate a Turing machine by a homeomorphism T in a Thompson-like
group, and adjoin the induced maps T_U, the first-return maps to clopen sets U.
An induced map runs T for as many steps as the input needs, so it looks like a
way to put an unbounded computation into one group element.

**Would prove.** A germ class with computation time that is not bounded, which
would escape the finite-state wall.

**Kill test.** Is the return time bounded?

**Result.** Killed by a hand argument.
- Let T be a homeomorphism of the Cantor set C, and U a clopen set on which
  every point returns.
- Each level set U_n = {x in U : first return at time n} is a finite Boolean
  combination of the clopen sets T^-k(U), so it is clopen.
- The U_n are disjoint and cover the compact set U, so only finitely many are
  nonempty. Hence the return time is bounded.
- Then T_U agrees with T^n on U_n, and is a finite piecewise gluing of powers of
  T on a clopen partition. It lies in the topological full group of T.
- If T is rational, T_U is rational too, since gluing along finitely many
  cylinders is realized by a transducer. So nothing escapes approach 1.

**Constraint.** C3. Unbounded running time can occur only where the return time
is not locally bounded, that is, at singular points. This is exactly the finite
germ extension regime of `shell-cantor-embeddings-are-finite-germ-extensions`.

## 3. Linearize the machine

**Idea.** Encode the input's machine by matrices, as counter machines as
matrices over a ring. Then use a linear or self-similar polynomial host of the
kind that settled the linear case, or E. A. Scott's 1984 construction of finitely
presented simple groups from linear data (J. Algebra 90; only abstract-level
information was seen here, the paper was not re-read).

**Would prove.** A linear actor containing every input, then fp simple envelopes
through `twisted-brin-thompson-finite-presentation-criterion`.

**Kill test.** The word-problem complexity of finitely generated linear groups.

**Result.** Killed as a universal method.
- Finitely generated linear groups have logspace word problem: Lipton--Zalcstein
  1977 in characteristic zero, Simon 1979 in positive characteristic. This was
  checked through the secondary statement in arXiv:1909.13781; the originals
  were not re-read.
- The actor must contain the input, because the orbit problem of the twisted
  Brin--Thompson host contains the actor's word problem
  (`twisted-brin-thompson-wp-equals-actor-orbit-problem` (a)). So hardness can't
  be hidden in the orbit or stabilizer problem.
- The wall with g polynomial kills every universal linear actor.
- Scott's conjugacy-problem examples don't conflict with this: they concern
  conjugacy, not the word problem.

**Constraint.** C2. The machine has to live in non-linear actors.

## 4. Machine-generated shell enumerations with singular induced germs

**Idea.** Stay inside the shell construction. Replace the arbitrary enumeration
nu with one generated by a reversible Turing machine M that walks the Cayley
graph of the input P, using P's word-problem algorithm. For example, take a
Bennett-reversible traversal whose g-subroutine takes configuration index n to
index nu(g * nu^-1(n)).
- Realize hat(g) as a singular induced map of a machine homeomorphism: its time
  to return from the shell 0^n1C grows with n, and it is singular only at
  p = 0^infinity.
- The hope is that the finitely many local rules of M supply the mixed near
  relation that `free-shift-shell-envelopes-are-not-finitely-presented` demands.
  That is, some nonidentity reduced word of P*<s> becomes finitary.

**Would prove.** E_nu finitely presented for a computable nu. That closes
`decidable-inputs-have-fp-shell-envelopes`, and Boone--Higman follows through
`boone-higman-via-fp-shell-envelopes`. For perfect inputs E_nu is already simple
(`perfect-decidable-inputs-have-fp-shell-envelopes`).

**Kill tests run.**
- **Displacement.** `regular-enumeration-displacement-bounds-growth` forces
  D_nu(r) >= r + 1 for Z^2. A machine traversal such as the square spiral has
  displacement of order sqrt(n) at index n, and a reversible machine can compute
  it. Not killed.
- **Mixed near relation.** For Z^2 with the square spiral, s^-1 rho_e1 acts
  trivially on the interiors of the south sides of all rings, but not on the
  other three sides. Every side has infinitely many points, and the germ group at
  p contains only <tau> from V, so no piecewise repair is available there. I
  found no short finitary word by hand. Nor could I prove that none exists.

**Verdict.** Unclear.

**Next test.** For P = Z^2 and a few machine enumerations (square spiral,
boustrophedon, a Cantor pairing), search all words of length <= 10 in
{rho_e1, rho_e2, s} for words that act finitarily. That directly tests the
necessary condition of the free-shift obstruction. It is a small computation and
belongs on MSI.

## 5. Renormalized machine germs defined by a self-referential relator

**Idea.** Thompson-type finite presentations come from self-similarity: a
cone's restriction is conjugate to the whole. Define a singular homeomorphism h
by one recursive relator:
- h equals sigma h sigma^-1 composed with m on the cone 0C;
- h is the identity on 1C.
Here sigma: C -> 0C is the prefix map and m is one step of a rational machine
homeomorphism.
- Unrolled, h should run one more machine step per level of depth.
- It is singular only at p = 0^infinity, and it satisfies an ascending-HNN-like
  relation over a finitely presented Thompson-type base, the classical engine of
  finite presentation.

**Would prove.** Groups <2V, h_1, ..., h_k> with non-rational germs that
accumulate unbounded computation, but with defining relations of bounded shape.
If they are finitely presented and contain inputs with hard word problems, they
escape C1 and C2 while satisfying C3.

**Kill test.** Is h well-defined, and is it non-rational?

**Result.**
- **Disjoint-support form: killed** (hand argument). If m is supported in 1C,
  the conjugates sigma^k m sigma^-k have disjoint supports 0^k1C.
  - h acts on each cone 0^k1C by a single conjugate, so every point sees a
    bounded amount of computation.
  - h is then sigma-self-similar with finitely many states, so rational, and
    approach 1 applies.
- **Feedback form: unclear.** Here m acts across depths, so information passes
  between levels. The unrolled h composes n genuine machine steps at points of
  depth n, which a transducer should not be able to reproduce.
  - The open issue is well-definedness. If m changes depth, the recursion depth
    along an orbit need not be monotone, and termination and continuity away
    from p could fail.
  - A sufficient condition to test: m preserves the depth partition {0^n1C},
    moving points only between shells of equal depth.

**Verdict.** Killed in the disjoint-support form, unclear with feedback.

**Next test.** Take m to be the odometer step, and check that h is well-defined
and conjugate to a known group. Compare with
`research/artifacts/boone-higman-arithmetic-odometer-model-2026-09-08.md`, which
was not read here. Then try a two-counter reversible machine and check whether h
is still well-defined under the depth-preserving condition.

## Sources checked in this lane

Abstracts or secondary statements only, as marked above:

- Birget, "The word problem of the Brin--Thompson group is coNP-complete",
  arXiv:1902.03852: nV has coNP-complete word problem for n >= 2.
- Belk--Bleak, "Some undecidability results for asynchronous transducers and
  the Brin--Thompson group 2V", arXiv:1405.0982: undecidable torsion problem in
  2V.
- Barbieri--Kari--Salo, "The group of reversible Turing machines",
  arXiv:1603.08715: the elementary Turing machine group is finitely generated;
  the group of reversible Turing machines is not.
- Belk--Hyde--Matucci: the finitely presented simple group VA contains every
  countable abelian group. Seen through a search summary only, not re-read.
- Lipton--Zalcstein 1977 and Simon 1979: logspace word problem for finitely
  generated linear groups. Seen through arXiv:1909.13781.

Repo nodes used:
- `uniform-wp-bound-excludes-bh-universal-targets`
- `rational-homeomorphism-subgroups-have-exponential-wp`
- `decidable-fp-groups-need-not-embed-in-rational-group`
- `twisted-brin-thompson-wp-equals-actor-orbit-problem`
- `shell-cantor-embeddings-are-finite-germ-extensions`
- `free-shift-shell-envelopes-are-not-finitely-presented`
- `regular-enumeration-displacement-bounds-growth`
- `decidable-inputs-have-fp-shell-envelopes`
- `perfect-decidable-inputs-have-fp-shell-envelopes`
- `boone-higman-via-fp-shell-envelopes`
