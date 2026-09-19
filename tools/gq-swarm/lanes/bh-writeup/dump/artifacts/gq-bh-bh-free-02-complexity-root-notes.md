# bh-free-02: notes on the complexity root (09-18)

Free lane, logic/computability seed. Target:
`fp-simple-groups-with-arbitrarily-complex-word-problem` (Birget's question). It is
a necessary consequence of Boone--Higman, strictly weaker, and OPEN. These notes
record what was checked, so later lanes do not repeat it. Only
`equivariant-scaling-hnn-vertex-groups-are-linear` is a claim; everything else
here is analysis.

## 1. Where hardness can enter a finitely presented simple host

A host `S` beats a bound `T` as soon as it contains one finitely generated group
that beats `T` (length-linear substitution, step 3 of
`arbitrarily-complex-fp-simple-via-hard-self-similar-groups`). So every route is
"BH for one hard input per bound". The hard inputs in the graph are:
- the graph-shift groups `G_A` (`graph-shift-groups-have-arbitrarily-hard-word-problem`),
  which are not finitely presented;
- the dual-certificate groups `H_f` (`dual-certificate-groups-force-large-host-dehn-functions`);
- the Kharlampovich--Myasnikov--Sapir groups (`kms-arbitrarily-hard-fp-rf-groups`),
  which are finitely presented and residually finite.

Every class on main that is known to satisfy BH has uniformly bounded word problem:
linear groups, hyperbolic groups, contracting self-similar groups, rational
homeomorphism groups, `Aut(F_n)`, Baumslag--Solitar and free-by-cyclic groups. So
no existing class supplies a hard input. The construction must consume the
input's algorithm (`compilers-cannot-drop-the-decidability-hypothesis`).

## 2. Finite-index HNN extensions (Bux--Llosa Isenrich--Wu Theorem 10.5)

`finite-index-edge-hnn-embeds-in-fp-simple-group` needs no envelope for the vertex
group. So a hard finitely presented residually finite `A` with a faithful HNN
extension over finite-index subgroups would settle the root unconditionally.
- **Ascending case.** This needs `A` isomorphic to a finite-index subgroup of itself,
  with no nontrivial normal subgroup invariant under the isomorphism: a weak form of
  scale invariance (Nekrashevych--Pete). Every known example (`Z^n`, Heisenberg,
  lamplighters, `BS(1,n)`, affine groups) is linear.
- **New claim.** `equivariant-scaling-hnn-vertex-groups-are-linear`: for
  `A = M ⋊ H` with `M` elementary abelian and a scaling that fixes `H`, faithfulness
  forces `A` to be linear over `F_p((x))`. This is exactly the shape a KMS group
  `T ⋊ H` offers first, so hard KMS groups admit no such scaling.
- **What is left.**
  - scalings that also move `H`, semilinearly;
  - non-ascending extensions whose two finite-index edges are proper and whose
    isomorphism is not the restriction of an automorphism.
  If `phi` is the restriction of a global automorphism `α`, then `core_A(C_1)` is
  `α`-invariant and normal, so it lies in the kernel. So `phi` must be a genuinely
  virtual isomorphism. No hard example is known.

## 3. Twisted Brin--Thompson hosts: where their hardness lives

By `twisted-brin-thompson-finite-presentation-criterion` and
`twisted-brin-thompson-wp-equals-actor-orbit-problem`, a hard `SV_G` needs a type (A)
actor `G ↷ G/P` with a hard orbit problem.

**Lemma (checked here; elementary; not landed as a node).** If `G` is finitely
presented and `P\G/P` is finite, then membership in `P` and the word problem of `G`
(for faithful actions) are decidable by double-coset search.
- *Membership.* Fix representatives `g_1 = 1, ..., g_k`. For `g` in `G`, enumerate
  equalities `g = h g_i h'` with `h, h' in P`; these are r.e. in `G`. Exactly one `i`
  occurs, and `g in P` iff `i = 1`.
- *Word problem.* `g != 1` iff some conjugate `x^-1 g x` lies outside `P`.

So solvability is automatic, and hardness can come only from the running time of
these searches. There is no a priori bound, but no mechanism is known either.

**The left-right trick** (`G = Q × Q` acting on `Q` by `z ↦ a z b^-1`) turns the
word problem of `Q` into stabilizer membership. Pair-orbits then correspond to
conjugacy classes of `Q`. This is on main as
`centerless-fp-finitely-many-conjugacy-classes-gives-pbh`.
- The version with a finitely presented `Γ <= Aut(Q)`, `Γ ∩ Inn(Q) = 1`, is also
  type (A). It acts by `(a, b, γ)·z = a γ(z) b^-1` on `(Q × Q) ⋊ Γ`. It needs only
  finitely many `Inn(Q)Γ`-orbits on `Q` (checked here; not landed).
- It still needs an exotic `Q`: infinite, finitely presented, with finitely many
  (automorphism-twisted) conjugacy classes. Whether any exists is not checked here.

## 4. Intermediate targets beyond Birget's coNP

The best known lower bound is coNP-completeness, for Brin--Thompson `nV`
(Birget, arXiv:1902.03852). Rational hosts are capped at exponential time
(`rational-homeomorphism-subgroups-have-exponential-wp`), but that cap still leaves
room for PSPACE-hard or EXPTIME-hard finitely presented simple groups.
- **Route.** Zaremsky's corollary (arXiv:2305.15176, `cor:simple_and_qr`, quoted in
  `fp-simple-group-with-at-least-exponential-dehn-function`'s artifact). A finitely
  presented, persistent, weakly diagonal, rational self-similar `G` has
  `V_d(G)` finitely presented and virtually simple.
- **What it would give.** A finitely presented automaton group of that kind with a
  PSPACE-hard word problem gives a finitely presented simple group beyond coNP,
  unless coNP = PSPACE. Automaton groups with PSPACE-complete word problems exist
  (Wächter--Weiß, STACS 2020; not read here), but they are not known to be finitely
  presented.
- **Open sub-question (not a node).** Is there a finitely presented automaton group
  with a PSPACE-hard word problem?

## 5. Dehn functions (Zaremsky Problem 1.16)

The dual-certificate node already turns BH for the groups `H_f` into the strong
reading of Problem 1.16. So any construction in sections 2–4 that hosts the `H_f`
also answers 1.16. No additional mechanism was found.
