# Class stabilizers of normal fibres in SL_3(Z) are virtually cyclic (2026-09-16)

Special-case / strengthening swarm lane, root `zaremsky-3-04-sl3z-coherent`.
Supports the claim `sl3z-normal-fibre-class-stabilizers-are-virtually-cyclic`
and its route `sl3z-normal-fibre-class-stabilizers-are-virtually-cyclic-proof`.
Unreviewed.

## 0. Summary, and what is new

Let `K <= SL_3(Z)` and `N ◁ K`. For `c in N` write `[c]_N` for its
`N`-conjugacy class, and let `K/N` act on these classes by conjugation.

- **Lemma H (centralizer Hirsch lengths).** For `g in SL_3(Z)` of infinite
  order, `h(C(g)) <= 2` unless `g^2` is a transvection `I + m v w^T`
  (`v, w` primitive integral, `w^T v = 0`, `m != 0`). In that case
  `C(g^2)` is `SL_3(Z)`-conjugate to `{[[±1,x,y],[0,1,z],[0,0,±1]]}`, of
  Hirsch length 3, and contains the lattice `U_v(Z)` of the unipotent radical
  of the stabilizer of the rational line `Qv`.
- **Theorem E.** If `N` is finitely generated and not virtually solvable, then
  for every `c in N` of infinite order, `Stab_{K/N}([c]_N) ≅ C_K(c)/C_N(c)` is
  finite or virtually infinite cyclic. No hypothesis on `K`.
- **Corollary E1.** If some such class has a finite `K`-orbit, `K/N` is
  virtually cyclic, and `K` is virtually `N` or `N x| Z`.
- **Corollary E2.** If moreover `N` is free of finite rank or a closed surface
  group, `K` is coherent (Feighn–Handel; Scott).
- **Corollary E3.** The same conclusions hold when the finite orbit is on the
  `N`-classes of a subgroup `A <= N` with `A ≅ F_2`. This uses Nielsen's
  commutator lemma, not the virtual freeness of `Out(F_2)`. So Theorem E plus
  Nielsen reproves "`N ≅ F_2` normal implies `K/N` virtually cyclic".
- **Corollary E4 (cusp constraint).** If `F_2 ≅ N ◁ K` with `K/N` infinite,
  the commutator of a basis of `N` is either virtually unipotent or has an
  irreducible, totally real characteristic polynomial.
- **Corollary E5 (bounded surfaces).** A surface-with-boundary fibre whose
  monodromy permutes the boundary classes gives a coherent `K` that is
  virtually `F_n` or `F_n x| Z`.
- **Remark E6.** Free-by-free subgroups reduce to monodromy that virtually
  fixes no proper free factor class.

**What is new relative to the graph and to the in-flight peer lane.** The
peer artifact `research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md`
(frontier lane, same day, not landed when this was written) proves
`Stab_{K/N}([c]_N)` *polycyclic* (its Lemma S), `K/N` *virtually polycyclic*
under a finite orbit (Corollary S1), and "virtually polycyclic; cyclic if the
quotient is free" for bounded-surface fibres (Corollary A4).

- Theorem E improves "polycyclic" to "virtually cyclic" for every finitely
  generated, not virtually solvable `N`. This is a Hirsch-length gap: the
  a priori bound is `h <= 2`, and `h = 2` is excluded by combining the landed
  claims `sl3z-infinite-index-normal-fibers-force-zariski-density` and
  `sl3z-dense-with-unipotent-lattice-has-finite-index`.
- Corollaries E1, E2 and E5 turn "virtually polycyclic" into coherence of `K`
  whenever `N` is free or a surface group. This excludes, for example, every
  `N`-by-`Z^2` and every `N`-by-(virtually polycyclic of Hirsch length at
  least 2) in which the quotient virtually fixes one infinite-order class.
  Those quotients are not free, so Corollary S2 of the peer lane does not
  apply to them.
- Lemma H with Corollary E4 is a new arithmetic constraint on any thin
  `F_2 x| Z` in `SL_3(Z)`. Long–Reid's family is consistent with it
  (Section 5).

No novelty is claimed for the classical inputs (Section 1). The search for
prior statements is recorded in Section 6.

## 1. Imports

From the graph (landed nodes; derivation status queried with `bin/cairn why`
on 2026-09-16):

- **(G1)** `sl3z-infinite-order-centralizers-are-solvable`: for `g in SL_3(Z)`
  of infinite order, `C(g) := C_{SL_3(Z)}(g)` is solvable.
- **(G2)** `sl3z-infinite-index-normal-fibers-force-zariski-density`: if
  `L <= SL_3(Z)` is finitely generated and `N ◁ L` is infinite, finitely
  generated, of infinite index and not virtually solvable, then `L` and `N` are
  Zariski-dense and `[SL_3(Z) : L] = ∞`.
- **(G3)** `sl3z-dense-with-unipotent-lattice-has-finite-index`: a Zariski-dense
  subgroup of `SL_3(Z)` containing a finite-index subgroup of `U(Z)`, with `U`
  the unipotent radical of the stabilizer of a rational line or plane, has
  finite index.
- **(G4)** `sl3z-products-of-infinite-subgroups-are-polycyclic`, used only in
  Section 4: commuting infinite subgroups generate a polycyclic group.

Classical facts, recalled and not re-read this session:

- **(C1)** Mal'cev: a solvable subgroup of `GL_n(Z)` is polycyclic.
- **(C2)** Hirsch length `h` of polycyclic groups (e.g. D. Segal, *Polycyclic
  groups*, Cambridge 1983, Chapter 1):
  - it is additive on extensions, `h(P) = h(Q) + h(P/Q)` for `Q ◁ P`;
  - `h(Q) <= h(P)` for `Q <= P`, with equality iff `[P : Q] < ∞`;
  - `h(P) = 0` iff `P` is finite, and `h(P) = 1` iff `P` is virtually
    infinite cyclic;
  - polycyclic groups are finitely generated.
  `h(Z^r) = r`, and a torsion-free abelian subgroup of `Q^r` that is
  finitely generated has `h <= r`.
- **(C3)** Dirichlet's unit theorem for orders: if `O` is an order in a number
  field with `r_1` real and `r_2` complex places, `O^×` is finitely generated
  of rank `r_1 + r_2 - 1`.
- **(C4)** Linear algebra. If `g in M_3(Q)` has squarefree characteristic
  polynomial `χ`, the commutant of `g` in `M_3(Q)` is `Q[g] ≅ Q[x]/(χ)`.
  `SL_n(Z)` acts transitively on primitive vectors of `Z^n`.
- **(C5)** Nielsen: every automorphism of `F(a, b)` maps `c = [a, b]` to a
  conjugate of `c` or of `c^-1`. A complete proof from the elementary Nielsen
  generators is in the peer artifact (its Lemma N). The generator identities
  and 3000 random products are checked by
  `experiments/sl3z-normal-free-rank-two-2026-09-16/nielsen_commutator_check.py`,
  which also confirms that the sign equals the determinant on `H_1`.
- **(C6)** Coherence of fibres of one:
  - M. Feighn and M. Handel, *Mapping tori of free group automorphisms are
    coherent*, Ann. of Math. 149 (1999): `F_n x| Z` is coherent;
  - G. P. Scott, *Compact submanifolds of 3-manifolds*, J. London Math. Soc.
    (1973): fundamental groups of 3-manifolds are coherent. This covers
    closed surface bundles over the circle.
  Neither was re-read this session. The title and journal of both are
  recalled. The page ranges are omitted.
- **(C7)** P. Hall: a group with a finitely presented subgroup of finite index
  is finitely presented. Hence coherence passes to finite-index overgroups: if
  `K' <= K` has finite index and is coherent, and `H <= K` is finitely
  generated, then `H ∩ K'` is finitely generated, hence finitely presented, so
  `H` is finitely presented.

## 2. Lemma H: Hirsch lengths of centralizers

For primitive `v in Z^3`, put `U_v(Z) = {I + v x^T : x in Z^3, x^T v = 0}`.
These are exactly the integral points of the unipotent radical `U_v` of the
stabilizer of the rational line `Qv`: that radical consists of the `h` with
`hv = v` acting trivially on `Q^3/Qv`, i.e. `h = I + v x^T` with `x^T v = 0`,
and `v x^T` is integral iff `x` is, because `v` is primitive.

**Lemma H.** Let `g in SL_3(Z)` have infinite order, with characteristic
polynomial `χ`, and put `C(g) = C_{SL_3(Z)}(g)`. Then `C(g)` is polycyclic and
at least one of the following holds.

- **(a)** `χ` is irreducible over `Q`. Then `C(g)` is abelian of rank
  `r_1 + r_2 - 1` for the cubic field `Q[x]/(χ)`: 2 if `χ` is totally real,
  1 otherwise.
- **(b)** `χ = (x - ε) q(x)` with `ε = ±1` and `q` an irreducible quadratic.
  Then `h(C(g)) <= 1`.
- **(c)** `χ = (x - 1)^3` and `(g - I)^2 != 0`. Then `h(C(g)) <= 2`.
- **(d)** `g^2 = I + m v w^T` with `v, w in Z^3` primitive, `w^T v = 0` and
  `m in Z \ {0}`. Then `C(g) <= C(g^2)`, `h(C(g^2)) = 3`, and
  `U_v(Z) <= C(g^2)`.

Consequently `h(C(g)) <= 3`. If `P <= C(g)` and `h(P) = 3`, then (d) holds,
`[C(g^2) : P] < ∞`, and `P ∩ U_v(Z)` has finite index in `U_v(Z)`.

*Proof.* `C(g)` is polycyclic by (G1) and (C1).

**The shape of `χ`.** `χ` is monic in `Z[x]`, and the product of its roots is
`det g = 1`.

- Suppose `χ` has a repeated root `λ`. If `λ` were irrational, its minimal
  polynomial `p` would have degree at least 2 and `p^2 | χ`, which is
  impossible in degree 3. So `λ in Q` is an algebraic integer dividing 1, hence
  `λ = ±1`. Then `χ = (x - λ)^2 (x - μ)` with `μ in Z` and `λ^2 μ = 1`, so
  `μ = 1`.
- Suppose `χ` is squarefree and reducible. It has a rational root, which is
  `ε = ±1`, and `χ = (x - ε) q(x)`. If `q` were reducible, all three roots
  would lie in `{1, -1}`, which is impossible for three distinct roots. This is
  case (b).
- Otherwise `χ` is irreducible: case (a).

**Case (a).** By (C4) the commutant of `g` in `M_3(Q)` is the cubic field
`F = Q[g]`. `O := Q[g] ∩ M_3(Z)` is a subring containing `Z[g]` and a finitely
generated `Z`-module, so it is an order in `F`. If `h in C(g)`, then `h` and
`h^-1` lie in `O`, so `C(g) <= O^×`. Conversely `u in O^×` lies in `GL_3(Z)`
and commutes with `g`. So `C(g)` is the kernel of `det = N_{F/Q}` from `O^×` to
`{±1}`, and (C3) gives the rank.

**Case (b).** By (C4) the commutant is `Q[g] ≅ Q × E`, with `E = Q[x]/(q)` a
quadratic field. As in (a), `C(g) <= O^×` with `O = Q[g] ∩ M_3(Z)`. Every
element of `O` is an integral matrix, hence integral over `Z`, so
`O <= Z × O_E`. A unit of `O` is a unit of `Z × O_E`, so
`C(g) <= {±1} × O_E^×`, whose rank is at most 1 by (C3).

**Repeated root.** `χ = (x - λ)^2 (x - 1)` with `λ = ±1`. If `g` were
diagonalizable, its eigenvalues would be `±1` and `g^2 = I`, which has finite
order. So the Jordan decomposition `g = s u` over `Q` has `u = I + n` with
`n != 0` nilpotent, and `s` and `n` are polynomials in `g`.

- **`λ = 1`.** Then `s = I` and `g = I + n`. If `n^2 != 0`, this is case (c).
  If `n^2 = 0`, then `im n <= ker n`, so `rank n <= 1`, and
  `g^2 = I + 2n` has the form in (d), shown below.
- **`λ = -1`.** `s` has eigenspaces `V_-` of dimension 2 and `V_+` of
  dimension 1. `n` commutes with `s`, so it preserves both. It vanishes on
  `V_+` and is nilpotent on `V_-`, so `n^2 = 0` and `rank n = 1`. Also `s^2 = I`,
  so `g^2 = s^2 u^2 = I + 2n`.

**Normal form in the transvection case.** Let `t = g^2 = I + n'`, with `n'`
integral, `n'^2 = 0` and `rank n' = 1`.

- Write `n' = r v w^T` with `v, w` primitive integral and `r in Q^×`. The gcd
  of the entries `v_i w_j` is `gcd(v) gcd(w) = 1`, so `r =: m` is an integer.
  Also `0 = n'^2 = m^2 (w^T v) v w^T` forces `w^T v = 0`.
- Choose `γ in SL_3(Z)` with `γ v = e_1` (C4). Then
  `γ t γ^-1 = I + m e_1 w'^T`, with `w' = γ^-T w` primitive and
  `w'^T e_1 = w^T v = 0`, so `w' = (0, p, q)`.
- Choose `δ = diag(1, δ_0)` with `δ_0 in SL_2(Z)` and `δ_0^-T (p, q)^T = e_2`.
  Then `δ e_1 = e_1` and `δ^-T w' = e_3`.
- Conjugation by `δγ` sends `t` to `I + m E_13`, where `E_13 = e_1 e_3^T`.
  It sends `U_v(Z)` onto `U_{e_1}(Z)`, because
  `γ (I + v x^T) γ^-1 = I + (γ v)(γ^-T x)^T` and `x -> γ^-T x` preserves
  integrality and the pairing with `v`.

**Case (d), computed in normal form.** `h in SL_3(Z)` commutes with
`I + m E_13` iff `(h e_1) e_3^T = e_1 (e_3^T h)`. For rank-one matrices this
means `h e_1 = λ e_1` and `e_3^T h = λ e_3^T` for one scalar `λ`. So
`h = [[λ, x, y], [0, a, z], [0, 0, λ]]` with `λ^2 a = 1` and `λ, a in Z`,
hence `λ = ±1` and `a = 1`. Conversely every such matrix commutes with `t`.
Hence

`C(t) = { [[λ, x, y], [0, 1, z], [0, 0, λ]] : λ = ±1, x, y, z in Z }`.

- Its index-2 subgroup `λ = 1` is the integral Heisenberg group. The subgroup
  `{x = z = 0} ≅ Z` is central in it with quotient `Z^2`, so `h(C(t)) = 3`.
- `U_{e_1}(Z) = {[[1, x, y], [0, 1, 0], [0, 0, 1]]} <= C(t)`.
- `g` commutes with `g^2`, so `C(g) <= C(t)`.

**Consequences.** In cases (a)–(c), `h(C(g)) <= 2`. In case (d),
`h(C(g)) <= h(C(t)) = 3`. If `P <= C(g)` has `h(P) = 3`, then (d) holds, and
`P <= C(t)` with `h(P) = h(C(t))`. So `P` has finite index in `C(t)` by (C2),
and `P ∩ U_v(Z)` has finite index in `U_v(Z)`. ∎

**Remark (which elements have large centralizers).** `h(C(g)) >= 2` only in
three cases: `χ` irreducible and totally real, `g` regular unipotent, or `g^2`
a transvection. In the last two, `g` is virtually unipotent.

## 3. Theorem E: the Hirsch-length gap

**Bookkeeping (any group).** Let `N ◁ K`. The rule
`g . [x]_N := [g x g^-1]_N` is well defined: if `x' = n x n^-1` with
`n in N`, then `g x' g^-1 = (g n g^-1)(g x g^-1)(g n g^-1)^-1`, and
`g n g^-1 in N`. `N` acts trivially, so `K/N` acts.

`Stab_K([c]_N) = N C_K(c)`. Elements of `N` and of `C_K(c)` fix the class.
Conversely, if `g c g^-1 = n c n^-1` with `n in N`, then `n^-1 g in C_K(c)`.
`N C_K(c)` is a subgroup because `N` is normal, and the second isomorphism
theorem gives

`Stab_{K/N}([c]_N) = N C_K(c)/N ≅ C_K(c)/(C_K(c) ∩ N) = C_K(c)/C_N(c)`.

The same argument with `N_K(A)` in place of `C_K(c)` gives
`Stab_{K/N}([A]_N) ≅ N_K(A)/N_N(A)` for `A <= N`. This is the peer lane's
Lemma S(1)–(2), repeated here to keep the argument self-contained.

**Theorem E.** Let `K <= SL_3(Z)` be any subgroup, and let `N ◁ K` be finitely
generated and not virtually solvable. For every `c in N` of infinite order,
`Stab_{K/N}([c]_N) ≅ C_K(c)/C_N(c)` is finite or virtually infinite cyclic.

*Proof.* Put `K_c = N C_K(c)` and `P = K_c/N ≅ C_K(c)/C_N(c)`.

**Step 1: `h(P) <= 2`.** `C_K(c) <= C(c)` is polycyclic by Lemma H, and so is
its quotient `P`. `C_N(c)` contains the infinite cyclic group `<c>`, so
`h(C_N(c)) >= 1`. By (C2) and Lemma H,
`h(P) = h(C_K(c)) - h(C_N(c)) <= 3 - 1 = 2`.

**Step 2: if `h(P) = 2`, then `K_c` contains a unipotent-radical lattice.**
Equality forces `h(C_K(c)) = 3`. By Lemma H applied to `C_K(c) <= C(c)`:

- `c^2 = I + m v w^T` with `v, w` primitive, `w^T v = 0`, `m != 0`;
- `C_K(c) ∩ U_v(Z)` has finite index in `U_v(Z)`.

So `K_c` contains a finite-index subgroup of `U_v(Z)`, where `U_v` is the
unipotent radical of the stabilizer of the rational line `Qv`.

**Step 3: contradiction.** Assume `h(P) = 2`.

- `K_c` is finitely generated: it is generated by finite generating sets of
  `N` and of the polycyclic group `C_K(c)` (C2).
- `N ◁ K_c` is finitely generated and not virtually solvable, hence infinite.
- `[K_c : N] = |P| = ∞`, because `h(P) = 2 > 0`.

By (G2), `K_c` is Zariski-dense and `[SL_3(Z) : K_c] = ∞`. By Step 2 and (G3),
`[SL_3(Z) : K_c] < ∞`. This is a contradiction.

**Step 4.** Hence `h(P) <= 1`, and `P` is finite or virtually infinite cyclic
by (C2). ∎

**Where each hypothesis is used.**

- *`c` of infinite order:* for `h(C_N(c)) >= 1` and for Lemma H.
- *`N` finitely generated and not virtually solvable:* only in Step 3, through
  (G2). If `c^2` is not a transvection, Lemma H gives `h(C_K(c)) <= 2`, so
  `h(P) <= 1` with no hypothesis on `N` beyond `c in N`.
- *No hypothesis on `K`:* `K_c` is automatically finitely generated.

**The hypotheses cannot be dropped.** Let `c = I + E_13`, `N = <c> ≅ Z`, and
`K = C(c)`. Then `N ◁ K`, and `K/N` contains the Heisenberg quotient `Z^2` of
Hirsch length 2, which fixes `[c]_N`. Here `N` is solvable. The integral
Heisenberg group is the only source of Hirsch length 2 in Step 1, and (G2)
with (G3) are what forbid a non-solvable fibre to sit normally over it.

**Is `h(P) = 1` attained with `K/N` infinite?** This needs a subgroup
`N x| Z <= SL_3(Z)` with `N` finitely generated, not virtually solvable and
of infinite index, whose `Z` fixes an infinite-order class. By (G2) it is thin.
A faithful Long–Reid representation (Section 5) would be an example. Their
Question 3, whether some `ρ_k` is faithful, was open in their 2010 preprint.
Its current status was not checked here.

## 4. Corollaries

Throughout, `K <= SL_3(Z)` and `N ◁ K`.

**Corollary E1 (finite orbit).** Let `N` be finitely generated and not
virtually solvable. Suppose some `c in N` of infinite order has a finite
`K`-orbit of `N`-classes. Then:

- `K/N` is virtually cyclic, and `K` is finitely generated;
- either `[K : N] < ∞`, or `K` has a finite-index subgroup `N x|_φ Z` with no
  nontrivial power of `φ` inner.

*Proof.* `K_c = N C_K(c)` has finite index in `K`, so `K_c/N` has finite index
in `K/N`, and Theorem E applies. `N` and `K/N` are finitely generated, hence so
is `K`.

Suppose `K/N` is infinite. Pick `t in K` such that `<tN>` is infinite cyclic of
finite index. Then `<t> ∩ N = 1`, and `N<t> = N x| <t>` has finite index.

Suppose `t^e` acts on `N` as conjugation by `n in N`, with `e != 0`. Then
`z := n^-1 t^e in C_K(N)`. `C_K(N)` is finite: otherwise `<N, C_K(N)>` would be
polycyclic by (G4), but `N` is not virtually solvable. So `z^r = 1` for some
`r >= 1`. Since `z` centralizes `n`, `t^{er} = (nz)^r = n^r z^r = n^r in N`,
which contradicts `<t> ∩ N = 1`. ∎

**Corollary E2 (coherence).** In Corollary E1, suppose also that `N` is free of
finite rank at least 2, or the fundamental group of a closed surface of
negative Euler characteristic. Then `K` is coherent.

*Proof.* By E1, `K` has a finite-index subgroup `K'` equal to `N` or to
`N x| Z`.

- `N` free: finitely generated subgroups of free groups are free, hence
  finitely presented. `F_n x| Z` is coherent by Feighn–Handel (C6).
- `N = π_1(Σ)` closed: `N x|_φ Z` is the fundamental group of the mapping torus
  of a homeomorphism of `Σ` inducing `φ`, which exists by the Dehn–Nielsen–Baer
  theorem (recalled, not re-read). It is a closed 3-manifold group, coherent by
  Scott (C6). `N` itself is a 3-manifold group (`Σ x S^1` has `π_1 = N x Z`,
  which contains `N`), so it is coherent as well.

Coherence passes from `K'` to `K` by (C7). ∎

**Corollary E3 (finite orbit on a rank-two free subgroup).** Let `A <= N` with
`A ≅ F_2`, and suppose the `N`-class `[A]_N` has a finite `K`-orbit. Then
`K/N` is virtually cyclic. No hypothesis on `N` is needed.

*Proof.* Let `L = N_K(A)`. Then `K_A = N L` has finite index in `K`, and
`K_A/N ≅ L/N_N(A)` (Section 3). Here `N_N(A) = L ∩ N` is normal in `L` and
contains `A`, so `L/N_N(A)` is a quotient of `L/A`.

Fix a basis `a, b` of `A` and put `c_A = [a, b]`. Conjugation by `l in L`
restricts to an automorphism of `A`. By (C5) it maps `[c_A]_A` to `[c_A]_A` or
to `[c_A^-1]_A`, so `L^+ = Stab_L([c_A]_A)` has index at most 2 in `L`.

Apply Theorem E to `A ◁ L^+ <= SL_3(Z)`, with `A` finitely generated and not
virtually solvable, and `c = c_A`, which has infinite order. So
`Stab_{L^+/A}([c_A]_A) = L^+/A` is virtually cyclic. Hence `L/A`, its quotient
`L/N_N(A) ≅ K_A/N`, and finally `K/N` are virtually cyclic. ∎

With `A = N ≅ F_2` the orbit is trivially finite, so E3 recovers the peer
lane's Proposition A(2): a normal `F_2` has virtually cyclic quotient. The
proof above uses Theorem E and Nielsen's lemma, not the virtual freeness of
`Out(F_2) ≅ GL_2(Z)`.

**Corollary E4 (cusp constraint).** Let `F_2 ≅ A <= N` with `[A]_N` of finite
`K`-orbit and `K/N` infinite. Let `c_A = [a, b]` for a basis of `A`. Then
`c_A` is virtually unipotent, or its characteristic polynomial is irreducible
and totally real.

*Proof.* In the proof of E3, `L^+/A ≅ C_{L^+}(c_A)/C_A(c_A)` (Section 3), and
`L^+/A` is infinite: it has finite index in `L/A`, which maps onto `K_A/N`, of
finite index in the infinite group `K/N`. `C_A(c_A)` is infinite cyclic, since
centralizers of nontrivial elements of free groups are cyclic. So
`h(C(c_A)) >= h(C_{L^+}(c_A)) >= 2`, and the Remark after Lemma H finishes. ∎

In particular, the commutator of a basis of the fibre of any `F_2 x| Z` inside
`SL_3(Z)` has these properties. That rules out complex cubic fields, and
reducible `χ = (x ∓ 1) q(x)`, for the peripheral element. Section 5 checks
this against Long–Reid.

**Corollary E5 (bounded surfaces).** Let `N ≅ π_1(S)` for a compact surface `S`
with `b >= 1` boundary components and `χ(S) < 0`, so `N` is free of rank
`1 - χ(S) >= 2`. Suppose conjugation by `K` permutes the `N`-classes of the
boundary loops and their inverses, as it does when the monodromy is induced by
homeomorphisms of `S`. Then `K/N` is virtually cyclic, and `K` is virtually
`F_n` or `F_n x| Z` and coherent.

*Proof.* A boundary loop has infinite order, and its orbit has at most `2b`
classes. Apply E1 and E2. ∎

This improves the peer lane's Corollary A4 from "virtually polycyclic" to
"virtually cyclic, hence coherent".

**Remark E6 (reduction for free-by-free candidates).** Let `N ≅ F_n` with
`n >= 2` and `K/N` not virtually cyclic.

*Claim.* There is a free factor `A` of `N`, of rank `r >= 3`, such that:

- `A ◁ L := N_K(A)`, and `L/A ≅ K_A/N` has finite index in `K/N`;
- `L` virtually fixes no `A`-conjugacy class of a proper nontrivial free factor
  of `A`.

*Proof.* Choose a free factor `A` of minimal rank among those whose `N`-class
has finite `K`-orbit. `A = N` qualifies, so the choice is possible.

- A nontrivial free factor of a free group is malnormal, so `N_N(A) = A` and
  `K_A/N ≅ L/A`.
- `r = 1` contradicts E1, and `r = 2` contradicts E3.
- Suppose a finite-index `L' <= L` fixes the `A`-class of a proper free factor
  `B` of `A`. Then `B` is a free factor of `N`. `N L'` fixes `[B]_N` and has
  finite index in `N L = K_A`, hence in `K`. So `B` has a finite orbit and
  smaller rank, contradicting minimality. ∎

The map `L/A -> Out(A)` has finite kernel `C_L(A) A/A`, by (G4). Recalled and
not re-read: by the Handel–Mosher subgroup alternative (arXiv:0908.1255,
finitely generated case) and Horbez's extension (arXiv:1404.4626), a subgroup
of `Out(F_r)` that virtually fixes no conjugacy class of a proper free factor
contains a fully irreducible element. So a free-by-free witness in `SL_3(Z)`
would contain a free-by-(not virtually cyclic) subgroup of fibre rank at least
3 whose monodromy contains fully irreducible elements. This remark is not
entered in the graph.

**Remark E7 (closed surface fibres; recalled inputs only).** Let `N ≅ π_1(Σ)`
be closed with `χ(Σ) < 0`, and `K/N` not virtually cyclic. By E1 no
infinite-order class has a finite orbit. In particular no simple closed curve
class does, so the image of `K` in `Out(N) ≅ Mod^±(Σ)` virtually fixes no
multicurve. The kernel `C_K(N)` is finite by (G4).

If Ivanov's classification of subgroups of mapping class groups holds as
recalled (irreducible subgroups are virtually cyclic generated by a
pseudo-Anosov, or contain two independent pseudo-Anosovs), the monodromy
contains a free group of pseudo-Anosov elements. Not entered in the graph.

## 5. Long–Reid cross-check

**Source.** D. D. Long and A. W. Reid, *Small subgroups of SL(3,Z)*, preprint
dated August 18, 2010 (published in Experimental Math., 2011; journal details
recalled). The arXiv PDF was read on 2026-09-16.

`Γ = <x, y, z | z x z^-1 = x y, z y z^-1 = y x y>` is the figure-eight knot
group, with fibre `F = <x, y> ≅ F_2`. Their Proposition 2.1 gives integral
representations `ρ_k`, with images `X_k, Y_k, Z_k`. The monodromy fixes
`c = [x, y]`, so `Z_k` commutes with `C_k = ρ_k(c)`.

**Computation.** Script:
`experiments/sl3z-normal-free-rank-two-2026-09-16/long_reid_peripheral_torus.py`,
output in the adjacent `.out` file. The matrices were transcribed from the PDF
layout. For every `k in [-12, 12]` the script checks exactly that:

- `det = 1`, and both relations hold;
- `χ(C_k) = p_k`, their Lemma 2.4 polynomial, which is irreducible for all
  these `k`;
- `Z_k in Q[C_k]`.

The discriminant is
`disc p_k = (2k+1)^2 (5k^2+5k-19)^2 (k^4+2k^3-5k^2-6k-23)`.

- **`k in {-3, ..., 2}`: `disc < 0`, complex cubic field.** The exact relations
  found are:

  | `k` | relation |
  |---|---|
  | 2 | `Z^3 = C` |
  | 1 | `Z^4 = C` |
  | 0 | `Z^10 = C` |
  | -1 | `Z^10 = C^-1` |
  | -2 | `Z^4 = C^-1` |
  | -3 | `Z^3 = C^-1` |

- **`k >= 3` or `k <= -4`: totally real field.** The `2 x 2` log-embedding
  determinant of `(C_k, Z_k)`, computed to 60 digits, is far from 0 (for
  example `|det| ≈ 4.2036` at `k = 3` and `≈ 25.335` at `k = 12`). So `Z_k` and
  `C_k` are multiplicatively independent there. This is numerical, not a
  certificate. The data are symmetric under `k <-> -1-k`.

**Comparison with Corollary E4.**

- For `k in {-3, ..., 2}`, `C_k` is regular semisimple over a complex cubic
  field, so `h(C(C_k)) = 1` by Lemma H(a). Corollary E4 then forbids `ρ_k(F)`
  from being a normal `F_2` with infinite quotient. Indeed the exact relations
  give a nontrivial kernel element `z^m c^{-n}`, which maps to `m != 0` in
  `Γ/F`. This is the argument of Long–Reid §4.2 for `k = 0, 1, 2`: Dirichlet's
  theorem when `χ(Z_k)` has one real root. So it is consistent with them, not
  new.
- **A discrepancy.** The PDF text extraction of §4.2 reads
  "`Z_1^10 = [X_1, Y_1]` and `Z_0^3 = [X_0, Y_0]`, `Z_2^4 = [X_2, Y_2]`".
  The exact computation above gives `Z_0^10 = C_0`, `Z_1^4 = C_1` and
  `Z_2^3 = C_2`. The printed exponents appear permuted among `k = 0, 1, 2`.
  Whether this is a typo in the preprint or an extraction artifact was not
  resolved.
- For `|k|` large the peripheral subgroup `<Z_k, C_k>` is a rank-2 subgroup of
  a split torus, as E4 requires of any faithful case. So E4 gives no
  obstruction there.
- E4 is not a thinness test. Long–Reid's Theorem 4.1 gives finite index of
  `ρ_k(Γ)` for `k = 0, 2, 3, 4, 5`, and the peripheral rank is 2 at
  `k = 3, 4, 5` too.

**Related text in the same preprint.**

- The proof of their Theorem 6.1 already sketches the semisimple part of
  Lemma H: "the centralizer of γ is (virtually) Z ⊕ Z or (virtually) Z by
  Dirichlet's Unit Theorem".
- Their Proposition 5.2 derives incoherence of `SL(3,Z)` from a non-free
  `ρ_k(F)` of infinite index in `ρ_k(Γ)` with vcd 2 (Bieri).
- Their Question 3 asks whether some `ρ_k` is faithful. By their remark,
  faithfulness is equivalent to faithfulness on `F`.

No novelty is claimed for Lemma H(a)–(b). The transvection case (d) and its
use through (G2) and (G3) are what Theorem E needs beyond Long–Reid.

## 6. Literature and status

TODO

## 7. Where it stops

TODO
