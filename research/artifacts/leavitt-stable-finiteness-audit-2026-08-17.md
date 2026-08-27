# 2026-08-17 — Stable finiteness of `F_2[L_(F_2)(1,2)^x]` (ingestion audit)

Source: a user-supplied external attempt, "Stable finiteness of
`F_2[L_{F_2}(1,2)^x]`: attempted resolution, new reductions, and exact finite
certificates", dated 2026-08-17, unrefereed, written against an upload of this
repository.  Delivered as `leavitt_stable_finiteness_new_work_2026-08-17.zip`
with a standalone exact verifier.  This file records the ingestion audit and
carries the proofs the new graph nodes cite; the canonical statements live in
the graph.

**Verdict, which this audit confirms.**  The question the source was set — is
`S = F_2[R^x]` stably finite, `R = L_(F_2)(1,2)` — is **not** resolved, and the
source says so in its own Section 0 rather than presenting quotient-level
evidence as a solution.  No pair `(A, B)` with `BA = I != AB` is exhibited at
any size, and no new bounded search was run.

What it does obtain is four things this graph did not have, three of which
change the frontier:

1. **Stable finiteness and direct finiteness are equivalent for this
   particular `S`.**  Matrix size is not an independent search dimension.
2. **`ker(pi_e) != 0`** — the computation the two 2026-08-17 audits both named
   as the next real piece of work — and in the strong form that it contains a
   nonzero **idempotent** of augmentation zero.  So
   `leavitt-corner-kernel-is-jacobson-radical` is **false**, not open.
3. **`pi : S ->> R` has no left `S`-module section**, because `S` is prime.  So
   `leavitt-evaluation-splits-as-module-map` is **false**, not open.
4. `K = ker(pi)` contains infinitely many pairwise orthogonal nonzero
   idempotents, all but one of augmentation zero.

Two of the four open sufficient conditions in the Kaplansky/Gottschalk lane
are therefore removed, and the two lanes that survive are the two that ask for
an explicit lift.

Every computation below was re-derived during ingestion.  Where this audit
differs from the source it is marked.

## What the audit changes about the source

1. **`G ~= EL_9(R)` is not the identification this repository owns, and the
   smaller one is what the theorem needs.**  The source writes "the prompt
   gives `G ~= EL_9(R)`".  What is established here is
   `leavitt-gl-equals-el-and-perfect-unit-group`: the three-leaf prefix code
   identifies `R^x` with `GL_3(R) = EL_3(R)`.  Three indices is exactly the
   hypothesis `elementaryGroup_finite_quotient_trivial` requires
   (`3 <= Fintype.card ι`), so the smaller identification is enough and the
   discrepancy is immaterial — but the nodes cite the repository's own rank.
2. **The primality argument does not need the source's route through
   `Aut(N)` alone; it needs one more step, and that step is free here.**  The
   source deduces `N <= Z(G) = 1` from triviality of `G -> Aut(N)`.  Correct.
   Worth recording alongside it: no-finite-quotients gives the stronger
   statement that **`G` has no proper subgroup of finite index at all** (a
   subgroup of index `n` gives `G -> S_n`, which is trivial, so the subgroup
   is everything).  Hence every finite conjugacy class of `G` is a singleton,
   `Delta(G) = Z(G)`, and `Z(F_2[G]) = F_2[Z(G)]`.  This is what makes the
   Connell import a formality rather than a load-bearing black box, and it is
   also what would be needed if one wanted to avoid Connell entirely.
3. **The `M_2(S)` amplification is cleaner by induction than by tensor
   powers.**  The source builds `M_N(S) -> S` for `N = 2^k` from a
   tensor-power representation `rho_k : H^k -> GL_N(F_2)` and a length-`k`
   prefix code.  Correct, but the `k = 1` statement already implies the rest:
   if `j : M_2(S) -> S` is an injective ring map with `j(I_2)` idempotent,
   then `j . M_2(j) : M_4(S) = M_2(M_2(S)) -> S` is another one, and induction
   gives every `2^k`.  Only the single finite `S_3` certificate is then
   needed.  The nodes state it that way; the source's version is equivalent.
4. **The center input is a literature import and is marked as such.**  The
   source states `Z(R) = F_2` "by the standard center theorem for prime
   Leavitt path algebras" and cites arXiv:1209.4375.  This repository does not
   have it: `LeavittNormalForm.lean` proves the monomials **span**, and no
   linear independence or center theorem is formalized.  It is therefore split
   off into its own citation node, `leavitt-center-is-coefficient-field`, and
   the primality chain depends on it visibly.  Section C records what is
   internal (everything else) and what is not.
5. **Certificate replay was attempted, and passed.**  Contrary to the
   standing practice on the two 2026-08-17 Leavitt audits, the exact verifier
   supplied with this source was run — on MSI, per the no-local-execution
   rule — and reproduced the delivered output line for line, including the
   twelve-element support table.  Its script is checked in beside this file as
   `research/artifacts/verify-s3-corner-2026-08-17.py`.
6. **No source-access failure was repaired.**  The source could not retrieve
   Liu's Zenodo record (HTTP 429) and so extracted no search bound and ran no
   search.  This session did not retrieve it either.  Nothing in the new nodes
   depends on it, and the repository's existing record of that gap stands
   unchanged.

---

## A. The finite `S_3` packet, and why it is the repository's own packet

`leavitt-corner-idempotent-unital-surjection` already owns

    x = s_0 t_1,   y = s_1 t_0,   u = 1 + x,   v = 1 + y,   g = u v,

with `u^2 = v^2 = 1` and `g` of order exactly three, and builds the idempotent
`e = [g] + [g^2]` of `S = F_2[G]` with `pi(e) = 1_R` and `eps(e) = 0`.

What that node does not say, and what everything below turns on, is **where
those units come from**.  Let

    Theta_2 : M_2(R) -> R,     Theta_2((a_ij)) = sum_ij s_i a_ij t_j

be the binary self-similarity isomorphism (`LeavittFamily.binaryMatrixRingEquiv`
in `LeavittSelfSimilarity.lean`), with inverse `Phi(r)_ij = t_i r s_j`.  Then

    u = Theta_2 [[1,1],[0,1]],   v = Theta_2 [[1,0],[1,1]],
    w = x + y = Theta_2 [[0,1],[1,0]],   g = Theta_2 [[0,1],[1,1]],

so `H = <u, v>` is precisely the image under `Theta_2` of the **constant**
matrices `GL_2(F_2) ~= S_3`, and `p_0 = xy = s_0t_0`, `p_1 = yx = s_1t_1`
are `Theta_2(E_11)`, `Theta_2(E_22)`.  Distinctness of the six is the
extraction `Phi(r)_ij = t_i r s_j`.

That identification is the whole content of Section B, because constant
matrices commute with scalar matrices.

### A.1 `e F_2[H] e ~= M_2(F_2)`

Inside the **finite group algebra** `F_2[H]` (six group elements, no Leavitt
relation used anywhere in this computation) put

    f_11 = [1]+[u]+[v]+[g],      f_12 = [v]+[w]+[g]+[g^2],
    f_21 = [u]+[w]+[g]+[g^2],    f_22 = [1]+[u]+[v]+[g^2].

Then `f_ij f_kl = delta_jk f_il` for all sixteen pairs, `f_11 + f_22 = e`,
every `f_ij` has augmentation zero, and

    pi(f_11) = p_0,  pi(f_12) = x,  pi(f_21) = y,  pi(f_22) = p_1.

Moreover `e F_2[H] e` has exactly sixteen elements and is the `F_2`-span of the
four `f_ij`, so it **is** `M_2(F_2)`.  The complementary idempotent
`z = 1 + e = [1] + [g] + [g^2]` satisfies `z^2 = z`, `ez = ze = 0`,
`pi(z) = 1 + g + g^2 = 0` and `eps(z) = 1`.

Structurally: `F_2[C_3] = F_2 x F_4`, `e` is the idempotent cutting out the
`F_4` factor, and `e F_2[S_3] e` is the crossed product of `F_4` by its Galois
group — a split four-dimensional central simple `F_2`-algebra.  The
sixteen-element enumeration is a certificate for the same fact.

**Replayed.**  `research/artifacts/verify-s3-corner-2026-08-17.py`, exact over
`F_2`, group elements as literal `2x2` binary matrices and group-algebra
elements as bitsets.  Run on MSI 2026-08-17: all nine assertions pass.  It
checks the six-element multiplication table, the involutions and `g^3 = 1`,
complementarity of `e` and `z`, all sixteen matrix-unit products, the four
evaluations, the sixteen-element count, and — in `F_2[S_3 x S_3]` — the
twelve-term idempotent of Section D.

**One negative fact from the same run, which explains a year of difficulty in
this lane.**  The repository's kernel witness `k = [u] + [v] + [w]` from
`leavitt-evaluation-kernel-hits-augmentation-one` satisfies

    e k = k e = 0.

So the one explicit kernel element the graph owned is **invisible** in the
corner.  That is why `ker(pi_e) != 0` was not obtainable by restricting the
element already in hand, and it is worth stating in that node.

---

## B. `e S e` contains `M_2(S)`, hence `M_(2^k)(S)`

For `q` in `G` define the scalar self-similarity unit

    delta(q) = Theta_2(q I_2) = s_0 q t_0 + s_1 q t_1,

which is `LeavittFamily.crossUnit` in `LeavittDiagonalClass.lean`, with
explicit inverse `delta(q)^-1 = s_0 q^-1 t_0 + s_1 q^-1 t_1`.  Since `Theta_2`
is a ring isomorphism, `delta : G -> G` is an injective group homomorphism.

**`delta(G)` centralizes `H`.**  Scalar matrices commute with constant
matrices in `M_2(R)`; apply `Theta_2`.

**`delta(G) n H = 1`.**  If `q I_2 = C` with `C` constant invertible, the
off-diagonal entries of `C` vanish and both diagonal entries equal `q`, so
`C = lambda I_2` with `lambda in F_2^x = {1}`.

Hence `delta(G) x H` embeds in `G`, and on group algebras

    S (x)_(F_2) F_2[H] ~= F_2[delta(G) x H]  ->  S    injectively.

Cutting by `e`, which lies in the second factor and therefore commutes with
the image of `S`,

    M_2(S) ~= S (x) M_2(F_2) ~= S (x) e F_2[H] e  ->  e S e,

an injective (nonunital) ring map `j : M_2(S) -> S` with `j(I_2) = e`.

**Induction to every `2^k`.**  If `j : M_2(S) -> S` is injective with
`j(I_2)` idempotent, then `M_2(j) : M_4(S) = M_2(M_2(S)) -> M_2(S)` is
injective and sends `I_4` to the idempotent `j(I_2) I_2`, so `j . M_2(j)` is
an injective ring map `M_4(S) -> S` carrying `I_4` to an idempotent.  Iterate:
for every `k` there is an injective ring map

    j_N : M_N(S) -> S,     N = 2^k,     j_N(I_N) = E_N,   E_N^2 = E_N.

The source instead builds `j_N` in one step from `H^k -> GL_N(F_2)` and a
length-`k` prefix code; the two agree and the induction needs only the single
finite certificate of Section A.1.

---

## C. `S` is prime

Three inputs, of which exactly one is external.

**C.1 (internal, formalized) `G` has no nontrivial finite quotient.**
`elementaryGroup_finite_quotient_trivial` in
`GroupApproximation/Leavitt/ElementaryNoFiniteQuotients.lean`: for a ring that
is `Infinite` and in which every nonzero element divides `1` on both sides,
and at least three matrix indices, every homomorphism from the elementary
group to a finite group is trivial.  Both ring hypotheses are formalized here
(`LeavittFamily.infinite`; `BinaryLeavitt.exists_mul_mul_eq_one` in
`LeavittSimplicity.lean`), and `G ~= GL_3(R) = EL_3(R)` is
`leavitt-gl-equals-el-and-perfect-unit-group`.

Consequence used below: `G` has **no proper subgroup of finite index**, since
the action on the cosets of one of index `n` would be a nontrivial
homomorphism to `S_n`.

**C.2 (internal, formalized) `Z(G) = Z(R)^x`, and `Z(R)` is a field.**
If `c` is central in `G` it commutes with every unit of `R`, hence — by the
unit-span theorem `unitAdditiveSpan_eq_top` in `UnitAdditiveSpan.lean`, which
is what `leavitt-unit-group-algebra-surjects-onto-leavitt` consumes — with
every element of `R`.  So `Z(G) = Z(R) n R^x`.  Conversely `Z(R)\{0}` consists
of units: strong two-sided division gives `a c b = 1` for `c != 0`, and `c`
central turns this into `c(ab) = (ab)c = 1`.  So `Z(R)` is a field and
`Z(G) = Z(R)\{0}`.

**C.3 (external) `Z(R) = F_2`.**  Corrales García--Martín Barquero--Martín
González--Siles Molina--Solanilla Hernández, arXiv:1209.4375, center theorem
for prime Leavitt path algebras, applied to the one-vertex two-loop graph
(finite, Condition (L)).  Not formalized here and not re-derived here; carried
as `leavitt-center-is-coefficient-field`.  With it, `Z(G) = 1`.

**C.4 No nontrivial finite normal subgroup.**  Let `N` be a finite normal
subgroup.  Conjugation gives `G -> Aut(N)` with finite target, trivial by C.1,
so `N <= Z(G) = 1`.

**C.5 (external) Primality.**  Connell, *On the Group Ring*, Canad. J. Math.
15 (1963), 650--685, Theorem 8: `A[G]` is prime iff `A` is prime and `G` has
no nontrivial finite normal subgroup.  With `A = F_2` and C.4, **`S` is
prime**.  Carried as `connell-group-ring-primality`.

By C.1 and C.2 the finite conjugacy classes of `G` are exactly the singletons
of `Z(G)`, so `Delta(G) = Z(G) = 1` and `Z(S) = F_2`; the Delta-method form of
Connell's criterion (`K[G]` prime when `Delta(G) = 1`) is the only part of it
actually consumed.

---

## D. The primitive corner, the recursive embedding, and the kernel idempotent

Put `f = f_11 = [1]+[u]+[v]+[g]`, so `f^2 = f`, `f <= e` (from
`f_11 f_11 = f_11` and `f_11 + f_22 = e`), `eps(f) = 0` and `pi(f) = p_0`.
Write `T = f S f`, a unital ring with identity `f`, and

    rho : T -> R,      rho(a) = t_0 pi(a) s_0.

**`rho` is a surjective unital ring homomorphism.**  For `a in T`,
`pi(a) = p_0 pi(a) p_0`, so
`rho(a)rho(b) = t_0 pi(a) s_0 t_0 pi(b) s_0 = t_0 pi(a) p_0 pi(b) s_0 = rho(ab)`,
and `rho(f) = t_0 p_0 s_0 = (t_0 s_0)(t_0 s_0) = 1`.  For surjectivity, given
`r in R` the matrix `U_r = [[r,1],[1,0]]` has inverse `[[0,1],[1,r]]` in
characteristic two, so `h_r = Theta_2(U_r) in G` and
`rho(f [h_r] f) = t_0 p_0 h_r p_0 s_0 = r`.

**The recursive embedding.**  Let `delta_* : S -> S` be induced by
`delta : G -> G`.  Its image commutes with `f`, so

    lambda : S -> T,      lambda(a) = delta_*(a) f

is a ring homomorphism with `lambda(1) = f`.  It is injective: inside
`F_2[delta(G) x H] ~= S (x) F_2[H]` it is `a |-> a (x) f`, and tensoring with a
nonzero vector over a field is injective.  On a basis element,
`pi(lambda([q])) = delta(q) p_0 = s_0 q t_0`, hence

    rho(lambda([q])) = t_0 s_0 q t_0 s_0 = q,     so   rho . lambda = pi.

So the extension `S ->> R` reappears verbatim inside the primitive corner
extension `T ->> R`, and `lambda(K) <= ker(rho) = f K f`.

**The kernel idempotent.**  With `z = [1]+[g]+[g^2] in K`, `z^2 = z`, set

    q = lambda(z) = delta_*(z) f.

Then `q^2 = q`, `q != 0`, `q in f K f <= ker(pi|_(eSe))`, and
`eps(q) = eps(z) eps(f) = 1 . 0 = 0`.  Expanded, `q` is the twelve-term element

    q = sum over a in {1, g, g^2}, h in {1, u, v, g}  of  [delta(a) h],

whose support elements are pairwise distinct with componentwise inverses
`(delta(a)h)^-1 = delta(a^-1) h^-1`.  The `F_2[S_3 x S_3]` half of the
verifier certifies exactly this: twelve distinct terms, idempotent, lying
under the constant primitive corner.

**Consequence.**  The Jacobson radical of a unital ring contains no nonzero
idempotent (if `r^2 = r in J(A)` then `1 - r` is a unit and `r(1-r) = 0`
forces `r = 0`).  So

    ker(pi_e)  is not contained in  J(eSe),

and in particular `ker(pi_e) != J(eSe)`.  This settles, negatively and in the
strongest available form, the question both 2026-08-17 audits named as the
next real piece of work.

**Infinitely many orthogonal kernel idempotents.**  Read `lambda` as an
injective nonunital endomorphism of `S` and set `q_0 = z`, `q_n = lambda^n(z)`.
Each is a nonzero idempotent in `K`; since `f <= e = 1 + z` we have
`z f = f z = 0`, every positive iterate lies in `f S f`, and for `i < j`,
`q_i q_j = lambda^i(z lambda^(j-i)(z)) = 0`, symmetrically on the other side.
Also `eps(q_0) = 1` while `eps(q_n) = 0` for `n >= 1`.

---

## E. Stable finiteness and direct finiteness coincide for this `S`

**Theorem.**  `S` is stably finite iff `S` is directly finite.

`n = 1` gives one direction.  Conversely suppose `B A = I_n != A B` in
`M_n(S)`.  Choose `N = 2^k >= n` and pad with an identity block:
`A' = diag(A, I_(N-n))`, `B' = diag(B, I_(N-n))` still satisfy
`B'A' = I_N != A'B'`.  Apply the injective `j_N` of Section B:

    b a = E_N,      a b != E_N,      a, b in E_N S E_N.

Unitize against the complementary idempotent:

    a^ = a + (1 - E_N),      b^ = b + (1 - E_N).

All cross terms vanish because `a, b` lie in the corner, so
`b^ a^ = ba + (1-E_N) = 1`, while `a^ b^ = ab + (1-E_N) != 1` — the sum
`E_N S E_N (+) (1-E_N)S(1-E_N)` being direct.  So `S` is not directly finite.

**What this does to the graph.**  `leavitt-group-algebra-not-stably-finite`
and `leavitt-unit-group-algebra-not-directly-finite` become equivalent, and
the sentence "Nothing in this graph reduces the matrix problem to the scalar
one" in the former is now false and has been corrected.  Concretely:
Gottschalk for `R^x` and Kaplansky for `F_2[R^x]` are, for this group, the
same problem — the surjunctivity lane can no longer be settled by a witness at
some `n >= 2` that leaves Kaplansky open.

---

## F. What is ruled out, and what the search space now is

**Dead, with proofs above.**

- `leavitt-corner-kernel-is-jacobson-radical` — refuted by the idempotent `q`
  of Section D.  With it dies the route
  `leavitt-unit-algebra-not-directly-finite-by-radical-kernel`.
- `leavitt-evaluation-splits-as-module-map` — refuted by primality.  If
  `sigma : R -> S` were left `S`-linear with `pi sigma = id` and
  `p = sigma(1)`, then `p != 0`, `p^2 = sigma(pi(p)) = p`, and for every
  `k in K`, `kp = sigma(pi(k)) = 0`; as `K` is two-sided this gives
  `K (S p S) = (K S) p S = K p S = 0` with both ideals nonzero, contradicting
  Section C.  With it dies the route
  `leavitt-direct-finiteness-failure-from-module-splitting`, and `R` is not
  projective as a left `S`-module.

**Alive, unchanged.**  `leavitt-corner-one-sided-lift-exists` and
`left-invertible-lift-of-s0-in-leavitt-group-algebra` — the two lanes that ask
for an explicit element.  Both still terminate at the same finite-support
kernel-lifting equation

    (B_0 A_0 - I) + B_0 alpha + beta A_0 + beta alpha = 0,      alpha, beta in K,

and the source did not solve it.

**Why the new idempotents do not finish it, which the source states and this
audit confirms.**  `rho lambda = pi` invites a recursive correction
`error_0 -> lambda(error_0) -> lambda^2(error_0) -> ...`; telescoping through
depth `m` cancels the first `m` errors and leaves a tail proportional to
`lambda^m(error_0)`, which is nonzero for every `m` because `lambda` is
injective.  Group-algebra elements have finite support, so there is no
infinite sum to absorb the tail.  This is a genuine Eilenberg-swindle failure,
not an unfinished computation.

The source also names three tempting shortcuts.  Two are correctly rejected,
while the first is now the exact open target: a Murray--von Neumann equivalence
`e~f` from the whole order-three corner to its primitive subcorner would give
the desired failure.  Augmentation blocks equivalence of either augmentation-
zero idempotent with `1`, but does not block `e~f`.  No such equivalence or
obstruction is known.  A nonzero kernel idempotent is not by itself a defect
`1 - ab`, since `ba = 1` constrains that defect associatively; and a nonunital
corner self-embedding does not imply direct infiniteness (directly finite
non-Noetherian rings can have proper corner self-embeddings and infinitely
many orthogonal idempotents).

**Search pruning now available.**

1. Rank one suffices — Section E.
2. Both supports are odd: `ba = 1` gives `eps(a) eps(b) = 1`, so
   `eps(a) = eps(b) = 1`.
3. For the specific explicit support-three lift of `t_0` already in the graph,
   the partner has support at least thirteen
   (`leavitt-rank-three-lift-inverse-support-thirteen`, from
   Dykema--Heister--Juschenko `(3,n)`, `n <= 11`).  This is a bound for that
   lane and must not be confused with Liu's unretrieved bound.
4. Finite quotients supply nothing: every homomorphism `G -> Q` with `Q`
   finite is trivial (C.1), so finite linear shadows of `S` reduce to the
   augmentation.
5. The correction ideal is not radical noise — model it with Peirce and
   corner structure, not with nilpotents (Section D).

**Not attempted, here or by the source.**  No machine search at any support
size; no presentation of `e S e`; Liu's Zenodo record still unretrieved and
its bound still unknown to this repository.

---

## G. Graph nodes carrying this material

New, established:
`leavitt-matrix-amplification-in-unit-group-algebra`,
`leavitt-stable-finiteness-equals-direct-finiteness`,
`leavitt-primitive-corner-recursive-extension`,
`leavitt-corner-kernel-not-jacobson-radical`,
`leavitt-recursive-kernel-idempotents`,
`leavitt-unit-group-has-no-finite-normal-subgroup`,
`leavitt-unit-group-algebra-is-prime`,
`leavitt-evaluation-does-not-split-as-module-map`.

New, imported (trust surface): `leavitt-center-is-coefficient-field`,
`connell-group-ring-primality`.

New route: `leavitt-direct-finiteness-failure-from-matrix-failure`, the
converse half of the equivalence, which makes
`leavitt-group-algebra-not-stably-finite` and
`leavitt-unit-group-algebra-not-directly-finite` interderivable.

Invalidated: `leavitt-unit-algebra-not-directly-finite-by-radical-kernel`,
`leavitt-direct-finiteness-failure-from-module-splitting`.

Corrected in place: `leavitt-group-algebra-not-stably-finite` (the
no-reduction sentence), `leavitt-corner-kernel-is-jacobson-radical` and
`leavitt-evaluation-splits-as-module-map` (both now refuted),
`leavitt-corner-one-sided-lift-exists` and
`leavitt-unit-group-algebra-not-directly-finite` (both said deciding
`ker(pi_e) != 0` was the first concrete piece of work; it is now done).

Unchanged and still the whole problem: `leavitt-corner-one-sided-lift-exists`,
`left-invertible-lift-of-s0-in-leavitt-group-algebra`,
`leavitt-unit-group-algebra-not-directly-finite`,
`leavitt-group-algebra-not-stably-finite`,
`leavitt-unit-group-nonsurjunctive`.

## G.1 Program placement

Three connections outside the Kaplansky/Gottschalk lane, recorded because the
graph grew a great deal on the same day and this material touches parts of it.

**The formalized no-finite-quotients theorem finally has a claim.**  Before
this ingestion, no node in `research/` cited
`ElementaryNoFiniteQuotients.lean`, though two lanes lean on what it proves.
`leavitt-unit-group-has-no-finite-normal-subgroup` is now its home, and it
records the scope: the theorem covers `EL_iota(L)` for at least three
indices, hence `L^x ~= EL_3(L)` here and `Q = EL_4(L)` in the atlas lane, but
not `U = St_5(L)` directly, because a finite quotient of the Steinberg cover
need not kill `K_2(5, L)`.  It comes within one step of covering `U` as
well — a finite quotient of `St_5` is central modulo a finite quotient of
`EL_5`, hence abelian, hence trivial if `St_5` is perfect — which would give
`leavitt-steinberg-hs-stable` a second derivation of its finite-index step,
independent of minimal almost periodicity.  Perfectness of the Steinberg
cover is not formalized here, so that is left as an observation for the atlas
lane rather than wired as a route.

**The Boone--Higman ring lane wants this exact ring, and nothing here helps
it.**  `boone-higman-via-universal-leavitt-host` cites the same Lean files
because `L_K(1,2)` is a finitely presented strongly simple ring with
well-behaved elementary groups — precisely a Boone--Higman envelope's wish
list.  That route is already dead at
`weyl-algebra-blocks-a-universal-leavitt-host`.  The center computation
imported here says `L_K(1,2)` is *central* simple over `K`, which looks like
it should bear on which `K`-algebras embed, and does not: a unital embedding
`A -> L_K(1,2)` puts no constraint on `Z(A)`, because a central element of
`A` need only centralize the image of `A`.  Recorded as a dead end so nobody
re-derives it.

**Nothing here is wired toward `q3-4-resolved`, deliberately.**  The scope
note on `leavitt-unit-group-algebra-not-directly-finite` keeps the Kaplansky
lane out of the goal's route structure, because the implication connecting
approximation properties to direct finiteness runs from soficity and `R^x` is
announced nonsofic.  The new equivalence
`leavitt-stable-finiteness-equals-direct-finiteness` ties Kaplansky to
Gottschalk for this group and to nothing else; it does not create a path to
the goal and no route should be built from it toward one.

**Where this joins the rest of the graph.**  It joins exactly where the two
2026-08-17 Leavitt audits left off.  `research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md`
closed with "computing that kernel — even to the point of deciding whether the
corner's part of it is nonzero — is the next real piece of work"; that is now
done, and the answer kills the radical lane rather than opening it.
`research/artifacts/gottschalk-leavitt-audit-2026-08-17.md` carried the
module-splitting criterion as one of three ways to manufacture a one-sided
inverse; that one is now closed too.  What survives is the intersection the
two audits already identified — one solution of
`(a + alpha)(b + beta) = 1` with `alpha, beta` in a kernel that is now known
to be large, idempotent-rich, and not radical.

## H. References

- Repository, formalized: `GroupApproximation/Leavitt/Leavitt.lean`
  (binary Leavitt relations, `LeavittFamily.infinite`);
  `LeavittSelfSimilarity.lean` (`binaryMatrixRingEquiv`);
  `LeavittDiagonalClass.lean` (`crossUnit`);
  `LeavittSimplicity.lean` (`exists_mul_mul_eq_one`);
  `UnitAdditiveSpan.lean` (`unitAdditiveSpan_eq_top`);
  `ElementaryNoFiniteQuotients.lean` (`elementaryGroup_finite_quotient_trivial`);
  `KOne/AllRanksElementary.lean` (`glAll_eq_elementary`, three-leaf
  identification of `R^x`).
- K. Dykema, T. Heister, K. Juschenko, *Finitely presented groups related to
  Kaplansky's direct finiteness conjecture*, Experimental Math. 24 (2015),
  326--338; arXiv:1112.1790.  Already imported here as
  `dykema-heister-juschenko-bounded-rank-direct-finiteness`.
- I. G. Connell, *On the Group Ring*, Canad. J. Math. 15 (1963), 650--685,
  Theorem 8.
- M. G. Corrales García, D. Martín Barquero, C. Martín González, M. Siles
  Molina, J. F. Solanilla Hernández, *Centers of path algebras, Cohn and
  Leavitt path algebras*, arXiv:1209.4375.
- Liu, *Kaplansky's Direct Finiteness Conjecture for the First Non-Sofic
  Group*, Zenodo record 21840947, DOI 10.5281/zenodo.21840947 (2026).  Located
  by the source, not retrieved (HTTP 429), bound still unknown here.
