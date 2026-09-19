# 2026-08-17 — Kaplansky direct finiteness via the Leavitt unit group (ingestion audit)

Source: a user-supplied external resolution attempt, "Kaplansky's
Direct-Finiteness Conjecture — Exact audit of the Leavitt-unit route, with a
sharp corner-lifting reduction", dated 2026-08-17, unrefereed, written
against an upload of this repository.  This file records the ingestion audit
and carries the proofs the new graph nodes cite; the canonical statements
live in the graph.

**Verdict, which this audit confirms.**  No proof or counterexample to
Kaplansky's Direct Finiteness Conjecture is obtained, and the source says so
itself in its own headline.  What it does obtain is a chain of exact,
checkable reductions that moves this repository's Leavitt-unit material from
"suggestive" to "one named lifting problem", plus a bounded-support
obstruction that rules out the smallest completion of that lift.  It also
states, correctly and prominently, the quotient-permanence gap that any
claimed disproof from the bare surjection `F_2[R^x] -> R` would contain.

Every computation below was re-derived line by line during ingestion.  Where
this audit differs from the source it is marked.

## What the audit changes about the source

1. **The augmentation is what forces the corner, and the source does not say
   so.**  This repository already owns `augmentation-blocks-unital-leavitt-family`:
   a unital ring homomorphism to `Z` forbids a binary Leavitt family.  The
   two-line scalar half of that proof uses only that the target is a
   *domain*, so it applies verbatim to the `F_2`-augmentation
   `eps : F_2[G] -> F_2`.  Consequence: **`F_2[G]` itself contains no unital
   binary Leavitt family, for any group `G` whatsoever.**  So a lift of the
   Leavitt relations into `F_2[R^x]` is impossible on the nose, and any
   idempotent `f` whose corner `f A f` could carry one must satisfy
   `eps(f) = 0` — otherwise `eps` restricts to a unital map `fAf -> F_2` and
   the same two lines fire.  The source's idempotent passes this test
   exactly: `eps(e) = eps([g]) + eps([g^2]) = 1 + 1 = 0`.  The corner is
   therefore not one convenient choice among many; vanishing augmentation is
   a *necessary* feature of any corner where the lifting problem is not
   already dead, and the constructed one has it.  See Section B.
2. **The radical criterion is an equality, not a containment.**  The source's
   sufficient condition `ker(pi_e) subseteq J(eAe)` is equivalent to
   `ker(pi_e) = J(eAe)`, because the reverse containment is automatic:
   `L_(F_2)(1,2)` is simple (`LeavittSimplicity.exists_mul_mul_eq_one`,
   kernel-checked here), a unital simple ring has zero Jacobson radical, and
   a surjective ring homomorphism carries `J` into `J`.  Stating it as an
   equality is what makes it legible: it says `R` is exactly the semiprimitive
   quotient of the corner.  See Section E.
3. **The support-13 bound needs one case the source omits.**  Dykema--Heister--
   Juschenko's rank pairs are defined for `m, n >= 2` (their Definition 2.12),
   so `|supp B| = 1` is not covered by the imported result.  It is excluded in
   one line instead: `B = [h]` forces `t~ = [h^-1]`, of support 1, not 3.  With
   that patch the bound stands.  See Section D.
4. **A distinctness argument in the source's Section 7 is longer than needed.**
   For `U_2 = [[t_0+1, 1],[1, 0]]` against `U_3 = [[0,1],[1,1]]` the `(2,2)`
   entries are already `0` and `1`; no appeal to `t_0 != 1` is required.  The
   source's conclusion is unaffected.
5. **Certificate replay was not attempted here either.**  The source reports
   SHA-256 digests for the two atlas JSON files and says the replay did not
   finish in its window.  This session did not run it (standing no-local-
   execution rule).  Nothing in the new nodes depends on those certificates.

## A. The base fact and the unit span

`R = L_(F_2)(1,2) = F_2<s_0,s_1,t_0,t_1 | t_i s_j = delta_ij, s_0t_0+s_1t_1=1>`.

`t_0 s_0 = 1` by definition, and `s_0 t_0 != 1`: if `s_0t_0 = 1` then
`s_1t_1 = 0` in characteristic two, whence
`1 = (t_1s_1)^2 = t_1(s_1t_1)s_1 = 0`.  So `R` is not directly finite.

Units additively span `R`.  This is `unitAdditiveSpan_eq_top` in
`GroupApproximation/Leavitt/UnitAdditiveSpan.lean`, kernel-checked, for every
ring carrying a binary Leavitt family and with no characteristic hypothesis:
`x^2 = 0` makes `1+x` a unit with inverse `1-x`, so `x = (1+x) - 1` is a
difference of units; `xy = (1+x)(1+y) - 1 - x - y` handles products of two
square-zero elements; the off-diagonal corners `s_0 a t_1`, `s_1 a t_0` are
square-zero, the diagonal corners factor as
`s_0 a t_0 = (s_0 a t_1)(s_1 t_0)` and `s_1 a t_1 = (s_1 a t_0)(s_0 t_1)`,
and the four corners of `a = 1 a 1` sum to `a`.

Over `F_2` signs vanish and multiplicities reduce mod 2, so evaluation

    pi : A = F_2[R^x] -> R,   pi([u]) = u

is a **surjective** unital algebra homomorphism.

## B. The corner idempotent, and why its augmentation must vanish

Put `x = s_0t_1`, `y = s_1t_0`.  Then `x^2 = y^2 = 0`, `xy = s_0t_0`,
`yx = s_1t_1`, `xy + yx = 1`.  In characteristic two `u = 1+x` and `v = 1+y`
are involutions, and `g = uv` satisfies

    g + g^-1 = (1+x)(1+y) + (1+y)(1+x) = xy + yx = 1,

so `g^2 + g + 1 = 0`, `g^3 = 1`, and `g != 1` (else `g + g^-1 = 0`).  `g` has
order exactly three in `R^x`.  In `A = F_2[R^x]`,

    e = [g] + [g^2],    e^2 = [g^2] + 2[1] + [g] = e,    pi(e) = g + g^2 = 1.

Hence `pi` restricts to a **unital** surjection `pi_e : eAe ->> R` with
`pi_e(e) = 1_R`: given `r`, pick `pi(a) = r` and note
`pi_e(eae) = pi(e) pi(a) pi(e) = r`.

The complementary idempotent is `1 + e = 1 + [g] + [g^2]`, the other
idempotent of `F_2[<g>] = F_2[C_3]`, and `eps(1+e) = 1`, `eps(e) = 0`.

*Why that zero is the point (this audit's addition).*  Let `f` be any
idempotent of `F_2[G]` with `eps(f) = 1`.  Then `eps` restricts to a unital
ring homomorphism `fAf -> F_2`, and the scalar half of
`augmentation-blocks-leavitt-family-proof` applies with `Z` replaced by the
domain `F_2`: from `t_0s_0 = 1` get `b_0 a_0 = 1` so `a_0 != 0`; from
`t_0s_1 = 0` and `F_2` a domain get `a_1 = 0`; then `t_1s_1 = 1` gives
`b_1 a_1 = 1`, contradiction.  So no unital binary Leavitt family lives in
`fAf`.  Taking `f = 1` shows in particular that **`F_2[G]` contains no unital
binary Leavitt family for any group `G`** — the relations cannot be lifted on
the nose, only into a corner, and only into one of vanishing augmentation.
`e` is such a corner.

### B'. An explicit element of the kernel

Neither the source nor the graph carried a witness for `ker(pi) != 0`, which
`leavitt-evaluation-kernel-hits-augmentation-one` establishes abstractly.  One
falls straight out of the same three elements.  With `x = s_0t_1`, `y = s_1t_0`
put

    u = 1 + x,      v = 1 + y,      w = x + y.

`u` and `v` are involutions as above, and so is `w`, since
`w^2 = x^2 + xy + yx + y^2 = xy + yx = 1`.  They are pairwise distinct: `u = v`
would give `x = y` and hence `s_0t_0 = xy = yx = s_1t_1`, contradicting
`s_0t_0 + s_1t_1 = 1`; `u = w` would give `y = 1`, impossible since `y^2 = 0`;
and `v = w` likewise gives `x = 1`.  In characteristic two

    u + v + w = (1+x) + (1+y) + (x+y) = 0,

so `[u] + [v] + [w]` is a nonzero element of `ker(pi)` of augmentation `1` —
a witness for both parts of that claim at once.  Whether the corner sees it,
that is whether `e([u]+[v]+[w])e != 0`, is not computed here, and deciding
`ker(pi_e) != 0` is the cheapest open piece of work in the whole lane.

## C. The gap, stated as the source states it

Direct finiteness does not pass to quotients, so neither
`A ->> R` nor `pi_e : eAe ->> R` makes `A` non-directly finite.  The
witness is elementary and complete: `k<X,Y>` is a domain (leading words
concatenate), every domain is directly finite (`ab = 1` gives
`(ba-1)b = b(ab) - b = 0` with `b != 0`), and
`B = k<X,Y>/(XY-1)` is not — on `V` with basis `v_0, v_1, ...` set
`Y v_n = v_(n+1)`, `X v_0 = 0`, `X v_(n+1) = v_n`, so `XY = 1` while
`YXv_0 = 0`.  A defining relation `XY = 1` never forces `YX = 1`.

## D. The rank-three lift and the support-13 floor

Self-similarity.  With `S = [s_0 s_1]` and `T = [t_0; t_1]`, `ST = 1` and
`TS = I_2`, so `Psi(M) = SMT` and `Phi(r) = TrS = (t_i r s_j)` are mutually
inverse ring isomorphisms `M_2(R) <-> R`.  Associativity alone gives

    Phi(t_0) = [[t_0, 0],[t_1, 0]],    Phi(s_0) = [[s_0, s_1],[0, 0]],

since `t_i(t_0 s_j) = t_i delta_0j` and `(t_i s_0)s_j`.  Over a ring of
characteristic two every `2x2` matrix is a sum of three units:

    [[x,y],[z,w]] = [[1+yz, y],[z, 1]] + [[x+1+yz, 1],[1, 0]] + [[0,1],[1,w+1]],

the first factoring as `[[1,y],[0,1]][[1,0],[z,1]]`, and
`[[d,1],[1,0]]^-1 = [[0,1],[1,d]]`, `[[0,1],[1,c]]^-1 = [[c,1],[1,0]]` (the
cross terms `d+d`, `c+c` vanish).  Specializing,

    Phi(t_0) = [[1,0],[t_1,1]] + [[t_0+1,1],[1,0]] + [[0,1],[1,1]],
    Phi(s_0) = [[1,s_1],[0,1]] + [[s_0+1,1],[1,0]] + [[0,1],[1,1]],

three distinct units in each line (entry `(1,2)`, `(1,1)`, `(2,2)`
respectively separate the three pairs).  Transporting through the injective
`Psi` gives distinct `u_1,u_2,u_3` and `v_1,v_2,v_3` in `R^x` with

    t_0 = u_1+u_2+u_3,    s_0 = v_1+v_2+v_3,

so `t~ = [u_1]+[u_2]+[u_3]` and `s~ = [v_1]+[v_2]+[v_3]` in `F_2[R^x]` have
support exactly three and `pi(t~) = t_0`, `pi(s~) = s_0`.  Note `u_3 = v_3`.
The formal product `t~ s~` need not be `1`; only `pi(t~ s~) = 1` is claimed.

**Support floor.**  If `B` in `F_2[R^x]` satisfies `t~ B = 1` then
`|supp B| >= 13`.  Parity first: `eps(t~) = 1`, so `eps(B) = 1` and the
support is odd.  Support 1 is impossible directly (`B = [h]` forces
`t~ = [h^-1]`, support 1).  For odd `n` with `3 <= n <= 11` the
Dykema--Heister--Juschenko computation gives `B t~ = 1`, so `pi(B)` is a
two-sided inverse of `t_0`; but a two-sided inverse `c` of `t_0` satisfies
`c = c(t_0s_0) = s_0`, forcing `s_0t_0 = 1`, contradiction.  Even `n` is
excluded by parity.  Hence `n >= 13`.

## E. The exact missing theorem

Corner padding.  If `a, b` in `eAe` satisfy `ab = e` and `pi_e(ba) != 1`,
set `alpha = a + (1-e)`, `beta = b + (1-e)`.  Cross terms vanish because
`a = eae`, so `alpha beta = ab + (1-e) = 1` while
`beta alpha = ba + (1-e) != 1` since `ba != e`.  So `A` is not directly
finite, and Kaplansky's conjecture is false.

Three sufficient conditions, in decreasing strength:

* a unital ring section `R -> eAe` of `pi_e`;
* a unital binary Leavitt family `S_i, T_i` in `eAe` lifting `s_i, t_i`
  (then `T_0S_0 = e` and `pi_e(S_0T_0) = s_0t_0 != 1`);
* `ker(pi_e) = J(eAe)`.

The third deserves its sharpened form.  Direct finiteness descends modulo an
ideal inside the radical: if `S` is directly finite, `I subseteq J(S)`, and
`a b = 1` mod `I`, then `ab` lies in `1 + J(S)` hence is a unit, and
`c = b(ab)^-1` has `ac = 1`, so `ca = 1`, and `(ab)^-1` lies in `1 + I`, so
`c = b` mod `I` and `ba = 1` mod `I`.  Under `ker(pi_e) subseteq J(eAe)`,
direct finiteness of `eAe` would therefore force it for `R`, which is false.
The reverse containment `J(eAe) subseteq ker(pi_e)` holds unconditionally —
`R` is simple hence `J(R) = 0`, and `f(J(S)) subseteq J(f(S))` for surjective
`f` — so the hypothesis is exactly `ker(pi_e) = J(eAe)`.

## F. The other repository routes, as audited

*Proper isometries.*  `GroupApproximation/Analysis/ProperIsometryFromCompression.lean`
is correct: for a projection `p` properly absorbed by `upu*`, the element
`s = pu* + (1 - upu*)` has `s*s = 1 != ss*`.  It proves non-direct-finiteness
of the ambient star ring holding the exact projection `p`.  In the intended
construction `p` is a Kazhdan projection obtained by norm functional calculus
and is not shown to lie in a finite-support modular group algebra.  The
repository already records this boundary at
`notes/SIMULTANEOUS_P_AND_OPERATOR_STABILITY_2026-08-13.md` and at
`official/counterexample.tex`.

*Coefficient-level proper infiniteness.*  A group-ring identity must hold in
every representation, the regular one included, and
`notes/FALSE_PROPERLY_INFINITE_CENTRAL_GROUP_CORNER.md` supplies the trace
obstruction for finite central-character corners.  Representation-level
proper infiniteness does not become a universal relation.

*Modular deformation searches.*  `notes/FALSE_ATLAS_UNIVERSAL_MODULAR_FIRST_ORDER_NO_GO.md`
and `notes/FALSE_ATLAS_NATURAL_ALL_FIELD_HIGHER_ORDER_NO_GO.md` close two
natural linearizations in their stated scope.  They do not exclude a lift;
they exclude those mechanisms for producing one.

## G. Source record

Verified from source during this ingestion:

* **Dykema, Heister, Juschenko**, *Finitely presented groups related to
  Kaplansky's direct finiteness conjecture*, Experimental Mathematics 24
  (2015) 326--338, arXiv:1112.1790; PDF read this session at
  `web.ma.utexas.edu/users/juschenko/files/Dykema-Juschenko-Heister.pdf`,
  dated 24 November 2014.  Abstract, verbatim: "By calculating all the ULIE
  groups over the field `K = F_2` of two elements, for ranks `(3,n)`,
  `n <= 11` and `(5,5)`, we show that the Direct Finiteness Conjecture and
  the Invertibles Conjecture (which implies the Zero Divisors Conjecture)
  hold for these ranks over `F_2`."  Definition 2.12 fixes the semantics:
  DFC holds over `K` for rank pair `(m,n)` if for all groups `G` and all
  `a,b` in `K[G]` of ranks `m` and `n`, `ab = 1` implies `ba = 1`; "rank" is
  support size, and `m, n >= 2`.  Remark 2.13 gives `(m,n)` iff `(n,m)`.
  Remark 2.8: over `F_2` a minimally realizable partition has only pairs plus
  the singleton `{(0,0)}`, so `m` and `n` are both odd — independent
  corroboration of the parity step in Section D.  Their introduction also
  confirms the landscape: Kaplansky proved characteristic zero; Ara--O'Meara--
  Perera proved residually amenable; Elek--Szabo proved sofic, with stable
  finiteness, over division rings.

Not verified this session, and used only as the source presents them:
Bradford--Fournier-Facio (Math. Z. 308 (2024) art. 58) for the Hopfian
wreath-product work, and Ceccherini-Silberstein--Coornaert--Phung (GGD 19
(2025) 495--503) for surjunctive groups.  The Zenodo record 21840947 the
source names in its own reference list was not retrievable by the source
either, and nothing here depends on it.

## H. Graph nodes carrying this material

Established: `binary-leavitt-algebra-not-directly-finite`,
`leavitt-unit-group-algebra-surjects-onto-leavitt`,
`leavitt-corner-idempotent-unital-surjection`,
`direct-finiteness-not-inherited-by-quotients`,
`leavitt-rank-three-unit-lift`,
`dykema-heister-juschenko-bounded-rank-direct-finiteness`,
`leavitt-rank-three-lift-inverse-support-thirteen`.

Open: `leavitt-corner-one-sided-lift-exists`,
`binary-leavitt-family-lifts-into-unit-corner`,
`leavitt-corner-kernel-is-jacobson-radical`,
`leavitt-unit-group-algebra-not-directly-finite`.

**Where this joins the rest of the graph.**  The lane head is shared with the
Gottschalk lane audited the same day in
`research/artifacts/gottschalk-leavitt-audit-2026-08-17.md`: failure of direct
finiteness feeds `leavitt-group-algebra-not-stably-finite` and from there
`leavitt-unit-group-nonsurjunctive`, so a witness produced here would settle
two named conjectures at once.  The two lanes attack the *same* correction
equation from different sides — that one works in the whole algebra with the
right factor pinned over `s_0`, which is what the cellular-automaton reading
needs, while this one works in `e A e` where the augmentation no-go is
inactive.  Neither implies the other, and only this side carries the support
floor of Section D.  Read together, they say the missing object is one
solution of `(a + alpha)(b + beta) = 1` with `alpha, beta` in a kernel nobody
has computed, and that computing that kernel — even to the point of deciding
whether the corner's part of it is nonzero — is the next real piece of work.
