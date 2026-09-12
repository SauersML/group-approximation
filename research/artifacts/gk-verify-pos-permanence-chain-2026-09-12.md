# Independent verification of the surjunctive nonsofic permanence chain

Lane `gk-verify-pos`, 2026-09-12. An adversarial re-derivation, made
independently of `review-surjunctive-nonsofic-2026-09-12.md`. The edits in
Section 8 were built on main at `cd999fec9`.

## Verdict

| Artifact (blob reviewed) | Statements | Result |
|---|---|---|
| `rf-lamp-wreath-surjunctivity-2026-09-11.md` (`e6f2f1395`) | Theorem 1, Corollary 2 | PASS |
| `finitary-split-extension-surjunctivity-2026-09-11.md` (`da5e18587`) | Theorem 0, Lemma 5.1, Corollaries 6 and 7 | PASS |
| `surjunctivity-graph-folds-2026-09-11.md` (`aee566c6b`) | graph-of-groups theorem | PASS |
| `lef-graph-wreath-surjunctivity-2026-09-12.md` (`a0f24c4cb`) | Theorems 1 and 2 | PASS |
| `fp-surjunctive-nonsofic-double-2026-09-11.md` (`56ab9e344`) | finite presentation, surjunctivity | PASS |
| `gottschalk-surjunctivity-fixed-tester-proof` (route body) | subgroup heredity, marked limits, noninjective directed colimits | PASS |
| `gottschalk-stable-three-factor-reduction-2026-09-08.md` | stable reduction to three unary factors | PASS |
| `affine-normal-form-reduces-three-factor-surjunctivity` (route body) | recipient-affine normal form | PASS |

No mathematical gap was found. Two routes consumed external theorems only in
their bodies; those inputs are now claims (Section 8). No route on main
completes a path into `gottschalk-surjunctivity-conjecture`, and no claim on
main asserts that the binary Leavitt unit group is surjunctive (Section 7).

## 1. Residually finite lamp wreaths

* **Coordinates.** `(n',g)(n,g)^-1 = (n' n^-1, 1)`, so `H(n,g) = H(n',g')`
  exactly when `g = g'` and `n'(s) n(s)^-1` lies in `A_0` for `s in S`. The
  right action is `(a,g).(n_1,g_1) = (a . nu_(n_1)(g), g g_1)` with
  `nu_(n_1)(g)(s) = A_0 n_1(g^-1 s)`; normality of `A_0` makes it well defined.
* **Strata.** `{g : g u = s} = G_s g_u`. An intersection over `s in U` of right
  cosets of the `G_s` is empty or a right coset of `G_U`.
* **Lemma 3.1.** For `g = k h_i` and `p in P`, `k h_i p = (k eta) f` with
  `eta = h_i p f^-1 in K`, independent of `k`. So `Psi` is a cellular automaton
  over `K` with memory `{eta(i,p)}`. Left invariance `mu_(k h_i) = mu_(h_i)` is
  what makes the rule at label `i` independent of `k`. The inverse memory
  `{1} union h_i^-1 D f_j` is right: at `g = k h_i`, `k d f_j = g (h_i^-1 d f_j)`.
* **Proposition 4.1(b).** Put `W_j = g P_k ... P_(j+1)`, contained in `gP`.
  The invariant for `j < j_V` is
  `z_j = (rho_V^(j))^[U] y` on `W_j`, where `rho_V^(j)` is `tau_V` followed by
  the slicewise inverses for the proper subsets of `V` among `U'_1..U'_j`.
  * A stage `U'_j` not inside `V` is the identity on `W_j`: pick
    `s in U'_j \ V`; then `W_j F_(U'_j)` lies in `g F_U`, which misses `Z_s`.
  * A stage `U'_j` properly inside `V` acts by nested extension.
  * At `j_V - 1` the composite is `rho_V`, because the order refines
    cardinality. Stage `j_V` returns `y` on `W_(j_V)`. Every later `U'_j` has
    `|U'_j| >= |V|` and differs from `V`, so none lies inside `V`.
* **Bijectivity.** With a fixed memory, commuting with `l_k`, `k in G_U`, forces
  `mu_(k^-1 g) = mu_g`, so Lemma 3.1 applies.
* **Consistency test.** `X` a point and `A = Z` gives `Z x G` surjunctive for
  every surjunctive `G`, which agrees with Arzhantseva--Gal for finitely
  generated residually finite kernels.

## 2. Theorem 0

* **Coset space.** `(f',g')(f,g)^-1 = (f' alpha_(g' g^-1)(f^-1), g' g^-1)`. So
  `H_(S,q)\W ~= Q x G`, and the right action multiplies the fibre on the right
  by `q p_S(alpha_g f_1)`.
* **`iota_(S,S) = id`.** Coherence with `V = U = S` gives
  `iota_(S,S) iota_(S,S) = iota_(S,S)`; injectivity gives the identity. So
  `tau_S` is the transplant to `H_(S,q)\W`.
* **Slice coefficients.** The instance needed is (A2) at the pair `(V,U)`, not
  only at `(U,S)`. If `g L(f_m)` misses `U\V`, then
  `p_U(alpha_g f_m) = iota_(V,U) p_V(alpha_g f_m)`, and by coherence
  `c^U_m(g) = q iota_(U,S) iota_(V,U) p_V(alpha_g f_m) = c^V_m(g)`. (A2) is
  quantified over every finite `S`, so the instance is available.
* **Fibre equivariance.** The coefficients multiply on the right, so `tau_U`
  commutes with left `Q_U`-translation.
* **Extension lemma.** `y_(kh)(h',g) = y_k(h h',g) = (l_(h^-1) y_k)(h',g)`, so
  `phi(y_(kh))(1,g) = phi(y_k)(h,g)`. Transitivity follows by restricting `y_k`
  to `J x G`.
* **Adversarial tests.**
  * Trivial action, `X` a point, `N` any residually finite group: (A1)--(A3)
    hold, giving `N x G` surjunctive. An independent direct proof agrees: the
    transplant to `(N/N_0) x G` is a cellular automaton over `G` with alphabet
    `B^(N/N_0)`.
  * A nontrivial action on a point, such as `Z^2 semidirect SL_2(Z)`, fails
    (A3). The theorem does not overreach there.

## 3. Lemma 5.1 and the doubles

* `alpha` is an action, and `alpha_g(e_(x_0)) = 1` is consistent.
* `Phi` on `Ghat`: `(e_(gx_0)^-1, g)(e_(hx_0)^-1, h) = (e_(ghx_0)^-1, gh)`, and
  `Phi(gammahat) = (1, gamma)`.
* `Psi` respects the conjugation relation.
* `Phi Psi(e_(gx_0), 1) = (e_(gx_0), 1)`: `alpha_(g^-1)(e_(gx_0)) = e_(g^-1 x_0)^-1`
  and `(1,g)(e_(g^-1 x_0)^-1, g^-1) = (e_(gx_0), 1)`.
* (A3) for doubles needs both cases, `x_0 in S` and `x_0 not in S`; both hold.

## 4. Graph folds

* `r` respects the edge relations by (4.1), and `c_e = 1` on tree edges.
* `ker r` meets `w G_v w^-1` trivially because `r(w g w^-1) = r(w) g r(w)^-1`.
  Bass--Serre actions are without inversion, so the kernel acts freely and
  `N ~= pi_1(N\Z, o)`.
* `N\W/G_v ~= G/r(G_v) = G/G`: one vertex per type, so `G` fixes every vertex.
  Edges of type `e` form `G/r(A_e)`, with orientation preserved.
* The loop formula (3.2) needs only that loops at `o` go to loops at `o`. Tree
  symbols equal `1`, which covers translated tree edges.
* (A3): `k` fixing `S` pointwise preserves `X \ S`, so
  `p_S(b_(ke)) = p_S(b_e)` in both cases.

## 5. LEF graph wreaths

* **Lemma 3.1.** `F` contains `SM` and `Omega M`. The partial table fixes the
  coincidence pattern of those products, so `sigma_K tau_K = id` is checked on
  assignments over `eta(SM)`, and the forbidden pattern survives on
  `eta(Omega M)`. `eta(1) = 1` because `1 . 1 = 1` lies in the table.
* **Lemma 4.1.** Recorded intermediate products and injectivity of `theta` let
  the same syllable reduction run on the images. A nonempty reduced word stays
  reduced, because reducedness depends only on the vertex sequence and on which
  coefficients are `1`. Actor components are unchanged.
* **Theorem 2, nonsoficity.** The use matches the statement of
  `sofic-groups-kill-rigid-compression-defects`: `H` countable sofic,
  `Gamma <= G <= H` both Kazhdan, `Gamma` infranormal in `G`, `z in C_H(Gamma)`.
  * `z = a_Gamma` is fixed by `Gamma`, because `Gamma` fixes the vertex `Gamma`.
  * A compressor `t` with `t Gamma t^-1` properly inside `Gamma` exists:
    otherwise every compressor normalizes `Gamma`, and they generate `G`.
  * `[t a_Gamma t^-1, gamma] = a_(t Gamma) (a^-1)_(gamma t Gamma)` is nontrivial
    under the retraction onto `A_(t Gamma)`.

  The proof of the rigid-defect theorem is negative-side work and is not
  reviewed here.

## 6. Finite presentation of the double

* **Stability.** `R = F_2[x_1^(+-1), x_2^(+-1), x_3^(+-1)]` is noetherian of
  Krull dimension 3. So `K2(r,R) -> K2(R)` is an isomorphism for `r >= 6`
  (van der Kallen's injective stability; the artifact cites Weibel, K-book,
  III.5.5.2).
* **Bass fundamental theorem for regular rings.**
  `K2(A[t^(+-1)]) = K2(A) (+) K1(A).{-,t}` and
  `K1(A[t^(+-1)]) = K1(A) (+) K0(A)`. Starting from `K0(F_2) = Z` and
  `K1(F_2) = K2(F_2) = 0`:
  * `K2(R_1) = 0` and `K1(R_1) = Z x_1`;
  * `K2(R_2) = Z {x_1,x_2}` and `K1(R_2) = Z x_1 (+) Z x_2`;
  * `K2(R_3) = Z {x_1,x_2} (+) Z {x_1,x_3} (+) Z {x_2,x_3}`.

  So the three symbols generate the kernel as a group, and three relators
  present `E_6(R)` from `St_6(R)`.
* **Presentations.** A semidirect product of finitely presented groups is
  finitely presented. An amalgam of finitely presented groups along a finitely
  generated subgroup is finitely presented by (3.1).
* **Positive part.** Surjunctivity of `D` needs only residual finiteness of `G`
  (Theorem E) and the fold theorem. Nonsoficity is Kun--Thom Theorem A.

## 7. Wiring audit (main at `cd999fec9`)

Routes into `gottschalk-surjunctivity-conjecture`, and what they require:

* `gottschalk-via-countable-transitive-decoder-fiber` requires
  `injective-ca-admit-countable-transitive-decoder-fiber`: open, no route.
* `gottschalk-via-matrix-observable-extension` requires
  `injective-ca-pullbacks-extend-to-matrix-observables`: open, no route.
* `gottschalk-via-surjunctive-fixed-host` requires
  `fixed-gottschalk-test-group-is-surjunctive`: open, no route.
* `stable-three-factor-reduction-proves-gottschalk` requires
  `three-factor-finite-alphabet-ca-are-surjunctive`. Its only route,
  `affine-normal-form-reduces-three-factor-surjunctivity`, requires
  `recipient-affine-three-factor-ca-are-surjunctive`: open, no route.

So no complete path into the goal exists on main. No claim on main asserts
surjunctivity of the binary Leavitt unit group. The steward's compiled
`cairn why` remains the authoritative confirmation.

## 8. Corrections landed

* `fp-surjunctive-nonsofic-double-by-stable-k2` used van der Kallen stability
  and the three-variable Laurent K2 computation only in its body. The existing
  claims `stable-laurent-k2-has-minimal-three-symbol-packet` and
  `rank-five-laurent-k2-stability-is-dimension-free` treat two inverted
  variables with polynomial spectators, where `K2 = Z (+) C_(q-1) (+) C_(q-1)`,
  not this ring. New claim `three-laurent-f2-k2-rank-six-kernel-is-three-symbols`
  with its `-proof` route; the route now requires it.
* `lef-graph-wreath-via-finite-lamp-tables` used Green's graph-product normal
  form and residual-finiteness theorems only in its body. New claim
  `graph-product-normal-forms-and-rf-permanence` with its `-citation` route;
  the route now requires it.

## 10. The fixed tester

* **Locality.** A cellular automaton over `H <= G`, run on `A^G`, is a product
  of copies over the cosets of `H`, so surjunctivity passes to subgroups. The
  memory of any automaton lies in a finitely generated subgroup, so `G` is
  surjunctive iff every finitely generated subgroup is.
* **Marked limits.** The injectivity detector `N` comes from compactness of
  `{(x,y) : x(1) != y(1)}`, covered by the open sets where `tau(x)` and
  `tau(y)` differ at one coordinate. The missing cylinder `F` exists because
  the image is closed. Once a ball containing `NM` and `FM` has the same
  equality table in `G_i`, transport gives:
  * injectivity, since the outputs on the copy of `N` read only the copy of
    `NM`, together with translation;
  * nonsurjectivity, from the copy of `FM`.

  The argument uses only "eventually", so it holds for nets.
* **Noninjective colimits.** An equality among marked words in the colimit
  holds at some stage. An inequality in the colimit holds at every stage,
  because the maps to the colimit are homomorphisms. So the finitely generated
  subgroups `H_j` converge to `H` as a net.
* **The host.** The abstract theorem is the standard one. A universal
  finitely presented group contains every finitely presented group (Higman),
  and every group is a directed colimit of finitely presented groups with
  arbitrary maps. The class of surjunctive groups is subgroup-closed and
  closed under such colimits, so `U surjunctive <=> every group surjunctive`.
  The node `universal-all-group-subgroup-colimit-class-tester` was not
  re-derived line by line here; its mathematics is the argument above.

## 11. The three-factor reduction and the affine normal form

* **Expression.** `mu = sum_p mu(p) prod_s delta_(p_s)(X_s)` over `Z/qZ`; exactly
  one product equals `1` at each input.
* **One cancellation.** Precompose `F x id` by `S(x,u,v) = (x, u + A(x), v + B(x))`
  and postcompose by `T(y,r,s) = (y - c r s e_i, r, s)`. Coordinate `i` becomes
  `F_i - cAB - cuv - cuB - cvA`, the new coordinates are `u + A` and `v + B`,
  and all other coordinates are unchanged.
* **Potential.** With `a,b >= 2` and `a + b = d`, the seven new occurrences
  `uv, uB, vA, u, A, v, B` have lengths `2, b+1, a+1, 1, a, 1, b`, all at most
  `d - 1`. So `sum 8^length` drops from at least `8^d` to at most
  `8^d - 8^d + 7.8^(d-1) < 8^d` for that contribution, and the procedure
  terminates.
* **Preservation.** Adding identity tracks, and composing with bijective
  shears, preserves injectivity and surjectivity in both directions. No new
  spatial addresses appear. The reduction is an honest equivalence, not a
  restatement: the three-factor class is a genuine subclass, and every
  automaton is stably equivalent to a member of it.
* **Affine normal form.** `H(x,u) = (x + u, F(x) - x - u)` equals `T o (F x id) o S`
  with `S(x,u) = (x, x + u)` and `T(y,w) = (w, y - w)`, both bijective. The
  fibre is `H^-1(z,w) = {(x, z - x) : F(x) = z + w}`. First-block outputs have
  own-track coefficient `+1` and read only `u` otherwise. Second-block outputs
  have own-track coefficient `-1` and read only `x` otherwise. The route into
  `three-factor-finite-alphabet-ca-are-surjunctive` is valid; its prerequisite
  is open, so nothing is established by it.

## 12. The permanence-closure obstruction (gk-fixed-host)

Reviewed: `fixed-host-permanence-closure-obstruction-2026-09-12.md` (`75922f372`),
`sofic-permanence-closure-omits-simple-fa-nonsofic-groups` with its proof route,
`fixed-host-outside-sofic-permanence-closure` with its proof route, the refuted
`fixed-host-lies-in-sofic-permanence-closure`, and the dead route
`fixed-host-surjunctive-via-sofic-permanence`. Verdict: PASS.

Theorem 3.1, for `Sigma` finitely presented, simple, FA and nonsofic, and
`D_Sigma` the groups with no copy of `Sigma`:

* **(c) colimits.** Lift `j(s_a)` to one stage, and kill the finitely many
  relator values at a later stage. This gives `phi : Sigma -> G_i` with
  `psi_i phi = j`, and `phi` is injective because `j` is. Only finite
  presentation is used, and no injectivity of the structure maps. So an
  embedding into the colimit does factor through an embedding into one stage.
* **(d) extensions.** `Sigma ∩ N` is normal in `Sigma`, so it is `1` or `Sigma`.
* **(e) graphs of groups.** FA gives a fixed vertex of the Bass--Serre tree, so
  `Sigma` lies in a conjugate of a vertex group.
* **(f) marked limits.** Ball agreement makes the relators hold in `K_n`, and a
  nontrivial generator stays nontrivial, so `K_n` is a nontrivial quotient of
  `Sigma`. Simplicity gives `K_n ~= Sigma`. The same argument covers local
  embeddability of groups that are not finitely generated.

Corollary 3.2:

* Finitary split extensions: (A1) with residually finite `N_S` makes `N`
  residually finite, hence sofic, and then (a) and (d) apply.
* Graph folds: the vertex groups embed in a member, so (b) and (e) apply.
* LEF-lamp graph wreaths: the kernel `Lambda(A)` is a graph product of sofic
  groups, which is sofic (Ciobanu--Holt--Rees). The artifact's star-splitting
  induction also works.

Instance `Sigma = R^x`:

* FA: `R_R ~= R_R^12` gives `R^x ~= GL_12(R) = EL_12(R)`, which is Kazhdan, and
  (T) implies FA.
* `R^x` embeds in `U` because `U` contains every recursively presented group.
* Trust surfaces:
  * finite presentation of `R^x`, imported from Khanh, arXiv:2609.08428v1,
    Theorem 6.1, whose proof has not been reviewed here;
  * the (T) and simplicity nodes;
  * the universal container.

The invalidator's prerequisites each have a live route on main.

**Overlap.** `gottschalk-counterexamples-lie-outside-the-permanence-closure`
(route `permanence-closure-evasion-proof`, from the table-realization lane)
proves an FA-free form for the landed operations. It sends a copy of `Q` in a
graph fold into the fold kernel, which is free, and a copy in an LEF graph wreath
into a sofic graph product. I re-derived it: PASS. The two claims are distinct:

* the FA form survives arbitrary extensions and arbitrary graphs of groups;
* the FA-free form needs only an infinite finitely presented simple nonsofic group.

Neither carries `distinct_from` on the other.

## 9. Trust surfaces not verified here

* Kun--Thom, arXiv:2608.06222v3, Theorems A and E: the statements were read by
  `review-surjunctive`; the proofs were not checked.
* Finite presentation of `St_n(R)` for `n >= 4`
  (`steinberg-finite-presentation-and-kazhdan-theorem`).
* van der Kallen's injective stability and Bass's fundamental theorem.
* Green's graph-product theorems, and Lawton's theorem that residually finite
  groups are surjunctive.
* The proof of `sofic-groups-kill-rigid-compression-defects`.
