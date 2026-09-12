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

## 13. The Rokhlin entropy self-copy dichotomy (gottschalk-positive-host)

Reviewed: `rokhlin-entropy-self-copy-dichotomy-2026-09-12.md`, the claims
`rokhlin-supremum-dichotomy-with-centralized-self-copies`,
`positive-rokhlin-entropy-makes-leavitt-units-surjunctive` and
`positive-rokhlin-entropy-on-one-host-proves-gottschalk`, the Seward imports,
and the open claims `leavitt-unit-group-surjunctive`,
`leavitt-unit-group-has-positive-rokhlin-entropy-action`,
`tester-host-has-positive-rokhlin-entropy-action` and
`every-group-has-positive-rokhlin-entropy-action`. Verdict: PASS.

* **Theorem A.** Take `G <= Gamma` with `h_sup(G) < infinity`, and finite `T`
  commuting with `G` with `T ∩ G = 1`.
  * Independence of the `G`-translates of `Q` needs only `T ∩ G = 1`:
    `gt = g't'` forces `g'^-1 g in G ∩ T`.
  * `xi` is a partition, because `M` is a transversal. Each `C_pi` is
    `T`-invariant, and `xi` refines `Q`, since `C_pi` lies in the union of the
    `D_(s.pi)`.
  * `R_l = union over s, pi with pi(s^-1) = l of (C_pi ∩ s.M)`: for
    `x = s.y` with `y in D_pi ∩ M`, `x(1) = y(s^-1)`.
  * `sigma_G(xi)` is `T`-invariant because `G` commutes with `T`, so every atom of
    the `k`-piece generator `beta` is `T`-invariant and `beta` lies in
    `sigma_Gamma(alpha)`.
  * `H(alpha | F) <= mu(M) log k = log(k)/|T|`, since `M in F` and `alpha` is
    trivial off `M`.
  * With subadditivity (S2) and the small free factor (S1), this gives
    `h^Rok_Gamma(L^Gamma) < 2 eps`, and (S4) gives `h_sup(Gamma) = 0`.
* **Corollary A1.** `Gamma_1 ~= Gamma` carries the same supremum, and the finite
  subgroups of `Gamma_2` commute with `Gamma_1` and meet it trivially. A2
  follows from (S4)--(S7).
* **Lemma 2.1.** `iota_0(a) iota_0(a') = s_0 a a' t_0 + s_1 t_1` and
  `t_0 iota_0(a) s_0 = a`. `iota_0(a) iota_1(b) = s_0 a t_0 + s_1 b t_1` is
  symmetric in the two factors. So `U x U <= U`.
* **Lemma 2.2.** `s_u t_v` are matrix units summing to `1`. Simplicity of
  `M_(2^n)(F_2)` gives `GL_(2^n)(F_2) <= U`.
* **Section 3.** `Gamma_U x Gamma_U` embeds in `Gamma_U` along the even and odd
  indices. `Sym_fin(N)` supplies unbounded finite subgroups, so POS(`Gamma_U`)
  gives surjunctivity of `U_*`, hence of every group.
* **Citation fidelity.** A grep of the MSI text
  `review-lit/entropy/1501.03367.txt` finds:
  * Theorem 1.11 ("Let P be a countable group containing arbitrarily large
    finite sub[groups]", line 252);
  * the chain `INF⇒RBS⇒INV+CPE+GOT+KAP` (line 294);
  * Corollary 4.1 (line 725).

  The other quoted statements were not re-read.
* **No premature establishment.** On main at `d3fefdbc63`,
  `leavitt-unit-group-surjunctive` is open. Its routes need
  `leavitt-unit-group-has-positive-rokhlin-entropy-action` (open) or
  `every-group-has-positive-rokhlin-entropy-action` (open, no route). The goal
  routes `gottschalk-via-positive-rokhlin-entropy-host`,
  `gottschalk-via-maximal-bernoulli-rokhlin-entropy` and
  `fixed-tester-surjunctive-via-rokhlin-entropy` each need an open maximality or
  positivity claim. The two maximality claims form a two-route cycle, an
  equivalence, which a least fixpoint never fires.

## 14. Bernoulli Rokhlin maximality (gk-rokhlin)

Reviewed: `gottschalk-rokhlin-entropy-route-2026-09-12.md` (`6328765c3`) and the
claims `strict-automaton-lowers-bernoulli-rokhlin-entropy`,
`bernoulli-rokhlin-maximality-passes-to-subgroups` and
`bernoulli-rokhlin-deficit-has-a-finitary-witness`. Verdict: PASS, with one
normalization added forward.

* **Theorem 1.**
  * Step 0: `lambda`-a.e. `y` avoids every translate of `[p]` in every copy.
  * Step 2: the Borel maximal `S`-independent set, built from a countable
    separating family, gives `lambda(C)(1 + |S|) >= 1`, so `s >= 1/D`.
  * Step 3: `w^-1.c = w'^-1.c'` forces `w' w^-1 = 1` by independence.
  * Step 4 decodes `beta(y) = (w.y)(w)` from the unique `w in Omega` with
    `w.y in C`. The entropy count is
    `log 3 + s k log(q^|Omega| - 1) + (1 - |Omega| s) k log q = log 3 + k log q - s k delta`.

  **Normalization.** Step 4 needs `C ⊆ B = Omega^-1 C`, that is `1 in Omega`, so
  that `{C, B \ C, Y_0 \ B}` partitions `Y_0` and `y(1)` is an entry of the
  pattern at `y in C`. This is harmless: `nu` is invariant, so the pattern
  can be translated to put `1` in its window, and `|Omega|`, `delta` and
  `D = |Omega Omega^-1|` (a conjugate set) are unchanged. The sentence has been
  added to the artifact.
* **Proposition 2.**
  * (1) The pullback of an `H`-generator along `x -> x|_H` generates for `G`,
    since `x(gh) = (g^-1.x)(h)`.
  * (2) The join over right coset representatives is `H`-generating, and
    `x -> (h -> (x(ht))_t)` is an `H`-equivariant isomorphism onto `(L^T)^H`.
* **Theorem 3.**
  * The upper bound runs the conditional typical-set lemma along `k'` copies;
    the translates `alpha'(f^-1.y)` list `U`.
  * The lower bound approximates a near-optimal generator by a cylinder partition
    `psi(x|_E)`, using `H(beta | alpha_0^F) <= H(beta | alpha^F) + sum_f H(f.alpha | f.alpha_0)`.
* **Corollary 3.1.** Incidence patterns lift to a later stage of any directed
  colimit. Finite groups are maximal because `H(join_(g in K) g.alpha) <= |K| H(alpha)`.
* **No restatement into the goal.**
  * `gottschalk-via-maximal-bernoulli-rokhlin-entropy` requires the open
    ergodic-theoretic claim `bernoulli-rokhlin-entropy-maximal-for-every-group`,
    which is Seward's open question, not surjunctivity renamed.
  * Its equivalence with `bernoulli-rokhlin-entropy-maximal-on-fixed-tester` is a
    two-route cycle.

## 15. Rectangle clauses and the recognition dichotomy (gk-logic)

Reviewed: `surjunctivity-is-axiomatized-by-rectangle-clauses`,
`surjunctivity-recognition-has-a-pi2-upper-bound` and
`surjunctivity-recognition-dichotomy`, with their proof routes (main at
`1ad7aa663a`). Verdict: PASS.

* **Axiomatization, if.** With realized data, `sigma tau(x)(1)` reads
  `x(x_s x_m)`. That pattern is constant on the realized forward coincidence
  classes, which are coarser than `T_f`, so `Dec(T_f)` gives `x(1)`. Every `q`
  constant on `T_r`-classes is realizable at `x_m x_s`, because the realized
  reverse coincidences are finer than `T_r`. So `not Enc(T_r)` gives `tau sigma != id`,
  and with `sigma tau = id` the automaton `tau` is injective and not surjective.
* **Axiomatization, only if.** Take the memories, with `1` adjoined, as labels,
  and the realized tables as `T_f` and `T_r`. A left-inverse automaton exists
  by compactness, and `tau sigma != id` translates to the identity.
* **`P(D)`.** A realization in `K` gives a homomorphism `P(D) -> K`. It
  preserves the forward equalities and cannot create reverse coincidences, so
  `P(D)` realizes `D`. Universal sentences pass to subgroups, ultraproducts,
  local embeddings and directed colimits. An existential realization
  transfers to an existentially closed `E` through `E * K`.
* **Upper bound.** `NONSURJ` is `exists D, w [Sigma^0_1 AND Pi^0_1]`, which is
  `Sigma^0_2`. On a host with decidable word problem it is `Sigma^0_1`.
* **Dichotomy.**
  * (B1): `P(D)` is finitely presented.
  * (B2): a direct seed switch gives `Pi^0_2`-hardness of `SURJ_enum`. Take the
    free product over `n` of copies of `P(D)`, where copy `n` is killed when a
    witness for the `n`-th `Sigma^0_1` clause appears. The result is trivial
    when the `Pi^0_2` sentence holds, and otherwise contains `P(D)`.
  * (B3): Adian--Rabin with seed `P(D)` reduces a `Sigma^0_1`-complete word
    problem to `SURJ_fp`. So `SURJ_fp` is undecidable and `NONSURJ_fp` is
    `Pi^0_1`-hard, hence not r.e.
  * Under (A) all the sets are full or empty.

  `Pi^0_2`-completeness of `SURJ_fp` is correctly not claimed.
* **Consequence for search.** No complete r.e. listing of nonsurjunctive finite
  presentations exists unless there are none. A counterexample search is a
  `Sigma^0_1` certificate search in one host with decidable word problem.
* **Trust surfaces.** Adian--Rabin (Lyndon--Schupp IV.4.1). The repository switch
  theorem was not re-read; the direct construction above suffices for (B2).

## 16. Controlled self-linear feedback (gk-three-factor)

Reviewed: `three-factor-audit-and-controlled-feedback-2026-09-12.md`, Sections
1--3, and `controlled-self-linear-feedback-ca-are-surjunctive`. Verdict: PASS.

* **Lemma 2.2(a)** uses only additivity of `L_Y` and `L_(Y')(0) = 0`.
* **Both uses of `nonlinear-certificate-fibers-are-all-surjective-or-all-strict`
  match its hypotheses.**
  * `E(X,Y) = (L_Y X, Y)`: certificate `Y`, bijective fibre at `Y_0`.
  * `D = F o E^-1`: certificate `Z` in `R^d`, fibre `v_0` at `Z = 0`.

  One surjective fibre suffices. Re-derived mechanism: finite-output rigidity
  (for `c'` a finite modification of `c`, `T_(c') o T_c^-1` is an injective map
  that fixes all but finitely many coordinates, hence bijective), density of
  finite modifications, and closedness of fibrewise surjectivity by compactness.
* **Theorem 2.3.** Each row `b < a` is (2.2) at `X_b = 0`, so
  `F(0, X_(>=a)) = (0, S_a(X_(>=a)))` and `S_a` is injective. Downward induction
  uses `v_0 = S_(a+1)`.
* **Sharpness.** In `(x + u, F(x) - x - u)`:
  * with `x` first, the row carries the offset `u`;
  * with `u` first, the own part `-u` is admissible (constant controller `-2`
    at `s = 1`, `L0 = -id`), but the offset `F(x) - x` vanishes only for `F = id`.

## 17. Defect-window automata and nested defects (gk-defect-automaton)

Reviewed: `defect-window-automata-2026-09-12.md` (main at `f317a3b0ce`). The
established claims are:
* `leavitt-units-carry-nested-rigid-defect`;
* `nested-rigid-defects-live-in-nonsofic-kazhdan-groups`;
* `wreath-subgroups-meeting-lamps-finitely-are-rf`;
* `free-centralizer-amalgams-are-surjunctivity-inert`.

The route `nonsurjunctive-from-nested-rigid-defect` into
`leavitt-unit-group-nonsurjunctive` stays incomplete, because its prerequisite
`nested-rigid-defects-force-nonsurjunctivity` is open. Verdict: PASS.

* **Lemma 1.** Constants map to constants injectively, so single cells display
  every symbol. If `Omega_1 M` misses `Omega_2 M`, the displayed patterns form a
  product, so a minimal Garden of Eden has a connected overlap graph, and
  `{1, d}` forces `d in M M^-1`.
* **Lemma 2.** The image of `H` in a metric ultraproduct of symmetric groups is
  countable and sofic. Images of the Kazhdan groups stay Kazhdan,
  `psi(P_Gamma)` lies in `P_(psi(Gamma))`, and centralizers map into
  centralizers. So the rigid-defect theorem kills the image.
* **Theorem 4.**
  * `Phi(k) = k_(x_0)` respects `Gamma x K`, because `Gamma` fixes `x_0`.
  * `Psi(k_(h x_0)) = h k h^-1` is well defined, because `Gamma` commutes with `K`.
  * `P` is the empty-graph LEF wreath, so surjunctivity transfers.
  * `[t k_(x_0) t^-1, gamma] = k_(t x_0) (k^-1)_(gamma t x_0)` is a reduced word of
    length two.
* **Proposition 5.2.** In the nine-leaf configuration, `z in J = V_(1000)`
  centralizes `Gamma ~= EL_3(R)` and `w = u z u^-1` lies in `V_(0001) <= Gamma`.
  Simplicity gives `Z(Gamma) = 1`, so `[w, gamma] != 1` for some `gamma`. The
  defect is rigid and nested. This is the OpenAI mechanism read as a defect.
* **Proposition 6.1.**
  * `z = t^-1 w t` lies in `G`.
  * `C_G(Gamma)` is not normal, because `t z t^-1 = w` fails to centralize `Gamma`.
  * The rigid-defect theorem with ambient group `G` makes `G` nonsofic.
  * (4) is `z in C_G(Gamma) ∩ t^-1 Gamma t` with `w` outside `Z(Gamma)`.
* **Proposition 7.1.** `w nu w^-1 = (n (g.nu) n^-1, 1)` has support `g supp(nu)`, so
  `Q'` preserves the finite `S`. Then `rho(n,g) = (n|_S, g)` is an injective
  homomorphism into `A^S ⋊ Q'`, which contains `A^S x K` with finite index.
* **Scope.** The one open step toward a refutation of Gottschalk is
  `nested-rigid-defects-force-nonsurjunctivity`. No strict automaton is constructed.

## 18. Simple Kazhdan hosts (gk-fixed-host, with gk-observables Section 3.4)

Reviewed: `simple-kazhdan-hosts-2026-09-12.md` (landings `a03dd1b0c8`, `8dff8bfdcb`,
`97dc9b6e5f`). Verdict: PASS.

* **Theorem 1.1 (containers).**
  * *Step 1.* A single member of the hyperbolically embedded family
    `{<h_1>, <h_2>}` is hyperbolically embedded, which is what Lemma 5.8
    needs. Clause (c) puts the generators of `C'` into `gamma_1(S) <= gamma_1(H)`,
    so `F_1 = gamma_1(H)`. Ball injectivity at the single element `c` gives
    injectivity on the simple `C'`. `K(F_1) = 1`, because a finite normal subgroup
    is normalized by the suitable `gamma_1(S)`.
  * *Step 2.* `D = <<gamma_1(C')>>` is suitable:
    * it is infinite and normal, hence s-normal, hence non-elementary (Osin, Lemma 7.1);
    * `K_(F_1)(D)` is normal by maximality, hence trivial.

    Clause (c) with `t = gamma_1(X_H)` gives `Q = gamma_2(D) = <<C'>>_Q`.
  * *Step 3.* For `1 != s in C'`, `<<s>>_Q` contains `C'` and hence `Q`. By Zorn
    there is a maximal normal subgroup avoiding `s`; it meets `C'` trivially, and
    the quotient is simple, infinite, finitely generated and Kazhdan.
  * *Trust surfaces:* Schupp, Hull Theorem 7.1 and Corollary 5.7, Lemmas 3.5 and 5.8,
    Osin Lemma 7.1, Dahmani--Guirardel--Osin free factors, and the hyperbolic
    Kazhdan partner.
* **Theorem 2.1 (reduction).** Localize to `<M>`, embed, and use subgroup heredity.
* **Theorem 3.3 (coset-shift witness).**
  * `psi(gh u^-1 H) = g u^-1 (u h u^-1) H`, so `psi` is well defined.
  * `psi(kuH) = kH`, so `psi` is onto.
  * `k in u^-1 H u \ H` collapses `kH` and `H`.
  * `Psi(y) = y o psi` is continuous, equivariant and injective, and its image is
    constant on fibres of size `[u^-1 H u : H] >= 2`.
  * Instance: `u` carries `[1]` onto `[11]`, so `u V_1 u^-1 = V_11 < V_1`.
  * `BS(1,2)` with `u = t` and `H = <a>` shows such embeddings exist over
    surjunctive groups too.
  * `kazhdan-bernoulli-rigidity-forces-surjective-embeddings` is correctly
    refuted, and `fg-simple-kazhdan-surjunctive-via-bernoulli-rigidity` is invalidated.
* **Theorem 3.4 (range projection).**
  * Step 3: `Stab(x) = K`, because `g K t = K t` iff `g in K`, and
    `tau(x) in Y ∩ C_c` has the same stabilizer.
  * Step 4: moving the supports off `F ∪ S_O^-1 F` makes `<z| a_g |g.z>` depend only
    on whether `g in h K h^-1`. So `O` has equal expectations at `h.u` and `h.y`,
    while `P` gives `0` and `1`.
  * (b): stabilizers of finite perturbations are finite, so the only invariant
    vector is `|c>`.
* **Scope.** `fg-simple-kazhdan-groups-are-surjunctive` and
  `finitely-generated-simple-groups-are-surjunctive` are open. Every route
  into the goal through them needs one of the two.

## 19. The compression mechanism in the rank metric (gk-kdf-structure)

Reviewed: `rank-row-compression-audit-2026-09-12.md` (`c7c0f91ee3`), with
`rank-ultraproduct-compressors-conserve-fixed-right-ideals` and
`leavitt-rank-models-kazhdan-fixed-ideals-are-global`. Verdict: PASS, with one
justification strengthened forward.

* **Lemma 1.**
  * (R2) for each `s` gives
    `codim(W_i ∩ K_i(S) in W_i) <= sum_s rank((sigma_i(s) - 1) x_i)`, and
    `1 - e_i` kills `K_i(S)`.
  * The ultraproduct passage takes limits of normalized ranks.
  * Representative independence: `eM` equals the canonical set `Fix_r(sigma(Gamma))`,
    since a fixed `x` has `rk((1-e)x) = 0`. So different choices of `e_i`
    give the same right ideal.
* **Lemma 2.**
  * `g -> sigma(g^-1)^T` is an almost-homomorphism.
  * The telescoping identity bounds the rank at scale `n^m` by `sum_j rank(X_j - Y_j) n^(m-1)`.
  * Degree `(1,1)` is `Ad` under `v (x) w -> v w^T`. Its kernel is the exact
    commutant when the representatives satisfy `sigma_i(s^-1) = sigma_i(s)^-1`
    on `S`.
* **Theorem 3.**
  * `u_i K_i(S) = ∩_x ker(u_i sigma_i(x) u_i^-1 - 1)` exactly.
  * `s x s^-1 = w_x` in `Gamma`, and `w_x(sigma_i(S))` fixes `K_i(S)`.
  * (R1) applied to `A_x = w_x(sigma_i(S))` and `B_x = u_i sigma_i(x) u_i^-1`, over
    the finitely many `x in S`, gives codimension `o(n_i)`. Equal dimensions then give
    `sigma(s) eM = eM`.
  * Conjugates `g gamma g^-1` fix `eM` pointwise.
  * No property (T) is used anywhere, and none hides: the argument only counts ranks.
* **Section 2.** The linear sofic `E` with its affine Kazhdan base and doubling
  compressor satisfies Theorem 3 and has `sigma(u) != 1` for an injective `sigma`. So
  the linear-scale layer is compatible with a nontrivial defect.
* **Section 3.**
  * (M): each `sW_j` meets `W_(tau(j))` in at least `d_j - l_j` dimensions, and these
    are independent, so `sum_(tau(j)=l) d_j <= d_l + sum_(tau(j)=l) l_j`. Equal totals
    give `sum |.| <= 2 sum l_j`.
  * (C): independent subspaces add dimensions.
  * (T1): the graph `{w (x) e_1 + w (x) e_2}` meets each piece in `0`.
* **Strengthened (K) example.** The all-ones vector alone obstructs only one
  dimension. The linear obstruction is the `(x-1)`-adic filtration.
  * Write `k^n = F_2[x]/((x-1)^n)`, with `A` multiplication by `x` and `W` the
    polynomials of degree `< n/2`.
  * The invariant subspaces are the ideals `((x-1)^(n-j)) = ker(A-1)^j`, of dimension `j`.
  * A nonzero polynomial of degree `< n/2` is not divisible by `(x-1)^(n/2)`, so
    `dim(ker(A-1)^j ∩ W) = max(0, j - n/2)`.
  * So every invariant subspace `V` has `dim V + dim W - 2 dim(V ∩ W) >= n/2`, while
    `dim(W + AW) = dim W + 1`. This sentence has been added to the artifact.
* **Section 4.** `G_L = R^x` is generated by compressors and is simple, so
  `<<Gamma>> = R^x`, and Theorem 3(3) gives the constraint in every degree.

## 20. The product-trace zero-one law (gk-observables)

Reviewed: `gottschalk-product-trace-zero-one-law-2026-09-12.md`, with
`bijective-ca-preserve-uniform-bernoulli-measure`,
`injective-ca-product-trace-zero-one-law` and the converse route
`matrix-observable-extension-from-surjunctivity`. Verdict: PASS.

* **Theorem 1.**
  * `rho = sigma pi tau` moves only coordinates in `F M^-1`.
  * At those coordinates it reads `x` on `E = (F M^-1 M ∪ F) N`, which contains
    `F M^-1` because `e in M ∩ N`.
  * `r : A^E -> A^E` is injective, because configurations agreeing off `E` are
    separated by the bijection `rho`. So `rho = r x id` preserves `mu`, and
    `tau^-1(pi B) = rho(sigma B)` gives invariance of `tau_* mu` under local
    permutations.
* **Theorem 2(b).**
  * Step 5: `P e_k = 0` for commuting diagonal projections gives
    `P <= prod(I - e_k)`, and `tr` factorizes over the disjoint windows `g_k Omega`.
  * Step 6: the trace property makes the diagonal restriction invariant under
    `u_pi`, so Fact 1.1 applies.
* **(viii) <=> (ix).**
  * `Phi(O*O) - Phi(O*)Phi(O) = V*O*(I-P)OV` vanishes iff `(I-P)OP = 0`. With `O*`, the
    multiplicative domain is `{P}'`.
  * `A_G` is irreducible on `l^2(C_c)`, because local matrix units connect any two
    finite perturbations. So `P in {0, I}`; `P != 0`, and `P = I` means the image
    contains the dense set `C_c`, so `tau` is onto.
* **Reading.**
  * The matrix-observable route is an honest equivalence, encoded as a cycle.
  * Every trace-level premise is zero-one per automaton.

## 21. Bernoulli deficit witnesses localize to the sofic radical (gk-rokhlin, batch 4)

Reviewed: `bernoulli-deficit-witness-localization-2026-09-12.md` (landing `da45b697b7`),
`sofic-radical-localizes-bernoulli-deficit-witnesses` with its `-proof` route, the open claim
`bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`, and the route
`rokhlin-maximality-via-fg-simple-kazhdan-hosts`. Verdict: PASS.

* **Degenerate cases.**
  * With `F` empty, `Phi >= log q` directly.
  * With `D` empty, `P = {1}`, so `k Phi = H(x(1))`. If `E` is empty as well, `psi` is
    constant and `Phi = log q`.
* **Step 1, product amplification.**
  * Negating invisibility, with `F'` fixed, gives for each `d in D` and every `delta` a model
    moving `d` at a fraction `> eps_d`.
  * Replicating to a common size and taking the disjoint union keeps the defect `<= delta`,
    and moves each `d` at a fraction `> eps_0/|D|`.
  * The `r`-fold product has defect `<= r delta`, since product permutations differ on at most
    the union of the coordinate disagreements. It fixes at most `(1 - eps_0/|D|)^r`.
* **Step 2, good points.**
  * `(v.a).b = v.(ab)` iff `phi(ab) w = phi(a)phi(b) w` with `w = phi(ab)^-1 v`. So the
    failures number at most `r delta |V|` per pair.
  * `v.p = v.p'` iff `phi(p^-1 p')` fixes `v.p`, and `v -> v.p` is a bijection.
  * `E^-1 E \ {1}` lies in `D` because `F` is nonempty.
* **Step 3, the entropy count.**
  * `k|V| log q = H(Z) + H(x|Z)`. On `U_E` the tuple is iid, so `H(Z_u) = H(psi(x|_E))`.
  * On `U_P` the chart is injective and `Z_(v.f) = psi((x(v.(fe)))_e)`. Coincidences
    `fe = f'e'` in `G` give the same point, so the joint law equals the law in `G`.
  * The error terms vanish as `r -> infinity` and then `delta -> 0`.
  * No sofic entropy theory enters. The lower-bound half of Theorem 3 converts "no witness"
    into maximality, so sofic groups are maximal.
* **Corollaries 3--4.**
  * A homomorphism to a sofic group composes with sofic approximations, so `Rad(G) <= ker pi`.
  * A simple nonsofic group has `Rad = G`.
* **Proposition 5 and heredity.** Maximality at `q` is equivalent to INF by Seward
  Theorem 1.10. It passes from a group to its subgroups: `h^Rok_G(L^G) <= h^Rok_H(L^H) <= log|L|`.
  The container embeds `C` into the host `G`, so the direction is right: maximality on hosts
  gives maximality on every countable `C`. The route's open prerequisite is ergodic-theoretic,
  so the route is a reduction, not a restatement.

## 22. Linear-scale rank conservation cannot kill defects (gk-kdf-structure, calibration)

Reviewed: `linear-scale-rank-conservation-does-not-kill-defects` and its route
`linear-scale-conservation-defect-witness-proof` (landing `af7bedd402`). Verdict: PASS.

* `E` is sofic, hence linear sofic over every field, so an injective `sigma : E -> M^x` exists.
* `u = [t c t^-1, v_1]` normally generates the MF radical, which contains the nontrivial central
  involution, so `u != 1`.
* `<Gamma, t>` is generated by compressors of `Gamma`, so Theorem 3 of Section 19 applies in
  every degree.
* The compressor group `<Gamma, t>` has the stable letter's `Z` as a quotient, so it is not
  Kazhdan. This agrees with the reading that a rank-row proof needs property (T) of the
  compressor group below linear scale.

## 23. The ternary split at the central involution (gk-invariant-output): one conclusion corrected

Reviewed: Sections 6--8 of `invariant-output-descent-and-sensitivity-2026-09-12.md` (landings
`faf9c127d2`, `aad8009fa`), `ternary-leavitt-swap-problem-splits-at-central-involution` with its
proof route, `ternary-swap-fullness-projects-to-scalar-quotient` and
`projective-swap-corner-gives-strict-automaton`. Verdict: parts 1--5 PASS. The conclusion of
Proposition 7.4(d) FAILS and has been corrected forward.

* **Lemma 7.1.** `(2(1 +- z))^2 = 8(1 +- z) = 2(1 +- z)`, the sum is `4 = 1`, and the product is
  `4(1 - z^2) = 0`. `S_+ ~= F_3[PG]`.
* **Lemma 7.2.** `d^2 = 1`, `d w = s0 t1 - s1 t0` and `(d w) d = -w`. On `S_-`,
  `[d] e_- [d] = 2 eps_-(1 - [w]) = eps_- - e_-`. The matrix units give `S_- ~= M_2(T)`. A
  commutative image would give `E_11 = E_22`, forcing `1 = 0`.
* **Proposition 7.3.** `c E_11 b = I` is a column times a row, which is `gamma_i beta_j = delta_ij`.
* **7.4(a)--(c).**
  * `pi(eps_+) = 0`.
  * Multiplying by `eps_+` projects the equation.
  * Over `PG`, `tau_c tau_(ebar b) = id` and the output is right-`<wbar>`-invariant, so every
    `y` with `y(1) != y(wbar)` is missed.
* **7.4(d) fails.** Its facts hold, but its conclusion does not. It says a solution in `S_-` gives
  at most a self-map of a proper subshift and carries no surjunctivity content. In fact:
  * `F_3^G = X_+ (+) X_-`, with projections `tau_(eps_+)` and `tau_(eps_-)`.
  * From `c e_- b = eps_-`, `A = e_- b + eps_+` and `C = c + eps_+` satisfy `CA = 1` and
    `AC != 1`. An idempotent with a right inverse equals the unit, and `e_- != eps_-` because
    `1, [w], [z], [zw]` are distinct.
  * So `F_3[G]` is not directly finite, and `tau_A`, the identity on `X_+` plus the strict map on
    `X_-`, is injective and not surjective on the full shift.
  * `subshift-self-embedding-carries-no-surjunctivity-content` is about subshifts with no linear
    complement, and `X_-` has one.
  * By Corollary 8.2 of the same artifact (`g -> s0 g t0 + s1 t1` embeds `G` in `PG`), `PG` is not
    surjunctive either.
* **Section 8.** `iota` is multiplicative, and `t0 iota(g) s0 = g`. `iota(g) = lambda` forces
  `lambda s1 = s1`, hence `lambda = 1`. Lemma 8.3 holds, since `Ad(g)` fixes `1`, while
  `b'(1) = 1 + w`. Proposition 8.4 was not reviewed.
* **Design consequence.** Both halves suffice. The Leavitt-visible half `S_-`, where the image
  equation holds in `R`, is a counterexample target, not a dead end.
* **Landed forward.**
  * Correction 7.4(e) in the artifact, and the corrected item and summary on the split claim.
  * The corrected Attempts bullet on `ternary-leavitt-swap-idempotent-is-full`.
  * The open claim `ternary-anti-invariant-swap-corner-is-full`.
  * The routes `anti-invariant-swap-corner-refutes-ternary-surjunctivity`,
    `ternary-swap-fullness-projects-to-anti-invariant-half` and
    `projective-swap-corner-refutes-ternary-surjunctivity`.

## 24. The scalar quotient, the Klein target and zero Rokhlin supremum (gk-invariant-output, gk-rokhlin)

Reviewed on main at `5edf273bee`.
* Landing `aad8009fa`: `leavitt-units-embed-in-their-scalar-quotient`,
  `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`,
  `ternary-unit-nonsurjunctivity-ascends-to-scalar-quotient`,
  `projective-ternary-klein-idempotent-is-full` and `klein-fullness-gives-swap-fullness`.
* Landing `10d9b0bf1`: `leavitt-units-have-zero-rokhlin-entropy-supremum` and
  `leavitt-zero-rokhlin-supremum-from-strict-automaton`.
* The SHA `ee05d55a60` in the lead's queue is the HS profile-rounding commit. The Klein claim
  landed in `aad8009fa`.

Verdict: PASS, with one gap in the refuted_by wiring, now fixed.

* **Corner embedding, over every field.**
  * `iota(g) iota(h) = s0 g h t0 + s1 t1`, because `t0 s1 = t1 s0 = 0`.
  * `t0 iota(g) s0 = g`.
  * `iota(g) = lambda` gives `lambda s1 = s1`, so `lambda = 1` by `t1 s1 = 1`.
  * Neither finiteness of `k` nor its characteristic is used.
* **Nonsoficity of `L_k(1,2)^x / k^x`.**
  * `units_not_isSofic` in `Leavitt/AryEndpoints` holds for every nontrivial countable algebra
    over a finite field that carries a `d`-ary family. So it applies to `A = L_(F_3)(1,2)`
    itself, which is countable, nontrivial and carries the binary family, independently of the
    universal presentation built in the development.
  * Subgroups of sofic groups are sofic.
  * Ascent of nonsurjunctivity from the unit group to `PG` is subgroup heredity along the same
    embedding.
* **Klein operators.** Write `R ~= M_2(R)` with `r = sum s_i a_ij t_j`, `d = diag(1,-1)`, and `w`
  the swap.
  * `2(1 + Ad d)` deletes the off-diagonal entries, and `2(1 + Ad w)` sends `diag(a, b)` to
    `2(a + b) I`. So `rho(e_K) = delta Psi`, with `a_ii = t_i r s_i`.
  * `Psi delta(r) = 2(r + r) = r`.
  * `Ad(w)` fixes `delta(x) = diag(x, x)`, so `rho(ebar) delta = delta`.
  * `delta(1) = Psi(1) = 1`, and `Ad(g)(1) = 1` gives `T(1) = eps(T) 1` on the image.
  * `wbar` and `dbar` commute in `PG`, because `d w = -w d`.
  * `klein-fullness-gives-swap-fullness` holds: `ebar e_K = e_K ebar = e_K`, so `c e_K b = 1`
    gives `(c e_K) ebar (e_K b) = 1`.
  * The refuted_by direction on the Klein claim is right.
* **No single conjugation, in scope.**
  * Put `a = t0 g` and `b = g^-1 s0`. If `a r b = r` for all `r`, then `ab = 1`, then `a r' = r' a`
    for all `r'`. So `a` is central, `a = lambda in F_3^x`.
  * In the coordinates `R ~= R (+) R`, `g x = (lambda x, t1 g x)` misses `(0, y)`, so `g` is not a
    unit.
  * This excludes splittings of the shape `t0 Ad(g)(.) s0` only, and the claim should be read in
    that scope.
* **Zero Rokhlin supremum.**
  * The three forms agree. POS gives `h_sup > 0` (Seward 7.7), and Seward 1.10 gives
    `h^Rok(A^U) = min(log|A|, h_sup)`. A deficit makes `h_sup` finite. Since `U` contains
    `U x U` and `GL_(2^n)(F_2)`, the self-copy dichotomy then forces `h_sup = 0`.
  * By Theorem 3, a deficit at some amplification is equivalent to a configuration with
    `Phi < log q`.
  * The certificate is finite. Its incidence pattern is decided through the decidable word
    problem. Its inequality is strict between finite sums of `p log p` with rational `p`, which
    interval arithmetic certifies.
  * The route from `leavitt-unit-group-nonsurjunctive` is the contrapositive of part 3 of the
    established Leavitt entropy claim.
* **Refuted_by wiring.**
  * `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups` and
    `bernoulli-rokhlin-entropy-maximal-for-every-group` correctly carry
    `refuted_by: leavitt-units-have-zero-rokhlin-entropy-supremum`: `U` is finitely generated,
    infinite, simple and Kazhdan.
  * The exact negation pair was not wired: `leavitt-unit-group-has-positive-rokhlin-entropy-action`
    listed only `leavitt-unit-group-nonsurjunctive`. I added
    `leavitt-units-have-zero-rokhlin-entropy-supremum` there, and the symmetric
    `refuted_by: [leavitt-unit-group-has-positive-rokhlin-entropy-action]` on the zero-supremum
    claim, following the surjunctive/nonsurjunctive pair.
* **Container reduction** (`a03dd1b0c8`): passed already in Section 18. Its trust surfaces are
  Schupp, Hull 7.1, 5.7, 3.5 and 5.8, Osin 7.1, and Dahmani--Guirardel--Osin.

## 25. Property (T) does not round in normalized rank (gk-kdf-structure)

Reviewed: `kazhdan-rank-rounding-counterexample-2026-09-12.md` (landing `5edf273bee`),
`kazhdan-group-rank-models-admit-no-expander-decomposition` and
`kazhdan-rank-ultraproducts-can-have-diffuse-commutants`, with their proof routes. Verdict:
PASS. Two statement scopes were tightened forward.

* **(T) input.** `controlSet_isKazhdanPair` in `PropertyT/FiniteFieldElementaryPropertyT`
  quantifies over any `X` with `[Fintype X]` and any finite field `K`. With `X` a one-point
  type, `FreeAlgebra F_2 X ~= F_2[t]`, and the control set is
  `{1} ∪ {e_ij(1), e_ij(t)}`: the scalar `0` contributes the identity, which is harmless. The
  theorem is stated for real orthogonal representations, and property (T) over `R` and over
  `C` agree. The counterexample uses only that `Gamma` is Kazhdan, never the constant.
* **Lemma 1.1.** `F_2[t] -> F_q` is onto, so `rho_k` hits the elementary generators of
  `EL_3(F_q) = SL_3(F_q)`. Transitivity on nonzero vectors kills every proper nonzero
  invariant `F_2`-subspace. Images and kernels of commutant idempotents are invariant.
* **Lemma 1.2.** `e_g(X) = d(X, gX)/2` with the triangle inequality and `d(gX, ghX) = d(X, hX)`.
  For intersections, `(X ∩ Y) ∩ s(X ∩ Y) = (X ∩ Y ∩ sX) ∩ (X ∩ Y ∩ sY)`, and codimensions add.
* **Lemma 1.3.**
  * `(pi_m C - C pi_m)(alpha^l)` is nonzero only at `l = m-1` (`-alpha^m`) and `l = k-1`
    (`pi_m(alpha^k)`), so the rank is `<= 2`.
  * `s = e_ij(t)` is an involution in characteristic two.
  * `x in W_m` has `s x in W_m` iff `alpha x_j in S_m` iff the `alpha^(m-1)`-coefficient of
    `x_j` vanishes, valid because `alpha^m` is a basis vector for `m <= k-1`. So the
    codimension is `<= 1`. Six of the twelve generators move `W_m`, so `b(W_m) <= 6`.
* **Theorem 2.1.** `d(W_m, 0) = 3m` and `d(W_m, N) = 3k - 3m`, so for `m = floor(k/2)` the
  distance is `>= (n-3)/2`, and `b/dim W_m <= 2/floor(k/2)`.
* **Remark 2.2.**
  * `pi(s)Ppi(s)* - P` vanishes on `(W ∩ sW) (+) (W + sW)^perp`, which has codimension
    `2 e_s(W)`, and its norm is `<= 1`.
  * `||xi||_HS^2 = dim W (1 - dim W/n)`.
  * Schur and the Kazhdan inequality on the orthocomplement of the scalars give
    `2 e_s >= kappa^2 dim W/2` for some `s`.
* **Theorem 3.1(1).**
  * `b(P) >= 1` for proper nonzero `P`.
  * The steps `U_(m+1)/U_m -> W_(m+1)/W_m` have dimension `<= 3`, so the largest `m` with
    `dim U_m <= p/2` has `dim U_m > p/2 - 3`, and `b(U_m) <= b(P) + 6`.
  * For `p >= 8`: `p < (2b + 12)/kappa + 6 <= (8b + 12)/kappa <= 20b/kappa`, using `b >= 1`
    and `kappa <= 1`. For `p < 8`: `p < 8b <= 20b/kappa`.
* **Scope tightened (claim item 4 and Theorem 3.1(2)).** "Expanding pieces have total dimension
  `< 20 Lambda/kappa`" and "`lambda > kappa/21`" need `N` not to be an expanding piece. That
  holds once `3 floor(k/2) kappa > 6`. For small `k` the decomposition `{N}` with `N` expanding
  has `Lambda = 0`, and both statements fail. "Linear-size pieces stay non-expanding under
  perturbation" needs the leakage hypothesis `b'(P) = o(n)` of Theorem 3.1(3). Both were added
  to the claim, and the first to the artifact.
* **Theorem 3.1(3).**
  * On `ker(rho'(s) - rho(s)) ∩ X` the two maps agree, so `d(rho X, rho' X) <= 2 delta n` and
    `|e'_s - e_s| <= delta n`.
  * With twelve generators, `b'(U) <= b'(P) + 24 delta n + 6`, and expansion of a linear-size
    piece contradicts this for large `k`.
* **Theorem 4.1.**
  * `rank [pi_(m_k) (x) 1, rho_k(s)] <= 2 = o(3k)` puts `p_beta` in the relative commutant, and
    the projections are nested.
  * No atoms: representatives `V_k` of an invariant right ideal have `b(V_k) = o(k)`. Then
    `V_k ∩ W_m` have boundary `<= b(V_k) + 6` and dimension steps `<= 3`. An `o(k)`-boundary
    subspace inside `V_k` defines an invariant right ideal inside `eM` of the chosen rank.
* **Remark 4.2** follows from the uniform spectral gap in `l^2(X_k)` and on `HS` minus scalars.
* **Section 5.** `x_l -> alpha` sends every `e_ij(x_l)` to `e_ij(alpha)`. Every `EL_r(F_q)` is
  transitive, the bound becomes `b <= r(r-1)d`, and the steps are `r`.

## 9. Trust surfaces not verified here

* Kun--Thom, arXiv:2608.06222v3, Theorems A and E: the statements were read by
  `review-surjunctive`; the proofs were not checked.
* Finite presentation of `St_n(R)` for `n >= 4`
  (`steinberg-finite-presentation-and-kazhdan-theorem`).
* van der Kallen's injective stability and Bass's fundamental theorem.
* Green's graph-product theorems, and Lawton's theorem that residually finite
  groups are surjunctive.
* The proof of `sofic-groups-kill-rigid-compression-defects`.
