# Linear-lift family: independent verification record

Lane `gk-vf-linear`, 2026-09-12. This lane is the verifier for the linear-lift family. Every item below
was re-derived from the statements and the Leavitt relations `t_i s_j = delta_ij`, `s0 t0 + s1 t1 = 1`.
None was checked by rereading the author's argument.

Conventions: `R = L_(F_3)(1,2)`, `G = R^x`, `S = F_3[G]`, `z = -1`, `eps_(+-) = 2(1 +- [z])`,
`w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`, `e = 2(1 + [w])`, `e_- = eps_- e`. All arithmetic is mod 3.

## 1. Swap-separated reformulation of the anti-central corner: PASS

Items checked: artifact `ternary-swap-separated-pairs-2026-09-12.md`, Theorem 1 and Corollary 2;
the routes `swap-separated-pair-gives-anti-invariant-corner` and
`anti-invariant-corner-gives-swap-separated-pair`; the claim
`ternary-twisted-algebra-has-swap-separated-one-sided-pair`.

**Basic identities.**
- `eps_+^2 = 4(2 + 2[z]) = eps_+`, `eps_+ + eps_- = 4 = 1`, `eps_+ eps_- = 4(1 - [z]^2) = 0`, and
  `[z] eps_- = -eps_-`.
- `w^2 = s0 t1 s1 t0 + s1 t0 s0 t1 = s0 t0 + s1 t1 = 1`, and `d^2 = s0 t0 + s1 t1 = 1`.
- `d w = s0 t1 - s1 t0` and `w d = -s0 t1 + s1 t0 = -(d w)`. So `d w d = -w = z w`, and `w d = d z w`.
- `e^2 = 4(2 + 2[w]) = e`. Also `[d] e_- [d] = eps_- 2(1 + [z][w]) = eps_-(2 - 2[w]) = eps_-(2 + [w])`,
  and `eps_- - e_- = eps_-(1 - 2 - 2[w]) = eps_-(2 + [w])`. The two agree.
- Hence `e_- [d] e_- = e_- (eps_- - e_-) [d] = 0`, and `[w] e_- = e_-`.

**(P) => (C).** Take `c' = c(1 + [w])` and `b = a`. Then
`c' e_- b = 2 c (1 + [w])^2 a = 4 c (1 + [w]) a = c a + c [w] a = eps_-`.

**(C) => (P).** Take `b' = e_- b`, `c'' = c e_-`, `a = 2(b' + [d] b')` and `chat = c'' + c''[d]`.
- Both cross terms equal `c'' [d] b' = c e_- [d] e_- b = 0`. So `chat a = 2 . 2 c'' b' = eps_-`.
- `[w][d] b' = [d][z][w] b' = -[d] b'`, because `[z]` acts as `-1` on `S_-` and `[w] b' = b'`.
  So `[w] a = 2(b' - [d] b')`, and `chat [w] a = 2(c'' b' - c'' [d][d] b') = 0`.
- `a` and `chat` lie in `S_-`, because `[d]` commutes with the central `eps_-`.

**(P) <=> (E).**
- `p = a c` is idempotent and equivalent to `eps_-`, and `p [w] p = a (c [w] a) c = 0`.
- Conversely, take an equivalence `c a = eps_-`, `a c = p`. Then `c = c p` and `a = p a`, so
  `c [w] a = c p [w] p a = 0`.

**(X) => (P).** With `m = c[w]a`, `c[w][w]a = c a = eps_-`, and `u = (eps_- - m^2)^(-1)` in `S_-`,
put `c' = u(c - m c[w])`. Then `c' a = u(eps_- - m^2) = eps_-` and
`c' [w] a = u(m - m eps_-) = 0`. A nilpotent `m` makes `eps_- - m^2` a unit by the geometric
series, which is Corollary 2.

**Section 2 claims.**
- In `R`, `w s0 = s1`, so `t0 w s0 = t0 s1 = 0`, and `(s0, t0)` satisfies (P).
- Right translation `(a[g], [g^-1]c)` preserves (P) because `eps_-` is central. Left translation by
  `h` in `C_G(w)` preserves it too.
- Augmentation gives `eps(c) eps(a) = 1` and `eps(c) eps(a) = 0` in any algebra with a unital map
  to a field. So (P) is impossible in `F_3[PG]`.
- `S_- ~= M_2(T)` because `e_-` and `eps_- - e_-` are conjugate by `[d]`. A unital map
  `M_2(T) -> k` into a commutative ring sends the diagonal units to equal orthogonal idempotents
  summing to 1, which forces `1 = 0`. So `S_-` admits no such map.

**Scope: finite-dimensional representations.**
- `G` has no nontrivial finite-dimensional representations: its image would be finitely generated
  linear, hence residually finite.
- `G` has no nontrivial finite quotient. A finite-index normal `N` maps onto `PG` or into `{±1}`.
  Simplicity of `PG` and perfectness of `G` then force `G/N = 1`.
- So every such representation of `S` factors through augmentation on `S_+` and kills `S_-`, as the
  artifact says.

Verdict: exact. Theorem 1 is an equivalence of statements, and the claim stays OPEN.

## 2. Direct-product splitting (correction e2dcdae9b): PASS, second independent derivation

Item checked: route `anti-invariant-swap-corner-refutes-ternary-surjunctivity`.

From `c e_- b = eps_-` with `b, c` in `S_-`, put `A = e_- b + eps_+` and `C = c + eps_+`.
- Since `c eps_+ = 0`, `eps_+ e_- = 0` and `eps_+^2 = eps_+`, we get `CA = eps_- + eps_+ = 1`.
- `AC = e_- b c + eps_+`. If `AC = 1`, then `e_- (bc) = eps_-`, so `e_- = e_- e_- (bc) = eps_-`.
- But `eps_- - e_- = eps_-(1 + 2[w]) = 2(1 + 2[w] - [z] - 2[zw])`. Its coefficients are nonzero on
  the four distinct elements `1, w, z, zw`. These are distinct because `w s0 = s1` is neither `s0`
  nor `-s0`.
- So `F_3[G]` is not directly finite, and `stable-finiteness-failure-refutes-surjunctivity` gives an
  injective, non-surjective linear automaton on the full shift `F_3^G`.

Statement fidelity: this is the full shift over `G`, not a subshift. The automaton is the identity
on the invariant summand and strict on the anti-invariant one, and both summands are linear direct
summands of `F_3^G`.

The companion routes `projective-swap-corner-refutes-ternary-surjunctivity` and
`ternary-swap-fullness-projects-to-anti-invariant-half` also pass:
- in `F_3[PG]`, `ebar = eps_+` forces `wbar = 1`, which is false;
- multiplying by the central idempotent `eps_-` projects the unit-group equation onto `S_-`.

**One-decidable-host rule.** A solution is a finite identity in `F_3[G]`, and `G` has a decidable
word problem. So a certificate is checkable in one host, and no surjunctive quotient is used.

## 3. F_3-linear soficity gate (cd4162f9b): PASS

Items checked: routes `f3-linear-soficity-refutes-projective-swap-fullness` and
`non-linear-sofic-via-projective-ternary-swap-fullness`, and the claims
`projective-ternary-group-is-f3-linear-sofic` and `projective-ternary-swap-idempotent-is-not-full`.

- `c ebar b = 1` gives `y x = 1` with `x = ebar b` and `y = c`.
  - If `x y = 1`, then `ebar` is right invertible, so `ebar = 1` and `wbar = 1`, which is false.
  - So `F_3[PG]` is not directly finite.
  - Linear sofic groups over `F_3` have stably finite group algebras
    (`linear-sofic-group-algebra-is-stably-finite`), which contradicts the gate.
- A non-directly-finite pair in `F_3[PG]` stays one in `F[PG]` for every field `F` containing
  `F_3`. It also lives in `F_3[H]`, where `H` is generated by the supports of `b`, `c` and
  `wbar`. So the contrapositive route and its localization remark are sound.
- The payoff paragraph is sound:
  - linear soficity passes to subgroups, and `G` embeds in `PG`;
  - a stably finite `S = S_+ x S_-` has no one-sided pair in either factor, because padding by the
    other factor's unit gives a pair in `S`.
- The claim correctly declines to assert that linear soficity descends to `PG` from `G`.

## 4. Scope of the s0-lift search records (b1418d097, 4cd7be203): PASS as scoped

Item checked: node `left-invertible-lift-of-s0-in-leavitt-group-algebra`.
- **Span bound.** A lift `a` with `pi(a) = s0` and `supp a` in `B_r` puts `s0` in
  `span pi(B_r)`. So "`s0` is not in `span pi(B_2)`" gives radius at least 3 over the atlas-chart
  generators, exactly as stated. The Gaussian elimination itself was not recomputed here, since
  this lane runs no heavy compute.
- **Two-sided mode.** The node correctly says that imposing `pi(b) = t0` restricts the search
  rather than deciding the one-sided instances.
- **UNSAT verdicts.** The node correctly records them as solver outputs without proof logs,
  excluding only the searched support pairs.
- No overstatement found.

## 5. Routes into the binary direct-finiteness roots: PASS

Items checked: `leavitt-direct-finiteness-from-both-lifting-problems-failing`,
`leavitt-direct-finiteness-from-f2-linear-soficity` and
`kaplansky-failure-from-invisible-kernel-defect`.

- **Both lifting problems failing.** The established normal-form claim
  `leavitt-inverse-defects-are-visible-or-invisible` says every one-sided pair of `F_2[R^x]` has a
  group-element translate over `(s0, t0)` or over `(1, 1)`. A pair over `(s0, t0)` gives a
  left-invertible lift of `s0`, and a pair over `(1, 1)` lies in `F_2 1 + ker pi`. So the two negated
  prerequisites exclude every pair, and the route is valid.
- **Linear soficity.** Linear soficity over `F_2` gives stable finiteness at every size, and at
  `n = 1` that is direct finiteness. The route is valid.
- **Invisible defect.** `F_2 1 + ker pi` is a unital subring with the same identity, so a one-sided
  pair there is one in `F_2[R^x]`. The route is valid.

## 6. No unital rank model of the Leavitt algebra (973727ddf): PASS, with one scope remark

Items checked: `leavitt-algebra-has-no-unital-rank-model` and its proof route.

- **The rank ultraproduct is directly finite.** For square matrices over a field, `v -> bv` maps
  `ker(1 - ab)` injectively into `ker(1 - ba)`: if `v = abv` then `(1 - ba)bv = 0`, and `bv = 0`
  forces `v = abv = 0`. By symmetry the nullities agree, so the ranks agree, and `ab = 1` implies
  `ba = 1` modulo rank-null sequences. The same computation shows that every corner `pMp`, with `p`
  idempotent, is directly finite:
  `rk(1 - ab) = rk(1 - p) + rk(p - ab)` for `a, b` in `pMp`.
- **Injectivity and contradiction.** `R` is simple, so a nonzero homomorphism is injective, and
  `t0 s0 = 1 != s0 t0` gives the contradiction.
- **Scope remark on the consequence paragraph.** The Steinberg relations
  `e_ij(a) e_ij(b) = e_ij(a + b)` and `[e_12(a), e_23(b)] = e_13(ab)` force approximate additivity
  and multiplicativity of `phi`. They do not force `phi(1) = 1`. The conclusion survives without
  unitality:
  - `p = phi(1)` is an idempotent of `M`, and `phi` is a unital homomorphism `R -> pMp`;
  - that corner is directly finite, and `phi != 0` makes `phi` injective;
  - so the elementary-matrix construction is dead for every nonzero, possibly non-unital, `phi`.
  The node's conclusion stands.
- **Wording.** "Over any field `F`" should be read for ring homomorphisms. `R` has characteristic
  two, so a unital homomorphism into a nonzero algebra forces characteristic two. The claim is
  vacuously true in other characteristics, and nothing depends on the wording.

## 7. Torsion-free host constraints (de231f8c9): PASS

Items checked:
- `leavitt-tower-does-not-embed-in-torsion-free-hosts`;
- `invariant-output-injective-ca-need-torsion`;
- `torsion-free-scalar-df-failure-gives-exotic-idempotents`, with their proof routes.

- **Involution.** `(1 + s0 t1)^2 = 1 + 2 s0 t1 + s0 (t1 s0) t1 = 1` over `F_2`, and `s0 t1 != 0`.
  Every member of the tower `V <= R^x <= A^x` contains an element of order two. `V` contains the
  finite symmetric groups.
- **Invariant output forces a finite symmetry group.**
  - `F(x)(gH) = tau(x)(g)` is well defined by invariance and continuous.
  - It is equivariant for the left action: `F(gamma x)(gH) = tau(x)(gamma^-1 g) = (gamma F(x))(gH)`.
  - The established constancy lemma for coset shifts with infinite stabilizers makes `F` constant
    when `H` is infinite. That contradicts injectivity when `|A| >= 2`.
- **Exotic idempotents.** `e = alpha beta` satisfies `e^2 = alpha (beta alpha) beta = e` and
  `e != 1`. It is also nonzero, because `beta e alpha = 1`. So a scalar one-sided pair in `k[G]`
  exhibits a nontrivial idempotent and zero divisors.

## 8. Ternary anti-central kernel normal forms (ab42f3cff, lane gk-l3-kernel): PASS

Items checked: `ternary-anti-central-kernel-has-klein-idempotents`,
`ternary-anti-central-pairs-visible-or-invisible` and
`ternary-anti-central-failures-transfer-into-kernel-corners`, with their proof routes. The
pressure points (1) to (4) were each re-derived.

- **Klein idempotent.** `h1 = s0 t0 - s1 t1` and `h2 = -q_00 - q_01 + q_10 - q_11` are ±1
  combinations of the orthogonal cylinder idempotents `q_gamma` (`|gamma| = 2`), so they are
  commuting involutions. The sign patterns on `(q_00, q_01, q_10, q_11)` are `(++++)` for 1,
  `(++--)` for `h1`, `(--+-)` for `h2` and `(---+)` for `h1 h2`. None is `(----) = z`, so `|H| = 4`
  and `z` is not in `H`.
  - `E^2 = 4E = E`.
  - `pi(E) = (1 + h1)(1 + h2) = (2q_00 + 2q_01)(2q_10) = 0`.
  - `q = 2(E - [z]E)` has coefficient 2 on `[1]`, because `[z]E` is supported on `zH`, which misses
    1. So `q != 0` and `tau(q) = 2`.
  - Side check: over `F_3`, `g = 1 + s0 t1` has order 3, and `n = (1 - [g])^2` satisfies
    `n^2 = (1 - [g^3])(1 - [g]) = 0`. So the binary kernel idempotent really does become nilpotent.
- **Visibility, Theorem 2.** `pi(p) y' pi(p) = 1` forces `pi(p) = 1`. `pi(e_-) = 2(1 + w) != 1`,
  since otherwise `w = 1`. For a separated pair, `pi(p) = 1` would force `pi(w) = 0`. Both hold.
- **Orbit theorem over `F_3`.** In Lemma 1 of the binary normal-form artifact, the only change is
  that `y = sum c_alpha S[alpha]` with `c_alpha` in `{1, 2}`. Then
  `T[w] T[alpha*] x S[gamma] S[w] = c_(alpha*)`, a nonzero scalar, and one divides by it. Lemma 2
  and Theorem 3 use only the Leavitt relations and module isomorphisms, with no characteristic.
  - The involution `1 + s0 gamma t1` becomes the unit `v = 1 + s0 gamma t1` with inverse
    `1 - s0 gamma t1`, because `t1 s0 = 0`.
  - `v s0 = s0`, and `(t0 + gamma t1)(1 - s0 gamma t1) = t0`.
  - The translates `[v] a` and `c [v^-1]` preserve `c a = eps_-`.
- **Dichotomy.** Translation by `[w]` or `[r]` fixes `ca` and conjugates `ac`, and `eps_-` is
  central, so `a'c' != eps_-`. The images `s0, t0` in (V3) and `1, 1` in (I3) follow from 3.1 and
  from `pi(c) = pi(a)^-1`.
- **Trace.** `tau(delta) = tau(eps_-) - tau(ca) = 0 != 2`, and equivalent idempotents have equal
  trace.
- **Kernel-corner transfer, Theorem 4.**
  - `delta4(g) delta4(g') = sum_gamma S[gamma] g g' T[gamma]` and `delta4(1) = sum q_gamma = 1`, so
    `delta4` is a homomorphism. `T[00] delta4(g) S[00] = g`, so it is injective.
  - For `h = sum lambda(gamma) q_gamma`, `q_gamma S[gamma'] = delta_(gamma gamma') S[gamma]` gives
    `h delta4(g) = delta4(g) h`. So `E` commutes with `delta4_*(S)`, and `mu` is multiplicative.
  - `delta4(-1) = -1`, so `mu(eps_-) = q`, and `pi mu = 0`.
  - Injectivity: `delta4(x)` in `H` gives `x = T[gamma] delta4(x) S[gamma] = lambda(gamma)`, a
    scalar, which is 1 since `-1` is not in `H`. So the products `delta4(g) h` are distinct group
    elements.
  - The padded pair: `CA = (eps_- - q) + mu(ca) = eps_-`, and
    `AC = (eps_- - q) + mu(ac) != eps_-` by injectivity. Both `A - eps_-` and `C - eps_-` lie in
    `K_-`.
- **Corollary 4a.** `K_-^+` is a unital subring of `S_-` with the same identity. A separated pair
  has `ac != eps_-`, because `eps_- [w] eps_- != 0`. The equivalences hold.

## 9. Scalar-character splitting and the cyclic twist (22e71610d, lane gk-lp-hosts): PASS, one scope remark

Items checked: `leavitt-unit-group-algebras-split-over-scalar-characters` and
`cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`, with their proof routes.

- **Splitting.**
  - `Z = F_q^x . 1` is central of order `q - 1`, which is prime to `p`, and `F_q^x` contains the
    `(q-1)`-th roots of unity. Character orthogonality then gives central orthogonal idempotents
    `eps_chi`, summing to 1, with `[lambda] eps_chi = chi(lambda) eps_chi`.
  - `pi(eps_chi) = delta_(chi, iota)`.
  - On `A_iota`, `[zeta^k]` acts as `zeta^k`, which is pressure point 1.
  - The padding gives `CA' = 1 != A'C`.
  - `sum_(lambda in F_q^x) lambda^-1 = 0` for `q > 2`, so the augmentation kills `A_iota`.
- **Permutation units.**
  - `u_sigma u_tau = u_(sigma tau)`, and `t_(sigma(i)) u_sigma s_i = 1` gives injectivity.
  - `u_sigma b = b` and `c b = (1/m) m = 1` need `p` not dividing `m`, which transitivity supplies.
  - The `m`-ary families come from substituting `s_k -> s_k s_1, ..., s_k s_d`, and the relations
    check.
  - In characteristic two, `pi(1 + g + g^2)` is a nonzero idempotent equivalent to 1, while
    `pi(1 + g0 + g0^2) = 0`. So `g` and `g0` are not conjugate.
- **Twist.**
  - `delta g = sum_k zeta^(k+1) s_(k+1) t_k = zeta g delta`, so `[delta][g^k][delta^-1] = [zeta^k][g^k]`,
    which is `zeta^k [g^k]` on `A_iota`.
  - The `m` isotypic idempotents exist because `p` does not divide `m` and `mu_m` lies in `F_q`
    (pressure point 2). Conjugation by `[delta]` sends `psi` to `psi zeta^-1`, a single cycle, so
    they are pairwise equivalent and `A_iota ~= M_m(T)`.
  - Morita: `1 <= E_11` in `M_m(T)` iff `T^m` is a summand of `T`, iff a unital `m`-pair Cohn family
    `gamma_i beta_j = delta_ij e_1` exists.
- **Ascent.**
  - `eps_iota(q) eps_iota(q^r) = eps_iota(q^r)`, because `[lambda]` acts as `lambda` on
    `A_iota(q^r)` for `lambda` in `F_q^x`. The field ascent holds.
  - The arity and prime-field statements are scoped correctly.
- **Scope remark on Theorem 3(5).** "`pi` maps `T` onto `pi(e_H) L pi(e_H)`" needs `pi` onto. The
  recorded claim `leavitt-unit-group-algebra-surjects-onto-leavitt` proves spanning by units in
  rings carrying a *binary* Leavitt family. That covers `d = 2`. For `d >= 3`, `L_(F_q)(1,d)` has
  no unital binary family, since admissible arities are `1 + j(d-1)`, so "onto" is unrecorded
  there.
  - Nothing else depends on it. Theorem 2's image equation, Theorem 3(1) to (4), and the corner
    equivalence `pi(e_H) ~ 1` all hold without surjectivity.
  - Read (5) as "into, containing `pi(e_H) G pi(e_H)`" for `d >= 3`, or record the `d`-ary spanning
    claim. For `q = 2`, the image solution with `m = 3` holds, while the twist needs `F_4`, as the
    artifact says.

## 10. Support no-go for swap-separated pairs (10fcc9563, lane gk-kdf-structure): PASS

Items checked: artifact `ternary-swap-separated-pairs-2026-09-12.md`, Sections 3 and 4; claim
`swap-separated-pairs-avoid-finitely-represented-supports`.

- **Cross-term form.**
  - `c(1 + [w]) e_- a = 2c(1 + [w])^2 a = c(1 + [w]) a`.
  - If `u = c(1 + [w]) a` is a unit, `u^-1 c(1 + [w])` solves (C). Conversely, (C) gives the unit
    `eps_-` with `c' = 2c`.
  - `eps_- - m^2 = (eps_- - m)(eps_- + m)`, and the factors commute. So invertibility under (X)
    implies `eps_- + m` invertible, and the new form is weaker, as stated.
- **Theorem 3.**
  - `rho(eps_-) = 2(1 - (-1)) = 1` in characteristic three.
  - (1) `rho(c) rho(a) = 1` for square matrices makes `rho(a)` invertible, so `rho(c)rho(w)rho(a) = 0`
    forces `rho(w) = 0`, which is impossible.
  - (2) `rho(e_-) = 2(1 + rho(w))` must be invertible, which excludes the eigenvalue `-1`.
- **Cantor module.** With `(s_i f)(x) = f(sigma x)` on `[i]` and `(t_i f)(y) = f(iy)`:
  - `t_j s_i f = delta_ij f` and `sum_i s_i t_i f = f`;
  - `w 1 = 1`, and every Thompson element, a sum of `S[alpha] T[beta]` over a partition, fixes 1;
  - `w v_- = s0(-1) + s1(1) = -v_-` for `v_- = 1_[0] - 1_[1]`;
  - `s0 x t0 + s1 y t1` fixes `v_-`, and `s0 x t1 + s1 y t0` negates it, whenever `x` and `y` fix 1.
  So the finite orbits are `{+-1}` and `{+-v_-}`, which span one-dimensional representations with
  `z = -1`, and in the second `w = -1`.
- **Finite quotients.**
  - `zbar` is central of order two, so `2(1 - zbar) F_3[Q] != 0` carries `z = -1`.
  - If `wbar != 1`, then `x = (1 - zbar)(1 - wbar) != 0`: if `wbar = zbar` this is `2 - 2zbar`, and
    otherwise `1, zbar, wbar, zbar wbar` are distinct. `wbar x = -x`, so `w` has eigenvalue `-1`
    on that summand.
- **Summary conditions.** "`z` lies in every finite-index subgroup" follows from the normal core.
  Statement fidelity holds: supports lie in `eps_- F_3[H]` with `z, w` in `H`.

## 11. Invariant census of the anti-central summand (cca468753, lane gk-l3-obstruct): PASS

Items checked: artifact `ternary-anti-central-invariant-census-2026-09-12.md`, Theorems A, B(ii)
and C; the claims `anti-central-state-obstruction-equals-stable-finiteness`,
`ternary-anti-central-summand-has-no-finite-dimensional-images` and
`ternary-corner-witnesses-need-non-linear-sofic-support`.

- **A(a).**
  - `f = (e_- b)(c e_-)` is idempotent, `f <= e_-` and `f ~ eps_-`, so `[e_-] = u + [h]`.
  - `e_- ~ eps_- - e_-` through `[d]`, so `u = 2[e_-]`. Then `[h] = -[e_-]` is in the cone, and
    `-u = 2[h]` is in the cone. So `u <= 0` with `k = 1`, and no state exists.
- **A(b), the state criterion, proved in place.** `p(x) = inf{m/n : n x <= m u}` has these
  properties:
  - it is finite;
  - it is bounded below, since `(m + nN) u >= 0` with `m + nN <= -1` is excluded;
  - it is subadditive, by cross-multiplying the inequalities, and positively `Q`-homogeneous;
  - it vanishes on torsion, since `r t = 0 <= 0 . u`.
  Also `p(u) = 1` and `p(-u) = -1`. Hahn–Banach over `Q` with a real-valued functional below a
  sublinear `p` works by one-dimensional extension and Zorn. `p(-x) <= 0` on the cone gives
  positivity.
- **A(c).** `[Q] + k u = 0` gives `Q + S_-^k + S_-^N ~= S_-^N`. That is an isomorphism onto a proper
  summand, hence `BA = 1 != AB` in `M_N(S_-)`. Padding by `eps_+` gives the matrix failure, and the
  matrix version of `stable-finiteness-failure-refutes-surjunctivity` applies.
- **Corollary (i).** `f' = [d] f [d] <= eps_- - e_-` is orthogonal to `f`, and both are equivalent
  to `eps_-`.
- **B(ii).**
  - The normal subgroups of `G` are `1`, `<z>` and `G`: if `N<z> = G`, then
    `G = [G,G] = [N,N] <= N`.
  - A finite-dimensional image is finitely generated linear, hence residually finite.
  - `G` and `PG` are infinite with no proper finite-index normal subgroup, so the representation is
    trivial.
  - A ring homomorphism `S_- -> M_n(k)` forces characteristic three, and `z = -1` acting trivially
    on `p k^n` forces `p = 0`.
- **C.**
  - The equation lives in `F_3[H]` for `H = <z, w, supp b, supp c>`, where `e_- != eps_-`.
  - Padding gives a direct-finiteness failure of `F_3[H]`, so `H` is not `F_3`-linear sofic.
  - It follows that `H` is not sofic, not amenable, and, being finitely generated, neither residually
    finite nor linear.

## 12. No exact equivariant lift of the Leavitt isometries (f78aaf852, lane gk-l3-corner): PASS

Items checked: `self-similar-leavitt-intertwiners-have-no-exact-lift`, Section 1 of
`leavitt-self-similarity-exactness-2026-09-12.md`.

- **The endomorphisms and intertwinings.**
  - `Theta : M_2(R) -> R` is a unital isomorphism. `delta = Theta(g I_2)` and
    `iota = Theta(diag(g, 1))` are injective, since `t0 delta(g) s0 = t0 iota(g) s0 = g`.
  - `u = 1 + s0 t1 = Theta(I + E_01)` is neither scalar nor diagonal, so neither map is onto.
  - The intertwinings `delta(r) s_i = s_i r`, `t_i delta(r) = r t_i`, `iota(g) s0 = s0 g` and
    `t0 iota(g) = g t0` all follow from `t_i s_j = delta_ij`.
- **Lemma 1.1.**
  - The normal core `N` of a finite-index subgroup maps to `1` or `PG`.
  - `1` would make `G` finite.
  - Otherwise `G/N` is a quotient of the abelian `F_p^x`, and perfectness forces `N = G`.
  - Trust surface: simplicity of `PG` is imported from `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`,
    as the author says.
- **Theorem 1.2.**
  - `V[g] = sum_x v(x g^-1)[x]` and `[phi(g)]V = sum_x v(phi(g)^-1 x)[x]` give
    `v(y) = v(phi(g)^-1 y g)`.
  - `g . y = phi(g) y g^-1` is an action, since `(gh) . y = g . (h . y)`, and `v` is constant on
    orbits.
  - A finite support forces finite orbits, and then a stabilizer `{g : phi(g) = y g y^-1}` of
    finite index. That stabilizer is `G`, so `phi = Ad(y)` is onto, a contradiction.
  - The right-handed version is symmetric. The anti-central statement holds because `S_-` is a
    subset of `k[G]` and the equations are the same.

## 13. Binary kernel-corner transfer (6579f5176, lane gk-l2-invisible; canonical claims of gk-l2-visible): PASS

Items checked: artifact `leavitt-invisible-corner-transfer-2026-09-12.md`, route
`kernel-unitization-df-from-unit-group-algebra-df`, and the canonical claims
`leavitt-unit-group-algebra-embeds-in-kernel-corner` and
`leavitt-kaplansky-failures-have-invisible-witnesses`.

- **Pressure point 1.**
  - `Theta(q I_2) Theta(M) = Theta(qM) = Theta(Mq)` for `M` in `M_2(F_2)`, whose entries are central.
    So `delta(Q)` commutes with `H = Theta(GL_2(F_2)) ~= S_3`.
  - `Theta(q I_2) = Theta(M_h)` forces `M_h` scalar, hence `I_2`, because `Z(GL_2(F_2)) = 1`.
  - So `Q x H` embeds in `Q`, and `J` is injective.
- **Pressure point 2.**
  - `M_g = [[1,1],[0,1]][[1,0],[1,1]] = [[0,1],[1,1]]`, and `M_g^2 = [[1,1],[1,0]] = M_g + I_2`.
    So `I + M_g + M_g^2 = 0` and `pi(z) = 0`.
  - `e_0^2 = 3 e_0 = e_0`, and `e_0` is central because `<g>` is normal in `S_3`.
- **Pressure point 3.** `mu(a) = J(a (x) e_0)`, the tensor `a (x) e_0` is nonzero over a field, and
  `J` is injective. So `mu` is injective on all of `S`, and `mu(a) mu(b) = J(ab (x) e_0^2)`.
- **The padded pair and the equivalences.** Same computation as Section 8. `Phi(x) = delta(x) z + e`
  is unital and multiplicative because `z e = 0`, and `1 - Phi(ab) = delta(1 - ab) z` lies in `K`.
- **Pressure point 4, level one over `F_3`.** The `3'`-subgroups of `GL_2(F_3)` are 2-groups, and
  a scalar-free 2-group without fixed vectors does not exist:
  - a cyclic group of order at least 4 contains `g^2` with eigenvalues `+-i` squared, so it contains
    `-I`;
  - a Klein group of commuting reflections contains their product `-I`;
  - generalized quaternion groups contain `-I` as their unique involution;
  - a single reflection fixes a line.
  So the averaging idempotent of any scalar-free `3'`-subgroup is not killed by `rho_2`, as claimed.
  The level-two Klein constants of Section 8 avoid `-I_4`.

## 14. Block-unipotent and monomial rank models (d5e9f806b, lane gk-l-gate-pos): PASS

Items checked: `block-unipotent-rank-models-of-leavitt-el3-are-trivial` and
`monomial-rank-models-are-hamming-models`, Sections 5 and 6 of
`leavitt-unit-rank-model-construction-audit-2026-09-12.md`.

- **Block calculus.** For `X` in `e_i M e_j` and `Y` in `e_j M e_k` (`i, j, k` distinct),
  orthogonality gives `X^2 = Y^2 = YX = 0`. Expanding,
  `(1 + X)(1 + Y)(1 - X) = 1 + Y + XY`, and then `(1 + Y + XY)(1 - Y) = 1 + XY`. Also
  `psi(a) psi(b)` lies in `e_i M e_j e_i M e_j = 0`, which gives additivity.
- **Matrix units.** `u_ij u_jk = u_ik`, and `u_ji = u_jk u_ki` makes `p_i = u_ij u_ji` independent
  of `j`. `p_i u_ij = u_ij = u_ij p_j`, `p_i^2 = p_i`, and `u_ji u_ij = p_j`, so the corners have
  equal rank.
- **Support.** `psi_ij(a) = psi_ik(a) u_kj = u_ik psi_kj(a)` lies in `p_i M p_j`.
- **Corner homomorphism.**
  - `phi(a) = psi_12(a) u_21 = psi_13(a) u_31`, using `psi_12(a) = psi_13(a) u_32`.
  - `u_21 psi_13(b) = psi_23(b)` gives `phi(a) phi(b) = psi_13(ab) u_31 = phi(ab)`, and `phi(1) = p_1`.
- **Directly finite corners.** `ab = p` gives `(a + 1 - p)(b + 1 - p) = 1`, hence `ba = p`.
  - Simplicity of `L_K(1,n)` and `t0 s0 = 1 != s0 t0` force `p_1 = 0`.
  - Then `psi_ij = u_i1 phi u_1j = 0`.
- **Weyl element and scope.**
  - `sigma(w_ij) = (1 - p_i - p_j) + u_ij - u_ji`.
  - Unequal blocks `e_i` add only trivial summands.
  - The finite-stage form follows by passing to the ultraproduct.
  - The statement for `St_3` or `EL_3` over every `L_K(1,n)`, `n >= 2`, is sound.
- **Monomial models.**
  - `j(AB) = j(A) j(B)`, and both distances are left invariant.
  - For `C = B^-1 A`, `j(C)` moves exactly the points over the `m` non-fixed columns, so
    `d_H = m/N`, and `rk(C - 1) <= m`.
  - Cycle blocks give rank at least `l - 1 >= l/2` for `l >= 2`, and 1 for a relabelled fixed point.
    So `rk >= m/2`.
  - Defects at most double under `j`, and separation survives. So the permutation-type family is
    excluded for every nonsofic host.

## 15. Anti-central matrix amplification and Cohn forms (2a48f8775, 8a9cd0ebe, lane gk-l3-units): PASS

Items checked: `anti-central-ternary-summand-contains-its-matrix-ring`,
`anti-central-ternary-summand-has-no-binary-leavitt-family`, and the equivalence routes
`anti-central-cohn-family-gives-swap-corner-fullness` and
`swap-corner-fullness-gives-anti-central-cohn-family`.

- **Lemma 1.1.** `w delta(g) = s0 g t1 + s1 g t0 = delta(g) w`, and
  `d delta(g) = s0 g t0 - s1 g t1 = delta(g) d`. Also `delta(-1) = -1`.
- **Lemma 1.2.** `[d][w] = [z][w][d] = -[w][d]` on `S_-`, so `Q` is closed under products.
  - `1, w, d, wd` are distinct modulo `z`, so `Q` is four-dimensional.
  - The matrix units check: `E_12 E_21 = e_-` and `E_21 E_12 = [d] e_- [d] = 1_- - e_-`.
  - `E_12 E_22 = e_-[d] - e_-[d]e_- = E_12`.
- **Theorem 1.3.** `delta_*(S_-)` centralizes `Q`. The multiplication map `Q (x) C -> S_-` has
  kernel an ideal `M_2(I)` of `M_2(C)`, and it restricts to the inclusion on `C`, so `I = 0`.
  Hence `J` is injective, unital and multiplicative. Iteration gives `M_(2^n)(S_-)` inside `S_-`,
  and therefore direct finiteness equals stable finiteness.
- **Theorem 2.1, (b) => (a).** `C_i` and `D_i` commute with `e_-` and `[d]`. The four terms of
  `c e_- b` are `e_- delta(tau_1 sigma_1)`, `E_12 delta(tau_1 sigma_2) = 0`,
  `E_21 delta(tau_2 sigma_1) = 0` and `(1_- - e_-) delta(tau_2 sigma_2)`, which sum to `1_-`.
- **Theorem 2.1, (a) => (b).**
  - `gamma_i beta_j = e_- [d]^(i+j-2) e_- = delta_ij e_-`.
  - The products give `u_p v_q = delta_pq e_-`, and `x[d]y = 0` for `x, y` in `T`.
  - So `tau_a sigma_b = delta_ab (e_- + [d]e_-[d]) = delta_ab 1_-`.
  - The equivalences (b) <=> (c) <=> (d) are standard.
- **Class traces.** `tau_C([g][h]) = [gh in C] = [hg in C]`, and `tau(1_-) = 2`.
  - A type `(1, n)` family gives `2 = 2n`, so `n = 1 mod 3`.
  - The Cohn defect has `tau_C(p) = -tau_C(1_-)`: `tau(p) = 1`, `tau_(z)(p) = -1`, and 0 on every
    other class.
  - Quaternary families are allowed.
- **Finite-subgroup defect exclusion (3555a55a9).** `F_3[G] ~= F_3[G] + d F_3[G]` gives `t_3(d) = 0`
  from the additive lifted trace. Nonzero sums of finite-subgroup projectives have positive
  rational lifted trace `dim/|H|`, which is integral over `Z_3` because projectives over 3-groups
  are free. So such sums are excluded as defects, as stated. This rests on the established node
  `lifted-trace-detects-finite-subgroup-projectives`.

## 16. Scalar-corner kernel embedding and lifted matrix units (5c62ee4ff, lane gk-l2-visible): PASS

Items checked: `leavitt-unit-group-algebra-embeds-in-kernel-corner`,
`leavitt-kaplansky-failures-have-invisible-witnesses` and
`leavitt-matrix-units-lift-into-finite-subgroup-algebra`, with the routes
`kernel-unitization-failure-from-group-algebra-failure`, `leavitt-df-from-kernel-unitization-df`
and `no-s0-lift-from-kernel-unitization-df`.

- **Claims 1 and 2.** These are the construction verified in Section 13.
  - `Phi(x) Phi(y) = delta(xy) z + e`, because `ze = 0` and `z` commutes with `delta(S)`, and
    `Phi(1) = 1`.
  - The defect `1 - Phi(ab) = delta(1 - ab) z` lies in `K`.
- **Claim 3, the explicit units.** `u, v` are transvections, `g = uv` has order 3, `g^2 = vu`,
  `w = uvu = vuv`, and `M_g^2 = M_g + I`.
  - Natural-representation images: `rho(f_11) = I + U + V + M_g = E_11`,
    `rho(f_22) = I + U + V + M_g^2 = E_22`, `rho(f_12) = M_g + M_g^2 + V + W = E_12` and
    `rho(f_21) = M_g + M_g^2 + W + U = E_21`, computed entrywise over `F_2`.
  - Block membership, spot-checked: `f_11 e = f_11` and `f_12 e = f_12`, using `ug = v`, `vg = w`,
    `ug^2 = w`, `vg^2 = u`, `wg = u` and `wg^2 = v`.
  - `rho` restricted to `e F_2[H]` is an isomorphism onto `M_2(F_2)` by dimension. So the
    multiplication table is exact, and `f_11 + f_22 = [g] + [g^2] = e`.
  - `pi(delta(x) f_ij) = s_i pi(x) t_j`.
- **Routes.** All three are valid: the conversion is exhaustive, and a lift of `s0` is never a unit.

## 17. Steinberg ring rigidity record (a9e3cf539, lane gk-l-gate-neg): proved parts PASS, claim correctly OPEN

Items checked: `el3-rank-models-factor-through-ring-rank-models` (OPEN), route
`non-linear-sofic-via-el3-ring-rank-rigidity`, artifact `el3-rank-ring-rigidity-2026-09-12.md`
Sections 1 and 4.

- **Lemma 1.** `x_ij(a)^p = x_ij(pa) = 1`. In characteristic `p`, `(1 + n)^p = 1 + n^p`, so
  `n_ij(a)^p = 0` exactly, and root subgroups are abelian.
- **Proposition 2.**
  - The level-`k` matrix units give a unital `M_m(F_2)` inside `R`, so `SL_(3m)(F_2) = EL_3(M_m(F_2))`
    lies in `EL_3(R)`.
  - `s_a t_b = s_(a0) t_(b0) + s_(a1) t_(b1)` makes `g = g (x) I_2` an identity of elements, so the
    type doubles from `r` to `2r`.
  - The compressor sends coefficients to `s0 a t0 = s_(0a) t_(0b)`, which is `g (+) I` of type `r`,
    and it is conjugate to `g` in `R^x`.
  - Unipotent involutions of a fixed rank form one class in `GL_N(F_2) = SL_N(F_2)`, and exact
    conjugation preserves `rk(sigma(.) - 1)`.
  - So `f(2r) = f(r)`. The calibration is right: free modules satisfy it, so it cannot refute alone.
  - **CORRECTED in Section 45.** This bullet passed the corner conjugacy `g ~ g (+) I` without re-deriving it. It fails at
    the endpoint `r = 3m/2`. Proposition 2 holds only for `1 <= r < 3m/2`.
- **Route validity.** Given the open prerequisite, the Leavitt no-rank-model theorem (Section 6,
  characteristic two), `EL_3(R) = R^x`, and simplicity of `R^x`, a linear sofic approximation gives
  a nontrivial homomorphism into a characteristic-two rank ultraproduct. The route is valid. It
  establishes nothing while `el3-rank-models-factor-through-ring-rank-models` is open, and the
  compiler status on main agrees.

## 18. Kernel-corner criterion over every field and host (4b3f811f4, lane gk-l2-invisible; 2b72dd6f1): PASS

Items checked: `leavitt-invisible-half-universal-over-every-finite-field` and
`leavitt-identity-factor-failures-transfer-into-kernel-corners`, with their proof routes.

- **Theorem 6.** `delta_n(q) = Theta_n(h)` forces `h = q I_n`, so a scalar-free `H` embeds
  `Q x H` in `Q`.
  - `z = J(1 (x) e)` with `pi(z) = Theta_n(rho_n(e)) = 0`.
  - `mu(a) = J(a (x) e)` is injective because the tensor is nonzero over a field.
  - `z mu(a) z = J(a (x) e^3) = mu(a)`, because the two tensor factors commute. Centrality of `e`
    is not needed, as the author says.
  - The three rings `S`, `K^+` and `zSz` are directly finite together, by padding in both directions.
- **Existence at level one, `(q, d) != (3, 2)`.**
  - For `d = 2`: `diag(lambda, lambda^-1)` with `lambda` of odd order `r | q - 1` is scalar-free
    and has no fixed vectors. So is a non-split torus element of odd prime order `r | q + 1`, since
    its eigenvalues are Galois conjugates and `gcd(r, q - 1) = 1`.
  - Both `q - 1` and `q + 1` are powers of two only for `q = 3`. For `q = 2`, `r = 3` works.
  - For `d >= 3`, a Zsigmondy primitive divisor of `q^d - 1` gives an irreducible, scalar-free
    element, and `(2, 6)` is covered by `diag(g, g, g)`.
- **Proposition 9, `(3, 2)` at level one.**
  - A scalar-free subgroup of `GL_2(F_3)` contains no `-I`. So it has no elements of order 4 or 8,
    whose powers give `-I`, and no element of order 6, since no reflection centralizes a
    transvection. The subgroups are `1`, `C_2 = <reflection>`, `C_3 = <transvection>` and `S_3`.
  - `C_2` idempotents project onto nonzero eigenspaces. `F_3[C_3]` is local.
  - `F_3[S_3]` has the two simple modules, trivial and sign, both composition factors of the natural
    module, so no nonzero idempotent is killed.
  - Level two has the Klein constants, or an element of order 5 in `GL_4(F_3)`.
- **Identity-factor form.**
  - The level-`k` diagonal constants commute with `delta_k` and meet it only in scalars.
  - `pi(E) = sum_(ev_gamma|H = psi) q_gamma = 0` when `psi` avoids every coordinate character.
  - Counting characters of `{lambda : lambda(0^k) = 1}` gives `(q - 1)^(d^k - 1)` against at most
    `d^k` coordinate characters.
    - At `(3, 2)`, level one gives `2` against `2`, and every character is coordinate. Level two
      gives `8 > 4`.
    - At `(3, 3)`, level one gives `4 > 3`, and for `q >= 4`, `(q - 1)^(d-1) >= 3^(d-1) > d`.
  - The level criterion holds, and `q = 2` has no diagonal constants.

## 19. Cyclically separated pairs and full cyclic corners (4da43c652, lane gk-lp-hosts): PASS

Item checked: `cyclic-separated-one-sided-pairs-equal-full-corners`.

- **Sufficiency.** `(mc) e_H a = sum_k c [g^k] a = c a = eps_iota`.
- **Converse under the twist.**
  - `delta^m = sum zeta^(im) s_i t_i = 1`, and `[delta]^r e_1 [delta]^(-r) = e_(psi zeta^(-r))`, so
    `e_H [delta]^r e_H = 0` for `r` not divisible by `m`. Hence `c a = (1/m) sum_j c' e_H b' = eps_iota`.
  - `[g^i][delta]^l = zeta^(-il) [delta]^l [g^i]` on `A_iota`, and `[g^i] e_H = e_H`.
  - So `c [g^i] a = (sum_j zeta^(-ij)) eps_iota = 0` for `0 < i < m`, as a sum of the `m`-th roots of
    unity.
- At `q = 3`, `m = 2` this recovers Theorem 1 of Section 1.

## 20. Signed Thompson crossed product (29a08d6fe, df61852de, ffc56b117, lane gk-l3-free): PASS, one wording remark

Items checked:
- `hadamard-unit-conjugates-swap-idempotent-to-cylinder`;
- `signed-thompson-algebra-is-odd-measure-crossed-product`;
- `odd-measure-space-has-no-honest-thompson-compression`;
- `odd-measure-crossed-product-carries-mod-three-trace`;
- `signed-thompson-group-has-no-finite-dimensional-representations`;
- the route `odd-measure-compression-gives-anti-invariant-corner`, and the open target
  `odd-measure-crossed-product-unit-below-cylinder-idempotent`.

- **Hadamard conjugation.**
  - With `M(x) = (t_i x s_j)`, `M(h) = [[1,1],[1,-1]]`, so `M(h)^2 = 2I = -I` and `h^2 = z`.
  - `M(h) M(w) M(h)^-1 = [[1,1],[-1,1]] [[-1,-1],[-1,1]] = [[-2,0],[0,2]] = [[1,0],[0,-1]]`, so
    `h w h^-1 = s0 t0 - s1 t1 = P_[0] - P_[1] = tau_[1] = z tau_[0]`.
  - `[h] e_- [h]^-1 = eps_- 2(1 + [z][tau_[0]]) = q_[0]`.
  - `q_[0] + q_[1] = 4 eps_-` and `q_[0] q_[1] = 4 eps_- (1 - [tau_[0]]^2) = 0`. `[w]` swaps them,
    so `S_- ~= M_2(q_[0] S_- q_[0])`.
- **Reflections.**
  - `tau_C tau_D = 1 - 2P_C - 2P_D + 4P_(C cap D) = tau_(C triangle D)`.
  - `V` normalizes `E`, and `E cap V = 1`.
  - The characters of `E_P = F_2^P` over `F_3` are the finitely additive `F_2`-measures.
  - `eps_-` maps to `4[mu(X) = 1] = 1_(M_-)`, and `q_C` to `1_(U_C)`.
  - `pi(q_C) = 4P_C = P_C`.
  - `S[alpha] T[beta] = pi([g] q_[beta])` for proper cylinders, so `pi(B) = R`, and a kernel clopen
    idempotent avoids the Dirac measures.
  - Cross-check: the Klein kernel idempotent of Section 8 is the indicator of
    `{mu([1]) = 0, mu([11]) = 1}`, which contains no Dirac measure.
- **No honest compression.** `V` acts on the compact group `M` by automorphisms and preserves Haar
  measure, and nonempty clopens have positive measure. So `lambda(U) >= sum lambda(A_i) = 1`
  forces `U = M_-`. For the naive Hilbert-hotel lift, `q_[00] + q_[01] - q_[0] = 2 . 1_(mu(00) = mu(01) = 1)`,
  checked case by case on `(mu(00), mu(01))`.
- **Mod-3 trace.**
  - Refining one atom doubles the count of odd vectors, and 2 is invertible mod 3, so the average is
    well defined and `V`-invariant.
  - `Tr(f[g] f'[g^-1]) = tau(f . f' o g^-1) = tau((f o g) . f')`, so it is a trace.
  - Values:
    - `Tr(q_[0]) = 1/2 = -1`, from one of the two odd vectors on `{[0],[1]}`.
    - `Tr(q_[0] q_[00]) = 1/4 = 1`, from the single odd vector `(1,0,0)` on `{00, 01, 1}`.
    - `Tr(eps_-) = 1`.
  - So `Tr` separates `q_[0]` from `q_[0] q_[00]` but does not obstruct `eps_- <= q_[0]`.
- **No finite-dimensional representations.**
  - `rho(V)` is finitely generated linear, hence residually finite, and `V` is simple, infinite and
    not residually finite. So `rho(V) = 1`.
  - `V` is transitive on proper nonempty clopens, so `rho(tau_C) = sigma` is constant.
  - `tau_[00] tau_[01] = tau_[0]` gives `sigma = 1`, and `tau_[0] tau_[1] = -1 = z` gives `rho(z) = 1`.
- **Route.** `B` is a subset of `S_-` containing `q_[0]`, and conjugating by `[h]` gives the
  corner solution. The route is valid, and its target claim is correctly OPEN.
- **Wording remark on artifact Section 7(b).** "a finite-index stabilizer, hence all of `G`, since
  `G` is simple" is inaccurate: `L_(F_3)(1,2)^x` has centre `{±1}`. The correct justification is that
  `G` has no proper finite-index subgroup, because it is perfect and `PG` is simple (Lemma 1.1 of
  `leavitt-self-similarity-exactness-2026-09-12.md`, Section 12 above). The conclusion stands.

## 21. Natural-lift defect, absorption no-go and Thompson V linear targets (12dfc8778, 012225c36, 86a10e7e9, 8ef1f79d9): PASS

- **Lemma 3.3 of `ternary-anti-central-cohn-reformulation-2026-09-12.md`.**
  - Over `F_3`, `(1 + p)^2 = 1 + 3p = 1` for an idempotent `p`, and `P_p = 2(1 - [1 + p])` has
    `pi(P_p) = p`.
  - For commuting `p, q`, `p + q + pq = p + q - 2pq` is their symmetric difference.
  - `P_p + P_q + P_p P_q = 8 - 6[1+p] - 6[1+q] + 4[1+p][1+q] = 2 + [(1+p)(1+q)] = P_(p xor q)`.
  - The examples hold: `1 + s0 t0 = -s0 t0 + s1 t1 = -d`, `1 + pi(e) = 2w = -w`, and
    `h_H pi(e) h_H^-1 = 2(1 + d) = 4 s0 t0 = s0 t0`.
- **The natural lift.**
  - `g p_0 = s0 s0 t0` and `h p_1 = s0 s1 t1`, which sum to `s0`.
  - `g^-1 p_00 = s0 t0 t0` and `h p_01 = s1 t1 t0`, which sum to `t0`.
  - By equivariance, `g^-1 p_00 g = p_0`, `h p_01 h = p_1`, `h p_00 h = p_00` and `g^-1 p_01 g = p_10`.
  - `(1 + p_0)(1 + p_1) = 2 = z` gives `P_0 + P_1 = 1_-` on `S_-`.
  - So `c a = 1_- + [g^-1 h] P_00 P_1 + [hg] P_10 P_0`, with each product `P_U P_V` idempotent and
    evaluation-killed. This is a diagnostic, correctly not stated as a theorem.
- **Kernel-corner absorption no-go.** `S = f_11 S + f_22 S + z S`. Base change along `pi` sends
  `zS` to 0 and `f_11 S` to `s0 t0 R ~= R`, so `zS ~= zS + f_11 S` is impossible.
- **Thompson V routes.**
  - `h: (00, 01, 1) -> (01, 1, 00)` has order 3, and `e_h = 1 + h + h^2` is idempotent over `F_2`.
  - `c e_h b = 1` is equivalent to a left-invertible `a` with `ha = a`, taking `a = e_h b`, and
    conversely `e_h a = 3a = a`.
  - `e_h b c != 1`, because a right-invertible idempotent equals 1 and `h != 1`. So `F_2[V]` fails
    direct finiteness.
  - `F_2[V]` is a unital subalgebra of `F_2[R^x]` through the tower, so the ascent route is valid.
  - The soficity route is valid and conditional, and `thompson-v-is-sofic` is open.

## 22. Matrix-unit root elements force triviality (384d05027, lane gk-l-gate-neg): PASS, one ordering slip, one scope sharpening

Items checked: `matrix-unit-root-rank-models-of-simple-el3-are-trivial`, route
`matrix-unit-root-rank-models-propagation-proof`, and artifact `el3-rank-ring-rigidity-2026-09-12.md`
Sections 4b (Lemma 3, Corollary 4, Proposition 5) and 4c (Proposition 6, Corollary 7). Every
entrywise computation below was redone from scratch.

**Block coordinates.** With `u_ij u_jk = u_ik` and `u_ij u_ji = p_i`, the map
`m -> (u_1k m u_l1 | u_1k m f | f m u_l1 | f m f)` identifies `M` with a generalized `4 x 4` matrix
ring over `T = p_1 M p_1`, with `u_ij = E_ij`. Pressure point 3: the hypothesis `u_ij u_ji = p_i` is
what makes this identification faithful.

**Lemma 3.**
- `x_ij(a)^2 = x_ij(2a) = 1`, so `(1 + n)^2 = 1 + n^2` forces `n^2 = 0`.
- With `g = 1 + x`, `h = 1 + y` and `g^-1 = g`: `[g, h] = (gh)^2 = 1 + (x + y + xy)^2`.
- Expanding, `(x + y + xy)^2 = xy + yx + xyx + yxy + xyxy`, and the image bound
  `Im n_13(a) <= Im y + x Im y` follows.

**Proposition 6, re-derived.**
1. **Step 1, pressure point 1.** `x_13(a)` commutes with `x_12(1)` and `x_23(1)`, since `j != k` and
   `i != l` in the Steinberg rule. For `Z = (z_kl)`:
   - `E_12 Z = Z E_12` gives `z_22 = z_11`, `z_21 = z_23 = z_24 = 0` and `z_21 = z_31 = z_41 = 0`;
   - `E_23 Z = Z E_23` gives `z_33 = z_22`, `z_31 = z_32 = z_34 = 0` and `z_12 = z_32 = z_42 = 0`.
   The survivors are `D` at `(1,1), (2,2), (3,3)`, `C` at `(1,3)`, `P` at `(1,4)`, `Q` at `(4,3)` and `S`
   at `(4,4)`, including the complement rows and columns.
2. **Step 2.** `[x_13(a), x_32(1)] = x_12(a)`. The terms are `Z E_32 = C E_12 + D E_32 + Q E_42`,
   `E_32 Z = D E_32`, `Z E_32 Z = CD E_12 + D^2 E_32 + QD E_42`, and `E_32 Z E_32 = Z E_32 Z E_32 = 0`.
   So `X = C(1+D) E_12 + D^2 E_32 + Q(1+D) E_42`, as stated.
3. **Step 3, pressure point 2.** `[x_12(a), x_23(1)] = x_13(a)`. With `A = C(1+D)`, `B = Q(1+D)` and
   `D2 = D^2`, the five terms sum to
   `A(1+D2) E_13 + D2(1+D2) E_33 + B(1+D2) E_43 + D2 E_22 + A D2 E_12 + D2^2 E_32 + B D2 E_42 + D2 E_23`.
   The `(1,1)` entry is 0, so `D = 0`. Then the `(1,4)` and `(4,4)` entries give `P = S = 0`, with
   `A = C` and `B = Q`.
4. **Step 4.** `x_23(a)` commutes with `x_13(1)` and `x_21(1)`. The same entrywise comparison gives
   `Z' = D'(E_11+E_22+E_33) + C' E_23 + P' E_24 + Q' E_43 + S' E_44`.
5. **Step 5.** `[x_12(1), x_23(a)] = x_13(a)`. The terms are `E_12 Z' = D' E_12 + C' E_13 + P' E_14`,
   `Z' E_12 = D' E_12`, `E_12 Z' E_12 = 0` and `Z' E_12 Z' = D'^2 E_12 + D'C' E_13 + D'P' E_14`. So
   `n_13(a) = D'^2 E_12 + (1+D')C' E_13 + (1+D')P' E_14`, with no `(4,3)` entry, hence `Q = 0`.
   - *Ordering slip, not load-bearing.* The artifact writes `C'(1+D')` and `P'(1+D')`. The correct
     factors are `(1+D')C'` and `(1+D')P'`, with `D'` on the left, because `yxy = Z'E_12Z'` puts `D'`
     first. Only the absence of the `(4,3)` entry is used.
6. **Step 6.** Each commutator leaves only the `xy` term:
   - `[x_21(1), x_13(a)]` gives `n_23(a) = C E_23`;
   - `[x_23(a), x_31(1)]` gives `n_21(a) = C E_21`;
   - `[x_32(1), x_21(a)]` gives `n_31(a) = C E_31`;
   - `[x_31(a), x_12(1)]` gives `n_32(a) = C E_32`.
7. **Step 7.**
   - `C(a) E_12 C(b) E_12 = 0` gives additivity.
   - `[x_12(a), x_23(b)] = x_13(ab)` leaves `C(a)C(b) E_13`, so `C` is multiplicative.
   - `n_12(1) = u_12` gives `C(1) = p_1`.

**Corollary 7, pressure point 4.**
- In the corner, `xy = p_1` makes `yx` an idempotent below `p_1` with `rk(yx) >= rk(x yx y) = rk(p_1)`.
  So `p_1 - yx` is a rank-null idempotent, hence 0.
- `C(t)C(s) = p_1` forces `C(1 - st) = 0`, and simplicity forces `p_1 = 0`.
- Then `u_1j = 0`, `u_ij = u_i1 u_1j = 0` and `p_i = u_ij u_ji = 0`, so `n_ij(a) = C(a)E_ij = 0`
  directly. Corollary 4 is not even needed.

**Scope sharpening.** The matrix-unit hypotheses follow from block support of the unit root
elements alone. Suppose `sigma(x_ij(1)) - 1` lies in `p_i M p_j` for pairwise orthogonal idempotents
`p_i`.
- The block calculus of Section 14 gives `u_ij u_jk = u_ik` from `[x_ij(1), x_jk(1)] = x_ik(1)`.
- `p_i' = u_ij u_ji` is an idempotent independent of `j`, with `u_ij` in `p_i' M p_j'`.
- `u_ij` still kills the enlarged complement `f' = 1 - sum p_i'`.
So the claim applies to every model whose six unit root elements are block unipotent on orthogonal
idempotents, with no matrix-unit hypothesis stated.

**Section 4b, Proposition 5.**
- `e = s_w t_w` with `eR ~= R` via `s_w`.
- `N = E_12` is an isomorphism `e_2 R -> e_1 R` that kills `e_1 R + e_3 R`.
- `N' = e E_12` is an isomorphism `e_2 eR -> e_1 eR` that kills `B' = e_1(1-e)R + e_2(1-e)R + e_3 R`.
- `B'` is free of rank `2(2^k - 1) + 1`, so `B' ~= R ~= e_3 R`.
- The compatibility check: `N'(e_2 s_w r) = e_1 s_w t_w s_w r = e_1 s_w r = g(N(e_2 r))`.
- So `x_12(1)` and `x_12(s_w t_w)` are conjugate in `GL_3(R) = R^x`, and the product decomposition is
  additivity plus `sum s_w t_w = 1`.
- Counting remarks:
  - every nontrivial element of `P_k` is `x_12(e_S)` with `e_S R ~= R`, so the displacement is
    uniform;
  - `g - 1` has rank `1/2` on free `F_2[P_k]`-modules;
  - the hyperplane sum gives about `1/4`.

## 23. Characteristic-zero-liftable idempotents are never inverse defects (e55b7ec28, lane gk-l3-kernel): PASS

Items checked: `char-zero-liftable-idempotents-are-never-inverse-defects`, route
`char-zero-liftable-idempotents-proof`, and Sections 8.0 to 8.3 of
`ternary-anti-central-kernel-normal-forms-2026-09-12.md`.

- **Conjugacy of lifts, pressure point 1.** For idempotents `E ≡ E'` mod `p` in `M_n(c_0(G, Z_p))`,
  `W = E'E + (1 - E')(1 - E) ≡ 1` is invertible. `E'W = E'E = WE`, so `E' = W E W^-1`, and the
  continuous cyclic trace `T` agrees on the two lifts. So `t_p([d]) = T(D)` for any idempotent lift
  `D`.
- **Defects have zero trace, pressure point 2.** Take finite-support lifts `A0, C0` of `ca = 1`.
  - `C0A0 ≡ 1`, so it is invertible.
  - `P = A0 (C0A0)^-1 C0` is idempotent and lifts `ac`, and `T(P) = T((C0A0)^-1 C0 A0) = n + m`.
  - So `T(1 - P) = 0` on a lift of `d (+) 0_m`, and by conjugacy `T(D) = 0`.
- **Positivity, pressure point 3.**
  - The coefficients of `D` generate a finitely generated extension of `Q`, which embeds in `C`.
  - The image `x` of `D` is a nonzero idempotent of `M_n(C[G])`, with `T(x) = sigma(T(D))`.
  - Kaplansky's argument: `p = x x*(1 + (x - x*)(x* - x))^-1` is a projection with `xp = p` and `px = x`.
    Then `T(x) = T(px) = T(xp) = T(p) = T(p*p) > 0`, by faithfulness: `T(y*y) = sum ||y_ij delta_1||^2`,
    and `y delta_1 = 0` forces `y = 0`.
  - So `T(D) != 0`, and `d` is not a defect.
- **The `e ~ f < e` case.** Padding `x + (1 - e)`, `y + (1 - e)` gives a pair with defect exactly `e - f`,
  so it is covered.
- **Linear characters, pressure point 4.** The fibre of `H2 x H1 -> H2H1` over `h2h1` is
  `{(h2 k, k^-1 h1) : k in K = H1 cap H2}`. The coefficient of `FE` there is
  `psi2(h2)^-1 psi1(h1)^-1 sum_k psi2(k)^-1 psi1(k) / (|H1||H2|)`.
  - If the characters disagree on `K`, then `FE = 0 != F`.
  - Otherwise every point of `H2H1` has a unit coefficient, so `FE = F` forces `H2H1 = H2`, hence
    `H1 <= H2` and `psi2|H1 = psi1`.
  - The converse is the direct sum computation.
- **Level coherence, pressure point 5.** `S[gamma]T[gamma'] = S[gamma 0]T[gamma' 0] + S[gamma 1]T[gamma' 1]`
  gives `Theta_(2^(k+1))(a (x) I_2) = Theta_(2^k)(a)`, so finitely many constants lie in one finite
  `Theta(GL_(2^K)(F_3))`.
- Trust surface: the established lifted-trace node and Kaplansky positivity, which is proved inline.

## 24. Units span every d-ary Leavitt algebra (7471b241e, lane gk-lp-hosts): PASS

Items checked: `leavitt-units-span-every-d-ary-leavitt-algebra` and route `d-ary-leavitt-unit-span-proof`.

- **Square-zero elements.** For `i != j`, `n = s_i a t_j` satisfies `n^2 = s_i a (t_j s_i) a t_j = 0`,
  so `n = (1 + n) - 1` is a difference of units.
- **Products.** For square-zero `n` and `m`, `nm = (1+n)(1+m) - (1+n) - (1+m) + 1` lies in the
  additive span of units.
- **Diagonal terms.** `s_i a t_i = (s_i a t_j)(s_j t_i)`, a product of two square-zero elements, using
  `t_j s_j = 1`.
- **Decomposition.** `a = sum_(i,k) s_i t_i a s_k t_k = sum_(i,k) s_i (t_i a s_k) t_k`, and each term is
  one of the two kinds above.
- So the additive group generated by the units is all of `A`. For `A = L_(F_q)(1,d)`, the evaluation
  `F_q[A^x] -> A` is onto for every `d >= 2`. This closes the scope remark of Section 9: Theorem 3(5)
  of the survey holds as stated.

## 25. Corner fullness is the absence of states, and colimit hosts (99f8eb777, lane gk-l3-obstruct): PASS

Items checked: `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` (Theorem E) and
`leavitt-visible-states-are-factorwise-and-colimit-stable` (Theorem F), census artifact Sections 7 and 8.

- **Diagonal endomorphism.**
  - `D(h) D(h') = sum_(i,j) s_i h t_i s_j h' t_j = D(hh')` and `D(1) = 1`.
  - `t_0 D(h) s_0 = h`, so `D` is injective, and `D` fixes scalars.
  - `g D(h) = sum_i s_(i+1) h t_i = D(h) g`.
  - So `D_*` fixes every `eps_chi`, maps `A_iota` into itself, and commutes with `e_H`.
  - `psi(x) psi(y) = e_H e_H D(x) D(y) = e_H D(xy)` and `psi(eps_iota) = e_H`: a unital ring homomorphism
    `A -> T`.
- **Halving.**
  - `Phi = M_m(psi)` is unital into `M_m(T) ~= A`, and induction is a monoid homomorphism
    `F : V(A) -> V(A)`.
  - Morita sends `[M_m(A)]` to `mu`, so `F(mu) = u` and `x = F(u)` satisfies `mx = u`.
  - `F` preserves `<=`, because `b = a + c` gives `F(b) = F(a) + F(c)`.
- **1 <=> `mp <= p`.** `c' e_H b' = eps_iota` says `A <~ e_H A`, that is `u <= p = [e_H A]`, with `u = mp`
  from the `m` conjugate isotypic idempotents.
- **1 => 2.** `p = p + (m-1)p + c` iterates to `p + m(m-1)p <= p`. Adding `(m-1)p` gives `mu <= u`, and
  then `2u <= u` for `m >= 2`.
- **2 => 1.** `psi` carries a two-pair Cohn family to one in `T`, so `2[T] <= [T]`, hence `m[T] <= [T]`.
- **3 => 2.**
  - Pad to `(mj + 1)u <= mju` and apply `F`: `ju + x <= ju`. Iterating gives `ju + mx = (j+1)u <= ju`.
  - With `j = ceil(n/m)`, `(m-1)(n-1) > 0` gives `j < n`, so the descent terminates at `n = 1`.
- **3 <=> 4 <=> 5.**
  - `A^n ~= A^(n+1) (+) Q` gives `[Q] = -u`.
  - Conversely `[Q] + u = 0` in `K_0` gives `Q (+) A (+) A^N ~= A^N` with `N >= 1`.
  - The state criterion of Section 11 uses only that `u` is an order unit, which holds for every
    unital ring.
- **Surjunctivity.** A(c) plus padding by `1 - eps_iota`.
- **Trace consistency at `q = 3`.** `tau(C) = 2 - 4 = 1`.
- **Theorem F.**
  - *Factorwise.* On a factor with `t_chi = 0`, classes lie between `-N[eps_chi]` and `N[eps_chi]`, so the
    state vanishes there. The augmentation state is carried by the trivial factor, since
    `epsilon(eps_chi) = delta_(chi, 1)`.
  - *Ascent.* `phi(x) = x eps_iota(q^r)` is unital because `eps_iota(q) eps_iota(q^r) = eps_iota(q^r)`
    (Section 9), and `e_H` maps to `e_H`.
  - *Presentation.* `[lambda] - lambda` acts invertibly on `A_chi` for `chi != iota`, so the quotient is
    `A_iota`.
  - *Colimits.* `V` and `K_0` commute with directed colimits.
  - *3 => 4.* `d` and `2d - 1` are both admissible and `p` cannot divide both, and a primitive `m`-th root
    appears at some stage `p^(k!)`.
- The census correction, that the stable target is equivalent to the corner rather than weaker, agrees
  with Theorem E, 4 => 1.

## 26. Hadamard frame section (f174ac372, lane gk-l3-units): conclusion PASS, Proposition 4.2 false as literally stated

Item checked: artifact `ternary-anti-central-cohn-reformulation-2026-09-12.md` Section 4, and the Attempts
entry on the OPEN claim `ternary-anti-central-summand-has-quaternary-leavitt-family`.

- **Lemma 4.1: PASS.** `u_N u_(N') = u_(NN')` at depth two, `M^2 = -I` over `F_3`, and
  `N^2 = M^2 (x) M^2 = I_4`. So `H_2 = u_N` is an involution, and `f_(+-) = 2(1 +- [H_2])` are
  idempotents.
- **Proposition 4.3: PASS in substance, with one misstatement.**
  - `eps_- F_3[H]` is finite-dimensional, hence Dedekind-finite. So `tau_1 sigma_1 = 1_-` makes `sigma_1` a
    unit, and `tau_1 sigma_2 = 0` forces `sigma_2 = 0`.
  - *Misstatement.* `H = <H_2, g_w, 1 + p_u, z>` is finite but not a `2`-group: `H_2` is not a signed
    permutation, and `Theta(GL_4(F_3))` has order divisible by 3. The correct containment is
    `H <= Theta_(2^K)(GL_(2^K)(F_3))` for `K = max(2, k)`, by level coherence (Section 23). Only
    finiteness is used.
- **Proposition 4.2: false as literally stated.** It asserts `sigma_v, tau_v` supported in a finite
  subgroup with `tau_v sigma_(v') = delta_(v v') 1_-` and `sum_v sigma_v tau_v = 1_-`. That is a unital
  quaternary Leavitt family inside the finite-dimensional `eps_- F_3[H]`, which Proposition 4.3 (and a
  dimension count, `A ~= A^4` with `0 < dim A < infinity`) excludes.
  - What the construction does give is a change of basis: the Gram matrix `N^T D N` has zero
    off-diagonal entries, so the cross terms `tau_v sigma_(v')`, `v != v'`, vanish, while the diagonal
    entries are proper idempotents, not `1_-`.
  - The section's conclusion is correct and unaffected: cross terms can be cancelled by non-monomial
    finite-level units, and the wall is infinite support. The Attempts entry on the claim node already
    phrases it that way.
  - Requested of the author: restate 4.2 as vanishing of the off-diagonal Gram entries, not as a
    frame with `tau_v sigma_v = 1_-`.

## 27. The ternary Cohn defect class has no characteristic-zero lift (d465300a3, lane gk-l3-kernel): PASS

Item checked: the Cohn-defect paragraph added to `char-zero-liftable-idempotents-are-never-inverse-defects`.

- **The class.** For a unital two-pair Cohn family `tau_i sigma_j = delta_ij eps_-` in `S_-`, put
  `p = eps_- - sigma_1 tau_1 - sigma_2 tau_2`. The three idempotents are orthogonal, and
  `sigma_i tau_i ~ eps_-`, so `[eps_-] = 2[eps_-] + [p]` and `[p] = -[eps_-]`.
- **The lifted trace.** `(1 - [z])/2` is an idempotent of `Z_3[G]`, because `z^2 = 1`, and it reduces
  to `2(1 - [z]) = eps_-`, since `1/2 ≡ 2` mod 3. Its identity coefficient is `1/2`, so
  `t_3([eps_-]) = 1/2` and `t_3([p]) = -1/2`. Mod 3 this is `1`, which matches `tau(p) = 1` (Section 15).
- **No lift.** Any idempotent `P` at any matrix size with `[P] = [p]` has `t_3 = -1/2`. A finite-support
  idempotent lift `D` over `Z_3` would have `T(D) = -1/2` by conjugacy of lifts, while Kaplansky
  positivity after embedding the coefficient field in `C` forces `T(D) >= 0` (Section 23). That is a
  contradiction.
- **Scope.** By Theorem E (Section 25), every stable failure reduces to a size-one Cohn family, whose
  defect class is `-[eps_-]`. So this exclusion covers every complement relevant to the corner target.

## 28. Matrix-unit root models in odd characteristic (1c8585ca8, lane gk-l-gate-neg): PASS, scope sharpening extends

Items checked: `matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial`, route
`odd-char-matrix-unit-root-rank-models-torus-proof`, artifact `el3-rank-ring-rigidity-2026-09-12.md`
Section 4d (Proposition 8 and Corollary 9).

- **Step 1, pressure point 1.**
  - `u_ij u_kl = u_ij p_j p_k u_kl = 0` for `j != k`, and `u_ij u_jl = u_il`, `u_ij u_ji = p_i`. So `Phi` is
    an algebra homomorphism with `Phi(1) = p_1 + p_2 + p_3`, and `Phi + f` is a group homomorphism.
  - `x_ij(lambda) = x_ij(1)^lambda`, and `(1 + u)^lambda = 1 + lambda u` because `u^2 = 0`.
  - The elementary matrices generate `SL_3(F_p)`, so `sigma = Phi + f` there.
- **Step 2, pressure point 2.** The entrywise block form uses no characteristic.
  - Row 2 and column 2 of `n` are `(0, D, 0, 0)`, so `p_2` is an invariant summand acted on by `D`.
  - On `(p_1, f, p_3)` the matrix is `[[D, P, C], [0, S, Q], [0, 0, D]]`, upper triangular.
  - So `n^p = 0` gives `D^p = S^p = 0`.
- **Step 3, pressure point 3.**
  - `h = diag(-1,-1,1)` has determinant 1 and scales `E_13` by `t_1/t_3 = -1`, so it inverts `x_13(a)`.
  - `sigma(h) = -p_1 - p_2 + p_3 + f` scales block `(i,j)` by `eps_i eps_j`, which gives `n'` as stated.
  - Entries of `n + n' + n n'`:
    - `(1,1)`: `2D + D^2`;
    - `(4,4)`: `2S + S^2 + n_43 n'_34 = 2S + S^2`;
    - `(4,3)`: `2Q + n_43 n'_33 + n_44 n'_43 = 2Q + QD + SQ`.
  - `2 + D = 2(1 + D/2)` is invertible by a finite geometric series, so `D = 0`, likewise `S = 0`, and then
    `2Q = 0`.
- **Step 4, pressure point 4.** `h' = diag(1,-1,-1)` also inverts `x_13(a)`, with scalings `-1` at `(1,3)`
  and `+1` at `(1,4)`. `(C E_13 + P E_14)(-C E_13 + P E_14) = 0`, so the product is `1 + 2P E_14`, and
  `P = 0`.
- **Step 5.** A signed permutation `w` in `SL_3(F_p)` sends `x_13(b)` to `x_kl(+-b)`, and `sigma(w) = Phi(w) + f`
  permutes the corners and fixes `f`, so every root has block support.
- **Corollary 9, pressure point 5.**
  - Block support gives additivity and `[1+X, 1+Y] = 1 + XY` in every characteristic.
  - The Steinberg relations give `psi_13(ab) = psi_12(a) psi_23(b)`, `psi_12(c) = psi_13(c) u_32`,
    `psi_13(b) = psi_12(b) u_23` and `psi_23(b) = u_21 psi_13(b)`.
  - So `C(a) = psi_12(a) u_21 = psi_13(a) u_31`, and
    `C(ab) = psi_12(a) u_21 psi_13(b) u_31 = psi_12(a) u_21 psi_12(b) u_23 u_31 = C(a) C(b)`, with
    `C(1) = p_1`.
  - The corner is directly finite and `R` is simple, so the collapse follows.
- **Ternary hosts.** `R_3 ~= R_3^3` gives `EL_3(R_3) <= GL_3(R_3) ~= G_3`, and `G_3` embeds in `PG`. A
  separating `F_3`-linear sofic model restricts to a nontrivial model of the infinite `EL_3(R_3)` in
  characteristic three, so Corollary 9 excludes the matrix-unit shape.
- **Scope sharpening (Section 22) holds here too.** The block calculus is characteristic-free. If only
  `sigma(x_ij(1)) - 1` lies in `p_i M p_j` for orthogonal idempotents `p_i`, then
  `u_ij u_jk = u_ik`, `p_i' = u_ij u_ji` is idempotent and independent of `j`, and `u_ij` lies in
  `p_i' M p_j'` and kills the enlarged complement. So the odd claim also needs only block support of the
  six unit root elements.

## 29. Rank-rigidity region for the lead: exact hypotheses, status of the factoring claim, route validity

This section answers the lead's priority request on `gk-l-gate-neg`'s landings (384d05027, 1c8585ca8,
ed4f426dc). The derivations are Sections 17, 22 and 28.

**Exact hypotheses of the two matrix-unit theorems (both PASS).**
- **Characteristic.** `R` is simple and not directly finite, of characteristic `p`. `M` is a rank
  ultraproduct over a field of the same characteristic. Characteristic two is needed for `n^2 = 0` in
  Proposition 6. For odd `p`, only `n^p = 0`, the torus of `SL_3(F_p)`, and invertibility of 2 are used.
- **Block support of the unit roots.** The six unit root elements must satisfy
  `sigma(x_ij(1)) - 1 in p_i M p_j` for pairwise orthogonal idempotents `p_i`. The matrix-unit relations
  and a trivial complement then follow (Sections 22 and 28), in every characteristic.
- **Nothing else.** Nothing is assumed about `x_ij(a)` for `a != 1`, about ranks of the `p_i`, or about
  additivity.
- **Transposed shape, new here.** The dual natural shape is covered as well. `g -> (g^T)^-1` is a group
  isomorphism `EL_3(R) -> EL_3(R^op)` sending `x_ij(a)` to `x_ji(-a)`, since transpose is an
  anti-isomorphism `M_3(R) -> M_3(R^op)`. `R^op` is again simple and not directly finite, because
  `ts = 1 != st`. If `sigma(x_ij(1)) = 1 - u'_ji` with `u'` matrix units (restriction
  `(dual natural (x) W) (+) trivial`), then `sigma o theta^-1` sends `x_kl(1)` to
  `sigma(x_lk(1))^-1 = 1 + u'_kl`. That satisfies the matrix-unit hypothesis over `R^op`, so `sigma` is
  trivial.

**What stays open (the lane's scope note is accurate).** A surviving rank model restricts to `SL_3(F_p)`
with some summand on which the unit roots are not block supported. That covers:
- a nontrivial complement;
- natural and dual natural pieces together;
- other composition factors, such as adjoint or Steinberg pieces, and projectives;
- non-split extensions between natural and trivial factors.

**The factoring claim.** `el3-rank-models-factor-through-ring-rank-models` is OPEN at tip `6be4178c43`,
correctly. Its Attempts accurately record every proved sub-case and where each attempt stops.

**The route `non-linear-sofic-via-el3-ring-rank-rigidity`: valid as stated, conditional.**
- An `F_2`-linear sofic approximation gives an injective homomorphism `R^x -> M^x` into a rank ultraproduct
  over `F_2`, with `rk(sigma(g) - 1) >= 1/4` for `g != 1` (Arzhantseva–Paunescu).
- `R^x = EL_3(R)` and `leavitt-algebra-has-no-unital-rank-model` are established. Simplicity of `R^x` is
  recorded, and the route does not even need it: separation alone contradicts triviality on the
  infinite `EL_3(R)`.
- So the route fires iff the prerequisite is established. Nothing decision-level has landed.

**Recommendation (not a defect).** The prerequisite is a class statement over all simple characteristic-`p`
rings without rank models, and a sofic `EL_3(S)` over any such `S` refutes it. The payoff only needs the
Leavitt instance. An instance claim for `L_K(1,n)`, with its own route into `non-linear-sofic-group`,
would keep the route alive even if the class statement fails for some non-finitely-generated ring.

## 30. Odd-measure kernel mass and nonamenable Thompson support (879678530, lane gk-l3-free); withdrawn Hadamard proposition (0a97d381d, lane gk-l3-units): PASS

- **`odd-measure-kernel-carries-almost-all-haar-mass`.**
  - *Pushforward.* Restricting to the length-`n` cylinders is a surjective continuous homomorphism
    `M -> F_2^(P_n)`, since it is dual to the injection `F_2^(P_n) -> C(X, F_2)`. So Haar measure pushes forward
    to the uniform measure, and on the coset `M_-` to the uniform measure on the `2^(2^n - 1)` odd vectors.
  - *Mass.* Dirac measures give exactly the `2^n` weight-one vectors, so `lambda(M_- \ U_n) = 2^(n+1-2^n)`.
    That gives `0`, `1/2` and `15/16` for `n = 1, 2, 3`. `U_n` is clopen and avoids every Dirac measure, so
    `1_(U_n)` is a kernel idempotent (Theorem 2(4), Section 20).
  - *Nesting.* If `mu` has weight one at every depth, the children of the carrying atom sum to 1, so exactly
    one carries 1; the children of the other atoms sum to 0, and weight one excludes two. The nested atoms
    define `x`, and `mu(C) = [x in C]` on every clopen `C`. The intersection has measure at most
    `2^(n+1-2^n) -> 0`.
- **`odd-measure-corner-witnesses-need-nonamenable-thompson-support`.**
  - *Soficity.* `L cap E` lies in an elementary abelian 2-group, so it is locally finite and sofic. It is
    normal in `L` with quotient `K`. `sofic-kernel-amenable-quotient-permanence` then makes `L` sofic, so
    `F_3`-linear sofic, so `F_3[L]` is directly finite.
  - *Membership.* `b'` and `c'` lie in `F_3[L]` because their supports and `z` are in `L`. `q_[0]` and
    `q_[1] = eps_- 2(1 - [z tau_[0]])` lie in `F_3[L]` because `z, tau_[0]` are in `L`.
  - *Contradiction.* With `x = q_[0] b' + eps_+` and `y = c' q_[0] + eps_+`, the cross terms vanish because
    `c' eps_+ = eps_+ q_[0] = 0`, so `yx = 1`. Then `xy = 1` gives `q_[0] b' c' q_[0] = eps_-`, and multiplying
    by `q_[1]` gives `q_[1] = 0`. But `1, tau_[0], z, z tau_[0]` are distinct.
  - *Scope.* Only the `V`-projection is constrained. Subgroups of amenable groups are amenable, so a witness
    with projection in `F` would make `F` nonamenable.
- **gk-l3-units corrections (0a97d381d).** Proposition 4.2 is withdrawn, and Proposition 4.3 now reads
  "`H` finite, containing `z`", which is exactly the scope of Section 26.
  - *Corollary 4.5.* No Cohn family is supported on the locally finite group of constant units. A family has
    finite support. Level coherence (Section 23) puts finitely many constants, together with
    `z = Theta(-I)`, in one finite `Theta(GL_(2^K)(F_3))`, and Proposition 4.3 applies there. PASS.
  - *Diagnostics.* The kernel mass sitting at finite depth (Proposition 7 above) supersedes the withdrawn
    "infinite-depth" dichotomy.

## 31. Tensor-shape calibration (154ca52a5, audit artifact Section 8): PASS, one wording remark

Item checked: Section 8 of `leavitt-unit-rank-model-construction-audit-2026-09-12.md`.

- **The characteristic-two formula.**
  - `x_ij(1) = 1 + E` and `(1 + E)^-1 = 1 + E`, so `rho^(-T)(x_ij(1)) = 1 + E'` with `E' = E_ji`.
  - The tensor product is `1 + N` with `N = E (x) 1 + 1 (x) E' + E (x) E'`.
  - `N^2 = 0`: the squares vanish, the two cross terms `(E (x) 1)(1 (x) E')` and `(1 (x) E')(E (x) 1)` add to
    `2 E (x) E' = 0`, and every product containing `E^2` or `E'^2` vanishes.
- **The calibration argument is sound.**
  - `rho_k (x) rho_k^(-T)` is an honest faithful homomorphism of `EL_3(F_2[t])`.
  - Restricted to `SL_3(F_2)` it is `(natural (x) dual)^(k^2) = gl_3^(k^2)`.
  - The eight-dimensional adjoint composition factor is not natural, so the unit root elements are not
    block supported (Section 29).
  - So any block-support argument using only the characteristic, `N^p = 0`, regular-ring
    ranges and kernels, and the Steinberg relations would prove a false statement. It must use
    simplicity and non-direct-finiteness of `R`.
- **Wording remark.** "with no trivial summand to split off" is not accurate. In characteristic `!= 3`,
  `gl_3 = F I (+) sl_3`, because `tr(I) = 3` is invertible, so natural (x) dual does have a trivial summand.
  The calibration survives, since the adjoint summand `sl_3` is irreducible of dimension 8 and its unit
  root elements are not block supported. Suggested wording: "natural (x) dual = trivial (+) adjoint, and
  the adjoint summand has no block-supported unit roots".
- **Tensor constructions die for `R`.**
  - `L_K(1,n)` is central simple over `K`, and a central simple algebra tensored with a simple algebra is
    simple, in every dimension. So every `R^((x) a) (x) (R^op)^((x) b)` is simple.
  - `(t_0 (x) 1)(s_0 (x) 1) = 1` while `s_0 t_0 (x) 1 != 1` (the tensor product is over a field), so it is
    not directly finite.
  - So it has no nonzero homomorphism into a corner of a rank ultraproduct (Sections 6 and 14). Approximate
    modules over these tensor algebras, including approximate bimodules, give nothing.

## 32. Finite triangular extensions of matrix-unit models (gk-rk-extensions, family R): PASS

Items checked: `perfect-groups-have-no-triangular-models-with-trivial-diagonal`,
`filtered-matrix-unit-rank-models-of-simple-el3-are-trivial`, their routes, and
`el3-rank-model-extensions-2026-09-12.md` Sections 1 to 3.

- **Lemma 1(1).** For `g, h` upper triangular, `h_t g h h_t = sum_r (h_t g h_r)(h_r h h_t)`. The terms with
  `r < t` die by `h_t g h_r = 0`, and those with `r > t` by `h_r h h_t = 0`. So compression is multiplicative
  and unital, and `sigma(g^-1)` in `T` makes `sigma_t(g)` a corner unit.
- **Lemma 1(2).**
  - `h_s M h_r . h_s' M h_r'` is nonzero only if `r = s'`, and then it has height
    `(r - s) + (r' - s')`. So `N_k N_l <= N_(k+l)` and `N_m = 0`.
  - `T N_k` and `N_k T` lie in `N_k`, because `T` never lowers the column index. So `N_k` is an ideal of `T`,
    and `1 + N_k` is a group, with finite geometric-series inverses.
  - `(1+x)(1+y) = (1+y)(1+x) + (xy - yx)` gives `[1+x, 1+y] = 1 + (xy - yx)(1+x)^-1(1+y)^-1` in `U_(k+l)`.
    So `gamma_c(U_1) <= U_c` and `U_m = 1`.
  - Trivial diagonal blocks give `sigma(g) - 1 = sum_(s<r) h_s(sigma(g) - 1)h_r`, which lies in `N`. A perfect
    subgroup of a nilpotent group is trivial.
- **Membership of all of `sigma(EL_3(R))` in `T`.** In the shapes E1 and E2 only root images are specified.
  `T` is a subring, and `x_ij(a)^-1 = x_ij(-a)` is again a root element. So triangular root images force
  `sigma(EL_3(R)) <= T`, and the hypothesis of the claim is met.
- **Corners are rank ultraproducts.**
  - Lifting idempotents: take a finite-stage matrix `e` with `rk(e^2 - e) = delta n`, and put
    `W = ker(e^2 - e)`. Every `w` in `W` is `(w - ew) + ew`, with the first term in `ker e` and the second in
    `ker(e - 1)`. So the idempotent `e'` projecting onto `ker(e - 1)` along `ker e (+) C` agrees with `e` on
    `W`, and `rk(e - e') <= delta n`.
  - So `h_t M h_t` is a rank ultraproduct with renormalized rank, or zero. Only direct finiteness of corners
    is used anyway.
- **Transposed pieces.**
  - Transpose is an anti-isomorphism `M_3(R) -> M_3(R^op)`: `(AB)^T_(ij) = sum_k A_jk B_ki = (B^T A^T)_ij`
    over `R^op`.
  - So `theta(g) = (g^T)^-1` is a group isomorphism `EL_3(R) -> EL_3(R^op)` with
    `theta(x_ij(a)) = x_ji(-a)`.
  - `R^op` is simple and not directly finite, so Corollaries 7 and 9 over `R^op` apply (Section 29).
- **Gluing.** `EL_3(R)` is perfect, and Lemma 1 gives triviality.
- **E1 and E2 coordinates.**
  - For `X` in `(p_i + f) M p_j` and `Y` in `(p_j + f) M p_k`: `X^2 = YX = 0` because `p_j(p_i + f) = 0` and
    `p_k(p_i + f) = 0`, `Y^2 = 0`, and `X d_jk = 0`.
  - So `XY = v_ij v_jk + d_ij v_jk`, as stated.
- **Scope.** The claim covers only finite upper-triangular flags whose graded pieces are matrix-unit,
  transposed or trivial pieces. Two-sided mixing, other composition factors, and diffuse flags of unbounded
  length remain open, as the artifact says. The restatement trap S4 is correctly not landed as a route.
  `el3-rank-models-factor-through-ring-rank-models` stays OPEN.

## 33. Coverage audit of family L claims; binary Leavitt projective monoid citation

**Coverage.** Every ESTABLISHED claim pushed by the family L and family R lanes now has an independent verdict,
either here or in `gk-verify-pos-permanence-chain-2026-09-12.md`. Five `gk-kdf-structure` claims from before
the swarm were verified there, not here:
- `rank-ultraproduct-compressors-conserve-fixed-right-ideals`;
- `leavitt-rank-models-kazhdan-fixed-ideals-are-global`;
- `linear-scale-rank-conservation-does-not-kill-defects`;
- `kazhdan-group-rank-models-admit-no-expander-decomposition`;
- `kazhdan-rank-ultraproducts-can-have-diffuse-commutants`.
Section 25 of that artifact tightens the scope of the last two.

**`binary-leavitt-nonzero-projectives-are-free`: PASS as a citation, with a consistency check.**
- *The import.* Bergman's monoid `V(L_K(1,n)) = <x | x = nx>`. At `n = 2` it is `{0, x}`, so a nonzero finitely
  generated projective is isomorphic to `R_R`. This was not rechecked against the source PDF, since this lane
  runs no local PDF reads; it is the trust surface.
- *Consistency.*
  - `R ~= R^2` gives `x = 2x`.
  - Pure infiniteness by monomials (Lemma 1 of the normal-form artifact, re-derived in Section 8) gives
    `1 = b e a` for every nonzero idempotent `e`, so `x <= [eR]`.
  - Every `[eR]` lies below some `nx = x`.
  - These agree with `V \ {0} = {x}`. Equality of `[eR]` and `x` itself needs the cited cancellation for
    purely infinite simple rings.
- *Consumers.* The only consumer is the second, imported route
  `leavitt-one-sided-pairs-unit-translates-via-projective-monoid`. The elementary route through Lemmas 1 to 3
  of `leavitt-inverse-defect-normal-forms-2026-09-12.md` (verified in Sections 8 and 13) carries the same
  conclusion with no import. No Gottschalk decision rests on this citation alone.

## 34. Leavitt instance claim, its routes, and free content (e53fe8884, lane gk-l-gate-neg): PASS, one scope remark

Items checked: `leavitt-el3-rank-models-over-finite-fields-are-trivial` (OPEN), routes
`non-linear-sofic-via-leavitt-el3-rank-triviality` and `leavitt-el3-rank-triviality-from-ring-rank-rigidity`, the
established `free-rank-models-on-sl3-admit-no-block-support` with its route, and artifact Section 4e.

- **Instance claim.** The statement is faithful. It is correctly OPEN, and it carries the payoff on its own route,
  which answers the Section 29 recommendation.
  - Payoff: `R ~= R^2` gives `R ~= R^3`, so `EL_3(R) <= GL_3(R) ~= R^x`. Linear soficity passes to subgroups, and
    `R^x` embeds in `PG` for `K = F_3`.
- **Route `non-linear-sofic-via-leavitt-el3-rank-triviality`: valid.**
  - `EL_3(L_(F_2)(1,2))` is countable and infinite, since the `x_12(a)` are distinct.
  - An `F_2`-linear sofic approximation of a countable group gives an injective homomorphism into the units of an
    `F_2` rank ultraproduct (Arzhantseva–Paunescu). The instance claim forbids a nontrivial one.
  - The target root asks for a countable `G` and a field `F` with `G` not `F`-linear sofic, so this is exactly the
    root. The route fires iff the instance claim is established.
- **Route `leavitt-el3-rank-triviality-from-ring-rank-rigidity`: valid.**
  - `L_K(1,n)` is simple.
  - `C(t_0)C(s_0) = 1` gives `C(s_0)C(t_0) = 1` in a directly finite `M`, so `C(1 - s_0 t_0) = 0`.
  - `(1 - s_0 t_0)s_1 = s_1 != 0`, so simplicity makes `C = 0`, contradicting `C(1) = 1`.
  - So the class hypothesis holds.
- **`free-rank-models-on-sl3-admit-no-block-support`: PASS.**
  - `beta = hg - h - g + 1` uses four distinct elements (`h, g != 1`, `h != g^-1`), so `beta . 1 != 0`, and
    `sigma_i(beta)` has rank at least `m_i` on the free summand with invariant complement.
  - Block support gives `v_23 v_12` in `p_2 M p_3 p_1 M p_2 = 0`.
  - *Example 11.*
    - `S_inf` is a unital direct limit of simple algebras, hence simple, and `a -> (a (x) I_(p^(j-k)))_j` is a
      unital ring rank model.
    - `EL_3(M_m(F_p)) = SL_(3m)(F_p)`: cross-block transvections give same-block ones through a third block.
    - Each `g` lies in the level groups for `omega`-almost all `k`, so the regular representations assemble into
      an exact homomorphism. It separates, since `rk(lambda(g) - 1)/N = 1 - 1/ord(g) >= 1/2`.
    - The restriction to `H_0` is free with `mu = 1/|H_0|`.
- **Artifact Section 4e.**
  - Free content is monomial in its own basis on each finite subgroup. For a nonsofic host, gluing along infinite
    subgroups must be non-monomial (Section 14). PASS.
  - The Kraft-inequality remark is not load-bearing and was not re-derived.
- **Scope remark on the instance claim's Attempts.** "Conjugacy `x_12(e) ~ x_12(1)` for nonzero sums `e` of level
  idempotents" holds as stated only for `n = 2`.
  - For `L_K(1,n)`, `e_S R ~= R^(|S|)` is the image of `x_12(e_S) - 1`. Conjugate elements have isomorphic images,
    and `R^m ~= R` iff `m ≡ 1 mod (n - 1)`. So the conjugacy holds iff `|S| ≡ 1 mod (n - 1)`.
  - Then `B' ~= R^(2(n^k - |S|) + 1) ~= R` as well, so the condition is also sufficient.
  - The product decomposition into `n^k` conjugates uses `|S| = 1` and holds for every `n`.
- **Wiring suggestion.** `binary-leavitt-unit-group-is-f2-linear-sofic` does not yet list the instance claim under
  `refuted_by`, although its negation follows through `EL_3(R) <= R^x`. Consider recording that link.

## 35. Two root identities decide the matrix-unit hypothesis (685d99751a, lane gk-rk-unipotent): PASS

Items checked: `el3-unit-root-matrix-units-iff-two-root-identities`, `matrix-unit-rank-models-extract-ring-rank-models`,
`fd-represented-coefficients-violate-two-root-identities`, their proof routes, the equivalence routes
`two-root-identities-give-el3-ring-rigidity` and `el3-ring-rigidity-gives-the-two-root-identities`, and
`el3-two-root-identities-2026-09-12.md` Sections 1 to 4. The claim `rank-models-of-el3-satisfy-the-two-root-identities`
is correctly OPEN.

- **Theorem A, commutator step.**
  - `X^2 = 0` gives `(1 + X)^-1 = 1 - X`.
  - Expanding `(1 + X + Y + XY)(1 - X - Y + XY)`:
    - the `1` row gives `1 - X - Y + XY`;
    - the `X` row gives `X - XY`, since `X^2 = X^2 Y = 0`;
    - the `Y` row gives `Y`, since `YX = Y^2 = YXY = 0`;
    - the `XY` row gives `XY`, since `XYX = XY^2 = XYXY = 0`.
  - The sum is `1 + XY`, so `N_ik = N_ij N_jk`.
- **Theorem A, idempotents.**
  - `N_ji N_ik = N_jk`, so `p_i^(j) N_ik = N_ik` and `p_i^(j) N_ij = p_i^(j) N_ik N_kj = N_ij`.
  - So `p_i^(j)` is idempotent, and `N_ij N_jk N_kj = N_ij`, which gives `p_i^(k) = p_i^(j)`.
  - `p_i p_j = N_ij N_ji N_ji N_ij = 0`. `N_ij` lies in `p_i M p_j`, since `p_j = N_jk N_kj`.
  - So MU holds with `u = N`.
- **Weyl reduction.** The signed permutation matrices of `EL_3(Z)` conjugate `x_ab(1)` to `x_(pi(a) pi(b))(+-1)`,
  and `N_x(-1) = -N_x (1 + N_x)^-1`, so vanishing of a product is Weyl-invariant.
  - The ordered pairs `(ab, cd)` with `b != c` fall into four orbits: squares, same row `(ab, ad)`, same column
    `(ab, cb)` with `c` the third index, and reversed composable `(ab, ca)`.
  - The converse uses the squares and `N_jk N_ij = 0`, which is the `(ab, ca)` orbit with representative
    `N_23 N_12`.
  - In characteristic two, `N_12^2 = sigma(x_12(2)) - 1 = 0` automatically.
- **Theorem D.**
  - [RR] Proposition 6 (characteristic two), and Proposition 8 plus the Corollary 9 computation (odd `p`), use
    neither simplicity nor non-direct-finiteness (Sections 22 and 28). So `C : R -> p_1 M p_1` is a unital ring
    homomorphism for every characteristic-`p` algebra `R`.
  - The corner is a rank ultraproduct (Section 32).
  - If `p_1 = 0`, then `u_1j = p_1 u_1j = 0`, `u_i1 = 0`, and `u_ij = u_i1 u_1j = 0`. Then
    `x_ij(a) = [x_ik(a), x_kj(1)]` lies in the normal closure of the kernel, so `sigma` is trivial.
- **Route `two-root-identities-give-el3-ring-rigidity`: valid.**
  - Identities give MU, and MU gives a unital homomorphism into a rank-ultraproduct corner unless `p_1 = 0`.
  - The hypothesis of the gate claim excludes that, and `p_1 = 0` gives triviality.
  - The reverse route is trivial, so the two routes form the intended cycle, and nothing becomes ESTABLISHED.
- **Calibration C.**
  - `EL_3(phi)` has finite image `H` in `GL_(3n)(F_p)`, with `h_ab = 1 + I_n (x) E_ab`.
  - `h_23 h_12 = 1 + E_23 + E_12` differs from `1`, `h_12` and `h_23`, so `beta = h_23 h_12 - h_23 - h_12 + 1` is
    nonzero and `lambda(beta) != 0`.
  - Relations among finitely many `x_ij(a_s)` hold in the subgroup `EL_3(S) <= EL_3(R)`.
  - The Toeplitz subring generated by `s_0, t_0` is the Jacobson algebra, since the monomials `S[0^a] T[0^b]` are
    independent, and it maps onto `F_2` by `s, t -> 1`.
  - Cross-check: redoing the nine products for the natural tensor dual model gives
    `N_23 N_12 = E_23 (x) E_21 + E_12 (x) E_32 + 1 (x) E_31 + E_12 (x) E_31 + E_23 (x) E_31 != 0`, as stated.
- **Artifact Section 5 (Attempts material).** Spot check only: `iota_0(g) iota_1(g) = s_0 g t_0 + s_1 g t_1 = g` for
  `g` with entries in `F_2`, because `t_0 s_1 = 0` and `(1 - e_0)(1 - e_1) = 0`. The counting remarks were not
  re-derived, and nothing established rests on them.

**Reading.** The gate claim `el3-rank-models-factor-through-ring-rank-models` is now equivalent to one product
identity `N_23 N_12 = 0` in characteristic two, together with `N_12^2 = 0` in odd characteristic. By Calibration C,
no finite set of group relations over a finitely represented coefficient subring can prove it. Nothing
decision-level has landed.

## 36. Equidistant root displacement on the locally matricial part (092320434, artifact el3-rank-ring-rigidity Proposition 12): PASS

- **Smith normal form.** `A_k ~= M_(2^k)(F_2)` in the matrix-unit basis `s_w t_v`, with unit `sum s_w t_w = 1`. So
  `a = g_1 e_S g_2` with `g_1, g_2` units of `A_k`, hence units of `R`, and `e_S` a sum of `r = rank(a)` diagonal
  level idempotents.
- **Conjugation.** `diag(d_1, d_2, 1) x_12(b) diag(d_1, d_2, 1)^-1 = x_12(d_1 b d_2^-1)`, so
  `d_1 = g_1, d_2 = g_2^-1` sends `x_12(e_S)` to `x_12(a)`.
  - `GL_3(A_k) = GL_(3 2^k)(F_2)`, and every elementary transvection of `GL_(3m)(F_2)` lies in `EL_3(A_k)`:
    cross-block transvections are there directly, and same-block ones come from `[e_(ab), e_(bc)] = e_(ac)`
    through a third block.
  - So `GL_3(A_k) = EL_3(A_k) <= EL_3(R)`.
- **Idempotent conjugacy.** `x_12(e_S) ~ x_12(1)` for every nonzero `S` at `n = 2` (Sections 22 and 34), realized
  in `GL_3(R) = EL_3(R)`.
- **Weyl.** Permutation matrices move `x_ij(a)` to `x_12(a)`, with no signs in characteristic two. So
  `rk(sigma(x_ij(a)) - 1) = rho` for all nonzero `a` in `A_inf`.
- **Consequence check.** For `U = (Z/2)^N` and `u != 0`:
  - on `F_2[U/Q]`, `u` acts trivially if `u` is in `Q`, and freely by translation otherwise, with normalized rank
    `1/2`;
  - the proportion of codimension-`c` subspaces containing `u` is `[N-1, c]_2 / [N, c]_2 = (2^(N-c) - 1)/(2^N - 1)`;
  - so the uniform sum has displacement `(2^N - 2^(N-c)) / (2(2^N - 1))`, which tends to `(1 - 2^-c)/2`, the same
    for every `u`.
  - The remark that such sums "occur in regular models of level groups" was not checked, and nothing depends on it.
    The free case `rho = 1/2` does occur.

## 37. Root displacement bounds and the dyadic calibration (42e9d058e, lane gk-rk-free): PASS

Items checked: `leavitt-rank-models-have-uniform-root-displacement`, `dyadic-root-displacement-data-admit-trivial-plus-free-models`,
their routes, and `root-displacement-rank-extraction-2026-09-12.md` Sections 1 to 3.

- **Parts 1 and 2 (invariances).** Permutation matrices of `SL_3(F_2)` give `x_(pi 1 pi 2)(a)`. `diag(u, v, 1)` in
  `GL_3(R) = EL_3(R)` gives `x_12(u a v^-1)`.
- **Part 3.** `x_12(a)^2 = 1` gives `N^2 = 0` in `M`, and Sylvester's inequality `rank N^2 >= 2 rank N - n`
  gives `rk N <= 1/2`.
- **Part 4.**
  - `sigma(x_12(a+b)) - 1 = N_a(1 + N_b) + N_b`, so its rank is at most `rk N_a + rk N_b`.
  - `[g,h] - 1 = (gh - hg) g^-1 h^-1`, and `gh - hg = (g-1)(h-1) - (h-1)(g-1)`, so the commutator displacement
    is at most `2 min(rk(g-1), rk(h-1))`.
  - With `x_13(ab) = [x_12(a), x_23(b)]` this gives the product bound.
- **Part 5.**
  - *Upper bound.* `rho_13(a . 1) <= 2 rho_23(1)`.
  - *Lower bound.* Monomial pure infiniteness gives `x a y = 1` with monomials `x, y`. Then
    `x_13(1) = [x_12(x), x_23(ay)]` and `x_23(ay) = [x_21(a), x_13(y)]` (indices `2, 1, 3` distinct). So
    `rho <= 2 rho_23(ay) <= 4 rho_21(a) = 4 rho(a)`.
- **Part 6.** With `N_i = e_i E_12` acting on columns:
  - `N_i(e_2 e_j r) = delta_ij e_1 e_j r`, and `N_i` kills the `e_1`- and `e_3`-coordinates and `e_2(1-e)R`,
    because `e_i(1-e) = 0`.
  - The blockwise map `g`, built from `phi_i : e_i R ~= f_i R` and `psi : B ~= B'` (nonzero finitely generated
    projectives, Bergman import of Section 33), is an automorphism of `R^3`. It satisfies
    `N'_i g(e_2 e_i r) = e_1 f_i phi_i(e_i r) = g N_i(e_2 e_i r)`, and both sides vanish on the other summands.
  - So `g x_12(e_i) g^-1 = x_12(f_i)` simultaneously, and `g` lies in `GL_3(R) = EL_3(R)`.
  - Wording remark: the artifact writes both the standard basis columns and the idempotents as `e_1, e_2, e_3` and
    `e_i`. The argument is correct, but the notation is ambiguous.
- **Calibration, Theorem 2.**
  - `D_k ~= (Z/2)^(2^k)`, because the `e_S` are distinct.
  - Stagewise regular actions extended by the identity are asymptotically multiplicative on each finite set, hence
    exact in the ultraproduct.
  - Order-two elements act freely on free modules, so the displacement is `epsilon/2`, and injectivity holds for
    `epsilon > 0`.
  - The free restrictions over `Q ~= Q'` intertwine along a generator-matching isomorphism.
  - The Boolean function meets parts 2 to 5.
  - Scope: this realizes the listed data (a scalar function on `R` and a model of `D`), not a model of
    `EL_3(R)`. The claim says exactly that.
- **Section 3.** For free `F_2[Q]`-modules, the sum of the images `Im(g_i - 1)` is the augmentation-ideal part, of
  codimension one per copy, giving `epsilon(1 - 2^-n)`. Natural block models over `A_inf` satisfy
  `N_23 N_12 = 0`, while free models do not. Both statements check.

## 38. Unipotent-valued models and the diagonal model of flag-preserving models (1940cc8920, lane gk-rk-extensions): PASS, one implicit step supplied

Items checked: `unipotent-valued-rank-models-of-el3-are-trivial`, `flag-preserving-rank-models-of-el3-reduce-to-their-diagonal`,
their routes, and `el3-rank-model-extensions-2026-09-12.md` Section 4.

- **Lemma 3.** `x^m - 1 = sum_(l>=1) binom(m,l) N^l = N c`, with `c = m(1 + nilpotent)` invertible when `m` is invertible
  in `k`. So `rank(x^m - 1) = rank(N)` exactly, at every stage and over every field.
  - Consequence: if `g` has representatives `g_i` with `g_i - 1` nilpotent and `g^m = 1` in `M`, then
    `rk(g_i - 1) = rk(g_i^m - 1)`, which tends to 0 along omega. So `g = 1`.
- **Theorem 5, characteristic `k != p`.** `x_12(1)^p = x_12(p) = 1` and `p` is invertible in `k`, so `sigma(x_12(1)) = 1`.
  Weyl elements give `x_kl(+-1)`, and `x_ik(a) = [x_ij(a), x_jk(1)]` finishes.
- **Theorem 5, characteristic `k = p`.**
  - The 3-cycle is even, hence in `SL_3(F_2)`, and has order 3. `diag(-1,-1,1)` has determinant 1 and order 2 for odd
    `p`. Both orders are invertible in `k`.
  - `F_p -> R` is a unital ring map, so `iota : SL_3(F_p) = EL_3(F_p) -> EL_3(R)`.
  - `K = ker(sigma iota)` contains `h`, which is not scalar, so `K` is not inside the centre.
  - `PSL_3(F_p)` is simple for every `p`, so `KZ = SL_3(F_p)`. The quotient `SL_3(F_p)/K ~= Z/(Z cap K)` is abelian, and
    perfection gives `K = SL_3(F_p)`.
  - Then all `sigma(x_kl(1)) = 1`, and the commutator identity kills every root.
  - No simplicity of `R`, direct-finiteness failure, property (T) or flag-length bound is used, and the characteristic
    of `k` is arbitrary.
- **Lemma 6.**
  - For block upper triangular matrices, `(xy)_tt = sum_r x_tr y_rt` keeps only `r = t`, and
    `det x = prod det x_tt`.
  - Rank contraction: the rows `union I_t` and columns `union J_t` give a submatrix that is block upper triangular with
    invertible diagonal blocks, hence invertible. So `rank x >= sum rank x_tt`.
- **Proposition 7.** Well-definedness, multiplicativity, (a) via `D(g_i - 1) = D(g_i) - 1`, and (c) via
  `rank((1 - D^-1) g_i) <= rank(D - 1)` all check.
  - *Implicit step supplied.* (b) and part 3 of Theorem 8 need `D_i(g_i)` invertible at finite stages. The
    presentation only gives triangular representatives. They can be made invertible:
    - `g_i h_i` is a triangular representative of 1, so `rank(D(g_i h_i) - 1) = o(n_i)`.
    - Hence `D(g_i) = D(g_i) D(h_i) + ...` has corank `o(n_i)`.
    - Perturbing each singular diagonal block by its nullity keeps triangularity and changes `g_i` by rank `o(n_i)`,
      with every block invertible.
    - Then `D_i(g_i)^-1 g_i - 1` is strictly block upper triangular, hence nilpotent.
    - The author should add this sentence. The results stand.
- **Theorem 8.**
  - *Equivalence.* (a) gives one direction, and Proposition 7(c) with Theorem 5 gives the other.
  - *Part 1.* Unipotent representatives element by element suffice.
  - *Part 2.* Diagonal values commute and `EL_3(R)` is perfect.
  - *Part 3, bounded blocks.*
    - Block-diagonal rank is additive over blocks, and a failing block has rank at least 1 and dimension at most `d`.
      So failing blocks on a finite set `F` carry dimension `o(n_i)`.
    - Blocks nontrivial at `g_0` carry dimension at least `rank >= c n_i`.
    - Choose one exact block per `F`, and take an ultrafilter on finite subsets containing all cones with `d'` fixed.
    - `prod_U GL_(d')(k) = GL_(d')(k^U)`, and `rho(g_0) != 1` because it fails on no `F`.
- **Payoff-host remark.** Prose only, and correct: a nontrivial finite-dimensional image of the finitely generated
  infinite simple `R^x` would be injective and residually finite.
- **Section 4.3.** The reduction of diffuse diagonal models to the general claim by compactness and Markov is prose,
  not a route. It is sound in outline, and the claim is correctly worded as "reduces", with no route landed.

## 39. Dyadic involution profiles kill bounded-degree content (gk-rk-composition): PASS

Items checked: `dyadic-involution-profiles-kill-bounded-degree-content`, route `dyadic-involution-profile-content-proof`,
and `level-group-polynomial-content-2026-09-12.md` Sections 1 to 6.

- **Additivity.** The pieces `e_i` commute with `sigma(H)`, so `sigma(h) - 1 = sum_i e_i(sigma(h) - 1)e_i`, and a
  Sylvester rank function is additive on orthogonal block-diagonal sums. On `M_d(k) (x) C_e`, `(A - 1) (x) 1` is
  equivalent to `rank(A - 1)` copies of `E_11 (x) 1`, and `rk(E_11 (x) 1) = rk(e)/d`.
- **Lemma 1.** Over `k[Z/2]` in characteristic two the indecomposables are `J_1` and `J_2`, and `rank(g - 1)` counts
  the `J_2` blocks. Projective modules restrict to free ones on any subgroup, so their normalized displacement is
  `1/2`.
- **Lemma 2.**
  - As a `<g_r>`-module, `V` is `r J_2 (+) (N - 2r) J_1`, and `V*` is dual, with the contragredient action.
  - The torus weight decomposition of a strict polynomial bifunctor gives `<g_r>`-stable summands `F_(alpha,beta)`,
    each depending on at most `D` effective summands.
  - By naturality the `J_2`-count of `F_(alpha,beta)` depends only on the degree shape and the types of its
    effective summands. The number of multidegrees of a given shape is a constant times
    `C(r, j_1) C(r, j_2) C(N - 2r, t_1) C(N - 2r, t_2)`, a polynomial of degree at most `D` in `r` on
    `0 <= r <= N/2`.
  - A shape with `j_1 = j_2 = 0` has all effective summands trivial, hence no `J_2` blocks. So `P_F(0) = 0`.
  - *Examples.* A tensor factor containing `J_2` is free, so `V^((x) a) (x) V*^((x) b)` gives
    `(N^d - (N - 2r)^d)/2`. For `Lambda^i`, the `J_1`-part series is `(1 + t^2)^r (1 + t)^(N - 2r)`, because
    `Lambda(J_2) = J_1 + J_2 t + J_1 t^2`.
- **Lemma 3.** `Q(2r) - Q(r) = sum_(j>=1) c_j (2^j - 1) r^j` has degree at most `D` and `D + 1` distinct roots, so
  `c_j = 0` for `j >= 1`, and `Q(0) = 0` kills `c_0`.
- **Theorem A.**
  - `f(r) = w_proj/2 + Q(r)` for `1 <= r <= N/2`.
  - The dyadic identity at `r = 1, ..., floor(N/4) >= D + 1` gives `Q = 0`.
  - At `r = 1` the pieces contribute nonnegative amounts summing to zero. Faithfulness gives `P_(F_i)(1) = 0`, so the
    transvections, which are the rank-one involutions, act trivially. They generate `SL_N(F_2)`.
- **Leavitt application.**
  - Proposition 2 of the rigidity artifact (verified in Section 17) holds at `N = 3 . 2^(k+1)` for
    `r <= 3 . 2^k/2 = N/4`, exactly the range needed.
  - **CORRECTED in Section 45.** The endpoint `r = N/4` is not available. The Leavitt application now uses `r < N/4`
    at levels `N >= 4(D + 2)`. The compressor matrix identity is correct, but it does not give the conjugacy.
  - The compressor matrix check: `u = [[s, 1-st],[0, t]]` has inverse `[[t, 0],[1-st, s]]` on both sides, using `ts = 1`
    and `(1 - st)^2 = 1 - st`, and `u diag(a, 1) u^-1 = diag(sat + 1 - st, 1)`.
- **Section 6, a remark, not a claim.**
  - `J/(1 - ST) ~= F_2[z, z^-1]`, and `EL_3(J) <= EL_3(R)` because `J` is a subring.
  - Regular permutation models of the finite images of `EL_3(F_2[z^(+-1)])` pull back to exact homomorphisms.
  - Fixed-point-free permutations have `rank(P - 1) >= 1/2`, and the constants inject.
  - Correct.
- **Trust surface.** The identification of simple algebraic modules of bounded polynomial highest weight with
  values of simple strict polynomial functors (Friedlander–Suslin) only enlarges the list of covered shapes. The
  theorem assumes polynomial pieces directly.
- **Scope, as stated.** The theorem needs an orthogonal splitting into pieces commuting with `sigma(H)`. Projective
  content, unbounded degree and non-split restrictions survive.

## 40. Two root identities localize to diagonal blocks (gk-rk-extensions, artifact Section 4.4, Proposition 9): PASS

Items checked: `two-root-identities-localize-to-diagonal-blocks` and route `two-root-identities-localize-proof`.

- **Descent.** The six displacements have block triangular representatives (invertible after the Section 38 step), so every
  noncommutative polynomial `P` in them does too. `D_i` is additive, multiplicative on block triangular matrices, and unital,
  so `D_i(P(N_i)) = P(D_i(N_i))`. Lemma 6.2 contracts rank.
- **Additivity.** `D_i(N_i) = (+)_t N^(i,t)`, and a block diagonal matrix has rank equal to the sum of its block ranks. So
  `rk(P^D) = lim_omega sum_t rk(P(N^(i,t))) / n_i`.
- **Localized gate.**
  - Weighted-average vanishing gives `N^D_12^2 = 0` and `N^D_23 N^D_12 = 0` in `M`.
  - `sigma_D` is a homomorphism of `EL_3(R)`, so the Weyl reduction of Theorem A applies to it, and its unit roots act by
    matrix units (Section 35).
  - Theorem D plus the no-rank-model hypothesis force `p_1 = 0`, so `sigma_D` is trivial.
  - The equivalence of Theorem 8 (`R` has characteristic `p`) makes `sigma` trivial.
  - In characteristic two the square identity is automatic for `sigma_D` as well.

## 41. Isometry commutator relations (e564d566d6, lane gk-ri-nofd): PASS, one scope remark

Items checked: `leavitt-isometry-commutators-constrain-el3-rank-models`, route `leavitt-isometry-commutators-proof`, and
`leavitt-isometry-commutator-relations-2026-09-12.md` Sections 1 and 2.

- **Expansion.** With involutions `g = 1 + A` and `h = 1 + B`, `[g, h] = (gh)^2 = (1 + A + B + AB)^2`. Expanding with
  `A^2 = B^2 = 0` and `2 = 0`:
  - the linear terms cancel in pairs;
  - `AB` occurs three times;
  - `A . AB`, `AB . B` and the squares vanish.
  So `[g, h] = 1 + AB + BA + ABA + BAB + ABAB`, the five-term form of [RR] Lemma 3.
- **Relations.** `[x_12(t_i), x_23(s_j)] = x_13(t_i s_j)`, which is `x_13(0) = 1` for `i != j` and `x_13(1)` for `i = j`.
  `x_12(1) = x_12(e_0) x_12(e_1)` by additivity with `e_0 + e_1 = 1`.
- **Corner Leavitt family, Section 2.**
  - In a corner of a rank ultraproduct, `T_0 S_0 = e` forces `S_0 T_0 = e`, so `S_1 T_1 = 0`.
  - But `rk(S_1 T_1) >= rk(T_1 S_1 T_1 S_1) = rk(e) > 0`, a contradiction.
  - The circularity remark is correct: placing the images in Peirce corners is the matrix-unit hypothesis.
- **Scope remark on the claim's paragraph.** "not consequences of the group relations available over any finitely
  represented coefficient subring" is true of the four relations jointly, not individually.
  - The diagonal relation alone uses only `t_0 s_0 = 1`. The Toeplitz subring maps onto `F_2`, and the regular models of
    Calibration C satisfy it.
  - An off-diagonal relation alone uses only `t_0 s_1 = 0`, which holds in `M_2(F_2)` via `t_0 -> E_11`, `s_1 -> E_22`.
  - All four together need the Cohn family `t_i s_j = delta_ij`, which has no unital finite-dimensional representation,
    since `rank(TS) <= n < 2n`.
  - The sentence should say "jointly". Nothing rests on it, and the claim correctly does not assert `N_23 N_12 = 0`.

## 42. Toeplitz defect kills coefficient-factoring and residually finite assemblies (gk-ri-counter): PASS, one scope remark

Items checked: `toeplitz-coefficient-factoring-kills-leavitt-el3-rank-models`, `toeplitz-defect-dies-in-every-finite-quotient-of-el3`,
their routes, and `el3-rank-model-toeplitz-assembly-2026-09-12.md` Sections 1 to 5.

- **Toeplitz matrix units.**
  - `e = 1 - st` satisfies `e^2 = e` and `es = 0 = te`, hence `t^m e = 0 = e s^m` for `m >= 1`.
  - For `e_ab = s^a e t^b`: `t^b s^c` is `t^(b-c)` or `s^(c-b)`, and `e t^m e = e(t^m e) = 0`, `e s^m e = 0`. So
    `e_ab e_cd = delta_bc e_ad`.
  - `t^a e_ab s^b = e != 0`. Nonzero matrix units over `F_p` are linearly independent, so their span is a copy of the
    finitary matrices.
- **Theorem A.**
  - `phi(t0) phi(s0) = 1` in a directly finite `D` gives `phi(e) = 0`, so `sigma(x_12(e)) = psi(1) = 1`.
  - `x_12(e) != 1`, and `EL_3(R) = GL_3(R) ~= R^x` is simple (`binary-leavitt-unit-group-is-simple`), so `sigma` is
    trivial.
  - Only the value at `x_12(e)` is used, and `psi` need not be a homomorphism.
  - *Limit version.* Stagewise agreement up to rank `o(1)` gives `sigma(x_12(e)) = 1` in `M`.
- **Theorem B.**
  - The same-block transvections come from `[e_(xy), e_(yz)] = e_(xz)`, so `F_K` is generated by all elementary
    transvections of the finitary group, hence equals `union_n SL_n(F_p)`.
  - *Simplicity of the union.* A normal subgroup containing `g != 1` in `SL_n` meets some larger `SL_m` in a non-central
    element, because `g` is the identity off `n` coordinates. So it contains `SL_m`, since `PSL_m(F_p)` is simple and
    `SL_m(F_p)` is perfect for `m >= 3`, and hence it is everything.
  - An infinite simple group embeds in no residually finite group, and residual finiteness passes to subgroups. So the
    image is trivial.
  - *Consequence.* Finite-image regular models, and their stagewise limits over `S_k ⊇ T`, kill `x_12(e)`. The
    entry-membership remark (`x_12(a)` in `GL_3(S)` forces `a` in `S`) is correct.
- **Section 5, necessary conditions (prose).** (C1) through (C4) are sound. In (C3), a unital block almost-representation
  of `T` in a directly finite `M` has `rho(e) = 0`.
- **Scope remark on the transfer paragraph.** The claim node says the argument transfers to `L_K(1,n)` over any finite
  field. The step needs `EL_3(L_K(1,n))` to be perfect (always true) and simple modulo its centre.
  - Simplicity modulo centre is recorded for `K = F_2, n = 2` (binary simplicity node) and for odd prime fields with
    `n = 2` (odd fp-simplicity node), where `EL_3(L) ~= L^x`.
  - For other `(K, n)`, `EL_3(L)` need not be the unit group, since `M_3(L) ~= L` iff `(n - 1) | 2`, and no landed node
    records simplicity modulo centre.
  - The transfer is therefore established only for those recorded cases. Nothing else rests on it.

## 43. Branch split, rank-modelled calibration, and the refuted dyadic shortcut (1ce1d7bd6a, lane gk-ri-selfsim): PASS

Items checked:
- `el3-two-root-violation-splits-over-leavitt-branches` and route `el3-two-root-branch-split-proof`;
- `rank-modelled-coefficients-violate-two-root-identities` and route `rank-modelled-coefficients-violation-proof`;
- the REFUTED `dyadic-constant-el3-rank-models-satisfy-two-root-identity`, the dead route
  `two-root-identity-by-restriction-to-dyadic-constants`, and artifact Sections 2 to 5.

- **Proposition 1.** `(1+X)(YX)(1+Y) = YX + XYX + YXY + XYXY`, so `n_ik(ab) - XY` is exactly the rest of the five-term
  expansion. `1 + X` and `1 + Y` are units, so the defect has rank `rk(YX)`.
  - *Invariance.* `diag(u, v, w)` sends `x_12(a)` to `x_12(u a v^-1)`, `x_23(b)` to `x_23(v b w^-1)`, and `x_13(ab)` to
    `x_13(u ab w^-1)`. Permutation matrices relabel the triple.
- **Proposition 2.**
  - `[x_12(e_0), x_23(e_1)] = x_13(e_0 e_1) = 1` and symmetrically, so the branches commute.
  - `1 + N_12 = (1 + a_0)(1 + a_1)`.
  - I redid the nine products of `(b_0 + b_1 + b_0 b_1)(a_0 + a_1 + a_0 a_1)`:
    `P_0, P_0 a_1, P_0 b_1, P_0 P_1, P_1, P_1 a_0, P_1 b_0, b_0 a_1, b_1 a_0`. For example
    `b_1 a_0 a_1 = a_0 b_1 a_1 = P_1 a_0`, and `b_0 b_1 a_0 a_1 = b_0 a_0 b_1 a_1 = P_0 P_1`. The grouping checks.
  - *Swap.* `w^2 = s_0 t_0 + s_1 t_1 = 1`, `w s_0 = s_1`, `t_0 w = t_1`, so `w e_0 w = e_1`. `W = diag(w,w,w) = W^-1` lies
    in `GL_3(R) = EL_3(R)`.
  - *Branch maps.* `iota_i(g) = s_i g t_i + (1 - e_i)` is multiplicative, because `t_i(1 - e_i) = 0 = (1 - e_i)s_i`, and
    injective via `t_i iota_i(g) s_i = g`. It sends `x_ab(1)` to `x_ab(e_i)`, so `P_0` is the branch two-root product.
    The bound is subadditivity of rank.
- **Theorem 3.**
  - `nu = GL_3(phi)` lands in the rank ultraproduct `M_3(M_omega)`.
  - *Well defined.* `A (x) A - A' (x) A' = (A - A') (x) A + A' (x) (A - A')`, and
    `rank(X (x) Y) <= rank X . 3n_i`, giving normalized rank at most `2 rk(A - A')`.
  - *Multiplicative.* Exact multiplicativity of the tensor square plus well-definedness give multiplicativity modulo
    rank-null sequences.
  - *The product.* In `N_23 N_12` with `N_ab = E_ab (x) 1 + 1 (x) E_ab + E_ab (x) E_ab`, every term containing `E_23 E_12`
    vanishes. What remains is `E_23 (x) E_12 + E_12 (x) E_23`, with images `e_2 (x) e_1` and `e_1 (x) e_2` from
    `e_3 (x) e_2` and `e_2 (x) e_3`. That is rank 2 out of 9, normalized `2/9`.
- **Corollary 4.**
  - `D_k ~= M_(2^k)(F_2)` sits in `D_(k+1)` by `a -> a (x) I_2`, and `a -> (a (x) I_(2^(n-k)))_n` is a unital rank model
    of `D`.
  - `s_i s_u t_v t_i = s_(iu) t_(iv)`, so `iota_i(x_ab(d)) = x_ab(s_i d t_i)` lies in `EL_3(D)`.
  - `W` lies in `GL_6(F_2) = EL_3(D_1)`.
  - So the dyadic shortcut is false, and the dead route is correctly invalidated. Its implication is valid, but its
    prerequisite is false.
  - `D` together with `s_0, t_0` generates `R`, since `s_1 = w s_0` and `t_1 = t_0 w`. `R` has no rank model because
    direct finiteness turns `s_0 t_0 + s_1 t_1 = 1` into `0 = 1` in characteristic two.
- **Section 6 bound.** `rk(N_12 N_23 - n_12(t_i) n_23(s_i)) <= delta(1,1) + delta(t_i, s_i)` follows from Proposition 1,
  because both products agree with `n_13(1)` up to their defects.

## 44. Shifted root pair and finite-subgroup rank data (8831a28b31, lane gk-rk-unipotent, artifact el3-two-root-identities Section 6): PASS

Items checked: `shifted-root-pair-conjugates-to-idempotent-root-pair`, `finite-subgroup-rank-data-cannot-force-two-root-identity`,
their routes, and artifact Sections 6.1 to 6.3.

- **The invariant `T`.** Simultaneous conjugation carries kernels and images to kernels and images, so `T` is invariant up to
  isomorphism.
  - *Unit pair.* The common kernel is `e_1 R`, contained in the image sum `e_1 R + e_2 R`, so `T = 0`.
  - *Shifted pair.* `t_0 v = 0` iff `v = s_1 t_1 v`, and left multiplication by `s_0` is injective. So the common kernel is
    `e_1 R + e_2 s_1 R`, the image sum is `e_1 R + e_2 s_0 R`, and `s_0 R cap s_1 R = 0`. Hence `T ~= s_1 R != 0`.
  - *Idempotent pair.* The common kernel is `e_1 R + e_2 e_1 R + e_3 e_1 R`, where `e_2` in "`e_2 e_1 R`" is the basis column
    and `e_1` the idempotent. The image sum is `e_1 e_0 R + e_2 e_0 R`. So `T ~= R/e_0 R + (e_1 R)^2 ~= R`.
  - So the shifted pair is not conjugate to the unit pair.
- **The explicit intertwiner.**
  - `g(e_0 E_12)` has second column `(t_0 e_0, s_1 s_0 t_1 e_0, 0) = (t_0, 0, 0)`.
  - `(t_0 E_12) g` has first row `t_0 (row 2 of g) = (0, t_0, 0)`, using `t_0 s_1 = 0`.
  - `g(e_0 E_23)` has entry `(2,3)` equal to `(s_0 t_0 + s_1 s_1 s_0 t_1) e_0 = e_0`, and `(s_0 E_23) g` has second row
    `s_0 (0, 0, t_0)`, also giving `e_0`.
  - *Invertibility.* The four terms of row 2 have ranges `s_0 R, s_1 s_0 R, s_1 s_1 s_0 R, s_1 s_1 s_1 R`, from the prefix code
    `0, 10, 110, 111`.
    - Injective: `gv = 0` forces `t_0 v_1 = t_1 v_1 = 0`, `t_0 v_2 = t_1 v_2 = 0` and `t_0 v_3 = t_1 v_3 = 0`, so `v = 0`.
    - Surjective: `v_1 = s_0 w_1 + s_1 t_0 t_1 w_2`, `v_2 = s_0 t_0 w_2 + s_1 t_0 t_1 t_1 w_2` and
      `v_3 = s_0 w_3 + s_1 t_1 t_1 t_1 w_2` give `gv = w`, using the prefix-code decomposition of 1.
  - So `g` lies in `GL_3(R) = EL_3(R)`.
- **Theorem F (free profile).**
  - `(1 + E_12)(1 + E_23)` has square `1 + E_13 != 1`, so it has order 4, and `UT_3(F_2) ~= D_8`.
  - `F_2[D_8]` has basis `1, x, y, xy, yx, xyx, yxy, xyxy` with `x^2 = y^2 = 0` and `xyxy = yxyx`. Left multiplication by
    `yx` sends `1, y, yx` to `yx, yxy, xyxy` and kills the rest (for example `yx . yxy = xyx . y^2 = 0`). Its rank is 3, so
    `r_D = 3/8`.
  - Restriction holds because `F_2[L] ~= F_2[K]^([L:K])`. Isomorphism invariance holds because isomorphic groups have
    isomorphic regular modules.
  - The scope of the consequence is stated accurately: it excludes only arguments built from relations inside finite
    subgroups, inclusions, conjugacies and per-subgroup rank data.
- **Side facts.**
  - `<x_12(1), x_12(t_0), x_23(1), x_23(s_0)>` is Heisenberg with root parts `span{1, t_0}` and `span{1, s_0}` and central part
    `span{1, s_0, t_0}`, since `t_0 s_0 = 1`. Its order is `4 . 4 . 8 = 128`.
  - `[[0, t_0],[s_0, 1]]^2 = [[1, t_0],[s_0, 1 + s_0 t_0]]`, and its cube is `[[t_0 s_0, 2 t_0],[s_0 + s_0 t_0 s_0, 1]] = 1`.
  - `[[e_1, s_0],[t_0, 1]]^2 = [[1, s_0],[t_0, 0]]`, and its cube is 1.
  - So both products have order 3, and each pair generates `S_3`.
- **Section 6.2.** The expansion
  `YX = Y'X' b''a'' + b'' X''Y' + X' Y''a'' + Y''X''` checks, using the commutations `[a', b''] = [a'', b'] = 1`.

## 45. CORRECTION to Sections 17 and 39: the dyadic identity excludes the endpoint; corrected Proposition 2, Lemma 13, Theorem G: PASS

**What was wrong in this artifact.** Section 17 passed Proposition 2 of `el3-rank-ring-rigidity-2026-09-12.md` for all
`1 <= r <= 3m/2`. It accepted the corner conjugacy `g ~ g (+) I` in `R^x` from the author's compressor attribution without
re-deriving it. Section 39 then called `r <= N/4` "exactly the range needed" and checked only the compressor matrix
identity. Lane `gk-l-gate-neg` found the gap (1c7283c42c, e68b687037). The conjugacy fails at the maximal type, so
Proposition 2 holds only for `1 <= r < N/4`. The matrix identity `u diag(a,1) u^-1 = diag(sat + 1 - st, 1)` is
correct, but it is a conjugacy in `GL_2(R)`, not between `a` and `sat + 1 - st` in `R^x`, so it cannot justify the step.

**Corrected Proposition 2, re-derived.**
- **Absorption.** `R = (+)_(|a|=k) s_a R` identifies `R^3` with `F_2^(3m) (x) R` compatibly with `A_k = M_m(F_2)`, so
  `(R^3, g) ~= W (x) R` as modules with an operator, where `W = (F_2^(3m), g)`.
  - `g (+) I = s_0 g t_0 + (1 - s_0 t_0)` entrywise, and `R^3 = s_0 R^3 (+) s_1 R^3` with `v -> s_0 v` intertwining. So
    `(R^3, g (+) I) ~= (R^3, g) (+) (R^3, 1)`.
- **Conjugacy.** Conjugacy in `GL_3(R)` is isomorphism of modules with an operator.
  - `W = r J_2 (+) (3m - 2r) J_1`, and `R^j ~= R` for `j >= 1`.
  - If `3m - 2r >= 1`, both modules are `J_2 (x) R (+) J_1 (x) R`, so they are conjugate.
  - If `r = 3m/2`, `(R^3, g) ~= J_2 (x) R` has `T = ker n / (ker n cap Im n) = 0`, while the `J_1 (x) R^3` summand of
    `g (+) I` gives `T ~= R`. So they are not conjugate.
- Doubling `g = g (x) I_2` gives type `2r`, so `f_(k+1)(2r) = f_(k+1)(r)` for `1 <= r < 3m/2 = N/4`. PASS in the corrected
  range.
- **Downstream check.** `dyadic-involution-profiles-kill-bounded-degree-content` (corrected at 1969803707) now assumes
  `f(2r) = f(r)` at `D + 1` distinct integers `1 <= r <= N/4`.
  - Step 2 needs only `r >= 1` and `2r <= N/2`, both valid there. Lemma 3 needs `D + 1` points.
  - The Leavitt application takes `r = 1, ..., D + 1 < N/4`, guaranteed by `N >= 4(D + 2)`. PASS.
  - The flag-diagonal inheritance I confirmed to that lane still holds, in the corrected range.

**Lemma 13 (root-subgroup compressor): PASS.**
- `c` sends `e_1 R` and `e_2 R` to `e_1 s_0 R` and `e_2 s_0 R`, and `e_3 R` onto `e_1 s_1 R + e_2 s_1 R + e_3 R ~= R`. It is
  bijective.
- On `e_2 s_0 r`, both `c x_12(a) c^-1` and `x_12(s_0 a t_0)` add `e_1 s_0 a r`. On `e_2 s_1 R` the latter adds
  `e_1 s_0 a t_0 s_1 r = 0`. On the other pieces both are the identity.
- For `g` in `GL_2(R)`, `e_j s_0 r -> sum_i e_i s_0 g_ij r = sum_i e_i (s_0 g_ij t_0)(s_0 r)`, and it is the identity on the
  `s_1` parts, since `(1 - s_0 t_0) s_1 = s_1`. That gives `(s_0 g t_0 + 1 - s_0 t_0) (+) 1`.
- `B = union_k c^-k U_12(R) c^k` is an increasing union of abelian groups normalized by `c`, so `<U_12(R), c>` is
  metabelian. Recorded as a pointer, correctly.

**Theorem G (6bdbec8cae, `sofic-subgroups-carry-rank-models-violating-two-root-identity`): PASS.**
- **Bad points.** `B_i` collects multiplicativity failures on `D x D`, `phi(1) != id`, and fixed points of nontrivial `d`,
  so `|B_i| = o(n_i)`. The complement of `G_i` lies in `B_i` together with the eight preimages `phi(d)^-1(B_i)`, so its size
  is at most `9|B_i|`.
- **Orbits.** For `x` in `G_i`:
  - multiplicativity holds at every `phi(d) x`, so `phi` restricts to an honest action on `O(x)`;
  - `phi(d) x = phi(d') x` forces `phi(d'^-1 d) x = x`, hence `d = d'`, so `O(x)` has 8 points;
  - meeting orbits coincide, because `phi(D) y = O(x)` for `y` in `O(x)`.
- **Correction.** `psi` equals `phi` on the union `U_i` and the identity elsewhere. It is a genuine homomorphism with
  `d_H(psi(d), phi(d)) <= 9|B_i|/n_i`.
- **Rank.** `F_2^(U_i)` is free over `F_2[D_8]`, and the value `3/8` comes from Section 44. The model is exact because
  rank distance is bounded by Hamming distance.
- **Scope list.**
  - `<diag(u,u^-1,1), x_12(1), x_23(1)>` lies in `UT_3(R) x| Z` (solvable).
  - `EL_3(A_inf)` is locally finite.
  - `F_2[s_0] ~= F_2[x]`, since the monomials `S[0^j]` are independent, so `EL_3(F_2[s_0])` is finitely generated and
    linear over `F_2(x)`, hence residually finite.
  - All are sofic.

## 46. Anti-central rank models kill ternary corner witnesses (38533db3fe, lane gk-l3-state): theorem PASS, Corollary 3.2 wrong as stated

Items checked: `anti-central-rank-models-kill-ternary-corner-witnesses`, route
`anti-central-rank-models-kill-ternary-corner-witnesses-proof`, and `ternary-corner-state-sources-2026-09-12.md` Sections 1 to 3.

- **Lemma 1.1, pressure point 1.** `w^2 = d^2 = 1`. `dw = s0 t1 - s1 t0`, then `(dw)d = -s0 t1 - s1 t0 = -w`, so `dwd = zw`. Also
  `wd = -s0 t1 + s1 t0` with `(wd)^2 = -s0 t0 - s1 t1 = z`, so `<w, d>` is dihedral of order 8 with centre `<z>`.
- **Lemma 1.2.**
  - `e^2 = 4(2 + 2[w]) = e`, and `eps_-[z] = 2([z] - 1) = -eps_-`.
  - So `[d] e_- [d]^-1 = eps_- 2(1 - [w])`, the sum is `4 eps_- = eps_-`, and the two summands are orthogonal.
  - Conjugation by the unit `eps_-[d]` of `S_Gamma` makes them equivalent.
- **Theorem 2.1(a), pressure point 2.** `f^2 = 4(2 - 2 sigma(z)) = f`, since `sigma(z)^2 = 1`. `f = 0` iff `sigma(z) = 1`, and `f`
  commutes with `sigma(Gamma)` because `z` is central.
- **Theorem 2.1(b), pressure point 2.** `sigma(g)f sigma(h)f = sigma(gh)f`, so the linear extension is an algebra map
  `F_3[Gamma] -> fMf` with `1 -> f`. From `sigma(z)f = 2(sigma(z) - 1) = -f` we get `eps_- -> 4f = f` and `eps_+ -> 0`, so the
  restriction to `S_Gamma` is unital.
- **Theorem 2.1(c), pressure point 3.**
  - Read `rho` as a Sylvester matrix rank function. This holds for `M_n(k)` and rank ultraproducts; in general by the
    map-to-matrix correspondence.
  - *Additivity.* For orthogonal idempotents, `p + q = BA` and `diag(p, q) = AB` with `A = (p; q)`, `B = (p, q)`, and
    `A = ABA`. So `rho(p + q) = rho(p) + rho(q)`.
  - *Invariance.* `rho(xy) <= rho(x) = rho(xyx) <= rho(yx)`, and symmetrically.
  - So `s` is additive on `V(S_Gamma)`, nonnegative, and extends to `K_0` with `s([eps_-]) = 1`. Positivity of `rho` is used
    only for `rho(f) > 0`.
- **Theorem 2.1(d), pressure point 4.** With `x = c e_-` and `y = e_- b`:
  - `xy = eps_-`, and `p = yx` is idempotent because `b` and `c` absorb `eps_-`;
  - `p e_- = e_- p = p` and `eps_- ~ p`, so `s(eps_-) = s(p) <= s(e_-) = 1/2`, a contradiction.
- **Corollary 3.1, pressure point 5: PASS.**
  - `b = eps_- b` lies in `F_3[Gamma]`.
  - Finite-dimensional representations in characteristic three, and regular representations over `F_3` of finite quotients,
    are rank algebras with faithful images. So `z` lies in the finite residual, and `Gamma` is not residually finite.
- **Corollary 3.3: PASS.** A normal subgroup `N` not containing `z` has `N<z>/<z>` trivial or all of `PG`. In the first case
  `N <= <z>`, so `N = 1`. In the second, `G/N` is a quotient of `<z>`, and perfection forces `N = G`, which contains `z`.
- **Corollary 3.2, and the claim's "implies that filter": wrong as stated.**
  - Corollary 3.1 constrains `Gamma = <z, w, d, supp b, supp c>`, which contains `d`.
  - `ternary-corner-witnesses-need-non-linear-sofic-support` (Section 11, Theorem C) constrains `H = <z, w, supp b, supp c>`,
    which need not contain `d`.
  - Linear soficity passes to subgroups, so "`H` is not `F_3`-linear sofic" implies "`Gamma` is not", not conversely. So
    Corollary 3.1 does not imply that claim.
  - The proof really needs `d`. Without it, `sigma(w) f = f` is possible, `s(e_-) = 1`, and there is no contradiction.
  - The two filters are incomparable. Corollary 3.1 needs only one rank model moving `z`, but applies to the larger group
    `Gamma`. Theorem C needs separating approximations, but applies to `H`.
  - *Requested correction.* Replace "implies that filter" on the claim (distinct_from and Consequences) and in artifact
    Corollary 3.2 with "complements that filter: weaker model hypothesis, larger support group `<H, d>`". Nothing
    established rests on the implication, and no route encodes it.

## 47. The two-root identity is corner-local (e5f2fbc35f, lane gk-gate-nonsofic): theorem PASS; Corollary 2.3 and one remark hold only up to conjugacy

Items checked: `two-root-identity-is-corner-local-for-leavitt-rank-models`, route `two-root-identity-corner-locality-proof`, and
`two-root-identity-nonsofic-mechanism-2026-09-12.md` Sections 1 and 2.

- **Lemma 2.1.**
  - `TS = 1`, `T(1 - ST) = 0` and `(1 - ST)S = 0` give `iota_P(g) iota_P(h) = S gh T + (1 - ST)^2 = iota_P(gh)`, with
    `iota_P(1) = 1`.
  - `T iota_P(g) S = g`, so `iota_P` is injective.
- **Theorem 2.2.**
  - *Per-model chain.* In characteristic two every `N_ab^2 = 0`, and `N_23 N_12 = 0` gives matrix units by Theorem A with
    Weyl symmetry (Section 35). Theorem D then gives `p_1 = 0` or a unital homomorphism `R -> p_1 M p_1`. The latter is
    excluded because corners of rank ultraproducts are directly finite and `R` is simple and not directly finite
    (Sections 6 and 22).
  - *(3) implies (1).* `tau = sigma o iota_P` is a rank model of `R^x`. Its unit pair values are
    `sigma(iota_P(x_ab(1)))` under the same code identification `R^x = EL_3(R)`, so (3) is `tau`'s two-root identity and
    `tau` is trivial. `iota_P(R^x)` is nontrivial and `R^x` is simple, so `ker sigma = R^x`.
  - PASS. This uses only that `iota_P` is an endomorphism of the group.
- **Corollary 2.3, and the remark `iota_P(x_ij(a)) = x_ij(s_P a t_P)`: false as literal equalities, true up to one
  simultaneous conjugation.**
  - *Counterexample.* Under the code `zeta = (0, 10, 11)`, `x_12(1) = 1 + S[0]T[10]`. So `iota_0(x_12(1)) = 1 + S[00]T[010]`,
    while `x_12(e_0) = 1 + S[0] e_0 T[10] = 1 + S[00]T[100]`. These are distinct basis monomials.
  - *Why.* The entrywise corner map `iota'_0((g_ij)) = (s_0 g_ij t_0) + (1 - e_0)I` is, in `R`, `g -> VgW + (1 - VW)` with
    `V = sum_i S[zeta_i] s_0 T[zeta_i]` and `W = sum_i S[zeta_i] t_0 T[zeta_i]`, so `WV = 1`. That is a different isometry
    from `s_0`.
  - *Repair.* Choose an isometry `Y` with `YY* = 1 - VW` (the complement is `~= R^3 ~= R`), and put `u = V t_0 + Y t_1`,
    `v = s_0 W + s_1 Y*`.
    - `WY = 0` and `Y*V = 0`, so `uv = VW + YY* = 1` and `vu = 1`.
    - `u s_0 = V` and `t_0 v = W`, so `u iota_0(g) u^-1 = VgW + Y t_1 s_1 Y* = iota'_0(g)`.
    - Hence `(iota_0(x_12(1)), iota_0(x_23(1)))` is simultaneously conjugate in `R^x` to `(x_12(e_0), x_23(e_0))`.
  - Every rank statement in Corollary 2.3 and in the isometry remark therefore holds as stated. So does
    "`sigma` trivial iff `rk(n_23(s_0) n_12(t_0)) = 0`", through Section 44. Only the equalities must be read as
    conjugacies.
  - *Requested correction.* "`iota_0(x_ab(1))` is conjugate, by one unit, to `x_ab(e_0)`", and likewise for general `P`.
- **Section 1.** `G = <Gamma, u, v> = EL_D(R) = R^x` is recorded, so subgroups containing the configuration are all of `R^x`.
  Correct as a remark.
- **Section 3 (audit).** Spot check of placement: `S[10000]T[100010]` has domain and range inside `[1]`, so it annihilates
  and is annihilated by the units on `[0]`, and `x'` commutes with `Gamma`. The rest is prose, correctly not landed as a
  route.

**Section 47 addendum: the correction (851def4ec3) PASS.** Artifact Lemma 2.3 and Corollary 2.4 of
`two-root-identity-nonsofic-mechanism-2026-09-12.md` now state conjugacies. I re-derived the general-prefix form.
- *Setup.* Take `Z*Z = 1` and `ZZ* = 1 - s_P t_P`. Then `Z = (1 - s_P t_P)Z`, so `t_P Z = 0 = Z* s_P`.
- *Units.* With `Y = sum_i S[zeta_i] Z T[zeta_i]`, `u_P = V_P t_P + Y Z*` and `v_P = s_P W_P + Z Y*`:
  - `W_P Y = 0` and `Y* V_P = 0`, and `YY* = 1 - V_P W_P`, `Y*Y = 1`;
  - so `u_P v_P = V_P W_P + YY* = 1` and `v_P u_P = s_P t_P + ZZ* = 1`.
- *Intertwining.* `u_P s_P = V_P`, `t_P v_P = W_P`, `u_P Z = Y` and `Z* v_P = Y*`. Hence
  `u_P iota_P(g) v_P = V_P g W_P + YY* = V_P g W_P + (1 - V_P W_P)`.
- *Entrywise action.* `V_P S[zeta_a] = S[zeta_a] s_P` and `T[zeta_b] W_P = t_P T[zeta_b]`, so this map sends
  `x_ab(r)` to `x_ab(s_P r t_P)`.
- *Existence of `Z`.* The complement `1 - s_P t_P` is a nonzero sum of cylinder idempotents, so its range is `~= R`.

## 48. Compressor conjugation of root pairs (gk-gate-compress): c-half PASS, c'-half FALSE as stated, corrected form given

Items checked: `compressors-conjugate-leak-free-root-pairs`, route `compressors-conjugate-leak-free-root-pairs-proof`, and
`el3-compressor-root-pair-calculus-2026-09-12.md` Section 1.

**Notation.** Below, `T[10] = t_0 t_1` is the adjoint of `S[10] = s_1 s_0`, so `T[10] S[10] = 1`, and `T[11] = t_1 t_1`. The
artifact writes both as "`t_1 t_0`" and uses the literal product `t_1 . t_0` in some steps.
- *The adjoint reading is forced.* The inverse `(x,y,z) -> s_0 x + s_1 s_0 y + s_1 s_1 z` is two-sided only for
  `psi(r) = (t_0 r, T[10] r, T[11] r)`.
- *The literal reading fails.* `r -> (t_0 r, t_1 t_0 r, t_1 t_1 r)` kills `s_1 s_0 R`, so `c` and `c'` would not be units.

**`c`, Lemma 1 and the first bullet of Lemma 2: PASS.**
- *Conjugating `x_12`.* `c x_12(a) c^-1 = x_12(s_0 a t_0)` (Lemma 13, Section 45).
- *Conjugating `x_23`.* `N = c x_23(b) c^-1 - 1` kills `c(e_1 R) + c(e_2 R)` and sends `c(e_3 r)` to `e_2 s_0 b r`.
  - `e_1 s_1 t_1 v = c(e_3 s_0 t_1 v)`, because `T[10] s_0 = 0`.
  - `e_2 s_1 t_1 v = c(e_3 s_1 s_0 t_1 v)` and `e_3 v = c(e_3 s_1 s_1 v)`.
  - So row 2 is `(s_0 b s_0 t_1, s_0 b s_1 s_0 t_1, s_0 b s_1 s_1)`.
- *Leak-free condition.* The first two entries vanish iff `b s_0 = 0 = b s_1 s_0`, iff `b = b S[11]T[11]`, which lies in
  `R t_1 t_1`. Then `c x_23(b' t_1 t_1) c^-1 = x_23(s_0 b')`.
- *Rank identity.* `delta(a, b' t_1 t_1) = delta(s_0 a t_0, s_0 b')` holds.

**`c'`, Lemma 1: PASS in the adjoint reading.**
- `c'(e_1 v) = e_1 T[11] v + e_2 s_1 t_0 v + e_3 s_1 T[10] v`.
- `c' x_23(b) c'^-1 = x_23(s_0 b t_0)`: `e_3 s_1 t_1 v = c'(e_1 s_1 s_0 t_1 v)` is killed, `e_1 v = c'(e_1 s_1 s_1 v)`, and
  `e_2 s_1 t_1 v = c'(e_1 s_0 t_1 v)`.
- `c' x_12(a) c'^-1 - 1` has column 2 equal to `(T[11] a t_0, s_1 t_0 a t_0, s_1 T[10] a t_0)`.

**`c'`, the second bullet of Lemma 2, Corollary 3 and the claim's second conjugacy: FALSE as stated.**
- *The step that fails.* The proof says "`s_1 t_0 a t_0` and `s_1 t_1 t_0 a t_0` vanish iff `t_0 a t_0 = 0`". That reads the
  third entry as literally `s_1 t_1 (t_0 a t_0)`. The correct entry is `s_1 t_0 t_1 a t_0`, which vanishes iff
  `t_0 t_1 a = 0`.
- *Counterexample.* Take `a = s_1`, which lies in `s_1 R`.
  - `c'(e_1 s_1 t_0 v) = e_1 t_1 t_0 v + e_3 s_1 t_0 t_0 v`, so `c' x_12(s_1) c'^-1 - 1` has entry `(3,2)` equal to
    `s_1 t_0 t_0 != 0`.
  - So the conjugate leaks into the 32 root and is not a root element.
  - *The artifact's own check.* Its commutator check has the same slip. For `beta = s_1 a' b`, column 3 is
    `(t_1 a' b t_0, 0, s_1 t_0 a' b t_0)`, and the last entry is generally nonzero.
- *Corrected statement.* `c' x_12(a) c'^-1` is a root element iff `t_0 a = 0` and `t_0 t_1 a = 0`, iff
  `a = S[11]T[11] a`, iff `a` lies in `s_1 s_1 R`. For `a = s_1 s_1 a''`:

  ```text
  c' (x_12(s_1 s_1 a''), x_23(b)) c'^-1 = (x_12(a'' t_0), x_23(s_0 b t_0)),     delta(s_1 s_1 a'', b) = delta(a'' t_0, s_0 b t_0).
  ```

  - *Consistency.* `[x_12(a'' t_0), x_23(s_0 b t_0)] = x_13(a'' b t_0)`. For `beta = s_1 s_1 a'' b`, column 3 of
    `c' x_13(beta) c'^-1 - 1` is `(a'' b t_0, 0, 0)`, since `t_0 t_1 s_1 s_1 = t_0 s_1 = 0`.
  - *Symmetry.* The result mirrors the `c` half: two-letter cylinders `R t_1 t_1` and `s_1 s_1 R`.
- *Downstream.* Only the claim, its route and the artifact cite this claim. Nothing else consumes the false half.
- *Requested correction.* Replace `s_1 R` with `s_1 s_1 R`, and `x_12(t_1 a' t_0)` with `x_12(a'' t_0)`, in the claim, in
  Lemma 2, in Corollary 3 and in its check. Use `T[10]` or `t_0 t_1` for the adjoint word throughout.

**Section 48 addendum: the correction (53fcaae60a) PASS.** Lemma 2's second bullet, Corollary 3, the commutator check and
the claim now carry the corrected `c'` half. I re-checked the proof as written.
- `s_1 t_0 a t_0 = 0` iff `t_0 a t_0 = 0`, cancelling `s_1` by `t_1`, iff `t_0 a = 0`.
- `s_1 t_0 t_1 a t_0 = 0` iff `t_0 t_1 a = 0`.
- Both together give `a = s_1 t_1 a` and `t_1 a = s_1 t_1 t_1 a`, so `a = s_1 s_1 t_1 t_1 a`.
- The surviving entry is `t_1 t_1 s_1 s_1 a'' t_0 = a'' t_0`.
- The check gives column 3 equal to `(a'' b t_0, 0, 0)`.
The verdict on `compressors-conjugate-leak-free-root-pairs` is now PASS as corrected.

## 49. Scalar two-root rank data cannot force the identity (f4cbbb4ea9, lane gk-gate-compress): PASS

Items checked: `scalar-two-root-rank-data-cannot-force-the-identity`, route `scalar-two-root-rank-data-calibration-proof`, and
artifact Section 2.

- **Unit moves.** `diag(g_1, g_2, g_3) x_ij(a) diag(...)^-1 = x_ij(g_i a g_j^-1)`, and `GL_3(R) = EL_3(R)`.
  - So `delta(u, v) = delta(1,1)` for units `u, v`.
  - `diag(w,w,w)` fixes `x_23(1)` and sends `x_12(e_0)` to `x_12(e_1)`, which gives `delta(e_0,1) = delta(e_1,1)`.
- **Lemma 4, with the corrected `c'`.**
  - *Forward moves.* `c` requires `b = b' t_1 t_1`, a zero divisor with `b s_0 = 0`. `c'` requires `a = s_1 s_1 a''`, with
    `t_0 a = 0`.
  - *Inverse moves.* These start from `(s_0 a t_0, s_0 b')` or `(a'' t_0, s_0 b t_0)`. Each of these entries is killed by
    `s_1` on the right or by `t_1` on the left, so none is a unit.
  - So every compressor move, in either direction, has a non-unit input, while unit moves preserve unit pairs.
  - By induction, chains of elementary moves from `(1,1)` reach only unit pairs. The lemma is about elementary moves only,
    as stated, not about arbitrary conjugacy in `GL_3(R)`.
- **Subadditivity.**
  - `n_12(a + a') = X + X' + XX'` with `X, X'` commuting and square-zero, so `Y n_12(a+a') = YX(1 + X') + YX'`.
  - `n_23(b + b') X = YX + (1 + Y) Y'X`.
  - Units do not raise rank, which gives both inequalities.
- **Proposition 5.** `x_12(a) != 1` iff `a != 0`, and conjugation preserves nontriviality, so (i) holds. If `a + a' != 0`,
  then one of `a`, `a'` is nonzero, so (ii) holds. (iii) is immediate. So `eps [a != 0][b != 0]` meets (i)–(iii) with
  value `eps` at `(1,1)`.
- **Scope.** This is exactly what the title says: scalar `delta`-data under same-shape conjugacy, subadditivity and
  vanishing. Operator identities are not covered.

## 50. No covariant rank model of Thompson's V (lane w3-gate-v): PASS, second independent derivation

Items checked: `thompson-v-cantor-system-has-no-covariant-rank-model`, route `thompson-v-covariant-rank-model-halving-proof`, and
`thompson-v-rank-models-cantor-covariance-2026-09-12.md` Sections 2 and 3. The assigned verifier named on the claim is
`w3-vf-linear`; this is a second derivation from the rank-gate family verifier.

- **Lemma 2.1.**
  - *(a)* `rk(axb) <= rk(x)` in both directions.
  - *(b)* With approximate idempotents `e_k, f_k` and rank-null cross products:
    - `im e_k cap im f_k` lies in `im(e_k - e_k^2) + im(e_k f_k)`, which has dimension `o(n_k)`;
    - `im e_k` lies in `im(e_k + f_k) + im(e_k^2 - e_k) + im(f_k e_k)`, and symmetrically for `f_k`;
    - so `rank(e_k + f_k) >= rank e_k + rank f_k - o(n_k)`.
- **Lemma 2.2.** Splitting cylinders equalizes the counts on both sides. The cylinders of `A` and of `X \ A` form a complete
  prefix code, so one prefix replacement maps `A` onto `B`.
- **Theorem 2.3.**
  - `mu(A) = rk(rho(1_A))` is additive on disjoint clopens and invariant under `V` by covariance.
  - By transitivity `mu` is constant, equal to `c`, on proper nonempty clopens.
  - Then `mu([0]) = mu([00]) + mu([01])` gives `c = 2c`, while `mu([0]) + mu([1]) = 1`. Contradiction.
- **Proposition 2.4.**
  - The four replacements are between complete prefix codes, and `h_1[0] = [00]`, `h_2[0] = [01]`, `h_3[1] = [10]`,
    `h_4[1] = [11]`.
  - `|m(h_i C) - m(C)| <= eps`, since `rank(A e_C A^-1) = rank(e_C)`.
  - So `m([0]) >= 2m([0]) - 2eps` and `m([1]) >= 2m([1]) - 2eps`, giving `1 <= 4 eps`.
  - The remark that `sigma` need not be almost multiplicative is correct.
- **Section 3.4.**
  - `S[a]T[a]` are orthogonal idempotents summing to 1 over any complete prefix code, and they span a unital copy of
    `LC(X, F_2)`.
  - For a prefix-replacement unit `g = sum_i S[b_i]T[a_i]`, `g S[a_i c]T[a_i c] g^-1 = S[b_i c]T[b_i c]`.
  - So the filter holds as stated. It rules out covariance, not rank models of `R^x` themselves.

## 51. The Thompson V rank gate nodes (lane w3-gate-v): routes PASS, one wording remark

Items checked:
- the OPEN claims `thompson-v-has-no-nontrivial-f2-rank-model` and `thompson-v-is-f2-linear-sofic`, which refute each other;
- the routes `non-linear-sofic-via-thompson-v-rank-triviality`, `thompson-v-f2-linear-sofic-from-soficity` and the dead
  `thompson-v-f2-linear-sofic-via-covariant-cantor-truncation`;
- artifact Sections 4 and 5.

The assigned verifier of this lane is `w3-vf-linear`; this is a second check.

- **`non-linear-sofic-via-thompson-v-rank-triviality`: valid.**
  - `V` is countable and nontrivial. An `F_2`-linear sofic approximation gives an injective homomorphism into a
    characteristic-two rank ultraproduct, which the prerequisite makes trivial.
  - The second paragraph is also correct: a linear sofic approximation of `R^x` restricts injectively to `V`. Simplicity is
    not even needed there.
  - The route fires iff the prerequisite is established, and it is correctly OPEN.
- **`thompson-v-f2-linear-sofic-from-soficity`: valid.** It is a specialization of `sofic-implies-linear-sofic-over-every-field`.
- **The dead covariant-truncation route: correctly invalidated.**
  - Compressions of a covariant Cantor module with normalized boundary tending to 0, under finitely many elements of `V` and
    the cylinder idempotents, assemble along omega into an exact covariant pair `(sigma, rho)` in the ultraproduct, after
    rounding the approximate idempotents (Section 38).
  - Theorem 2.3 forbids such a pair.
  - Proposition 2.4 quantifies the obstruction at the finite stage.
- **Section 4.4.** `V <= R^x` (`leavitt-cylinder-swaps-generate-thompson-in-el`), and nontrivial homomorphisms of the simple
  group `R^x` are injective. So rank triviality of `V` gives rank triviality of `R^x` in characteristic two, the binary case of
  the instance claim. Declining to land a route into the all-characteristics instance claim is correct scoping.
- **Wording remark.** The `distinct_from` of `thompson-v-has-no-nontrivial-f2-rank-model` calls it "strictly stronger" than the
  binary case of the instance claim. The implication is proved, but strictness is not: nobody knows a nontrivial rank model of
  `V` that fails to extend to `R^x`. Suggested wording: "at least as strong; the converse is not known". The artifact's
  Section 4.4 already says that.
- **Section 5.2 (heuristic).**
  - Cylinder swaps with proper union form one conjugacy class, by the refinement argument of Lemma 2.2.
  - `pi = pi_0 pi_1`, with the factors commuting, gives `N = N_0(1 + N_1) + N_1`, so `rk N <= 2 rk N_0`.
  - Correct as a heuristic, and correctly not landed as a claim.

**Section 51 addendum: the involution-calculus calibration (3ce1996bc) PASS.**
- **The finite example.** The regular Klein four-group in `Sym(4)` consists of `x = (12)(34)`, `y = (13)(24)` and `xy = (14)(23)`.
  - The three are conjugate in `Sym(4)`, since there is one class of double transpositions, and `x`, `y` commute.
  - `P - 1` has rank 2 over `F_2`: its columns are `e_2 - e_1`, `e_1 - e_2`, `e_4 - e_3`, `e_3 - e_4`.
  - The action is regular, so `(x - 1)(y - 1)` acts as a nonzero element of `F_2[V_4]` with four distinct group terms.
- **Conclusion.** Conjugacy, commutation, `N^2 = 0` and equal displacement do not force `rk(N_0 N_1) = 0`. The dead end is
  recorded correctly on `thompson-v-has-no-nontrivial-f2-rank-model`.

## 52. The two-root defect piece carries a nontrivial rank model (lane w3-gate-bridge-b): PASS, second independent derivation

Items checked: `leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model`, route `leavitt-two-root-defect-piece-rank-model-proof`,
and `two-root-defect-piece-and-fd-representations-2026-09-12.md` Section 1. The assigned verifier is `w3-vf-linear`; this is a
second derivation from the rank-gate family verifier.

- **`Gamma = iota_0(R^x)` is the nine-leaf `EL_alpha(R)`.**
  - `alpha = (000, 001, 01)` partitions `[0]`.
  - `EL_alpha(R) = GL_alpha(R)`, by GL = EL over the corner `e_0 R e_0 ~= M_3(R)`.
  - That group is the whole unit group of the corner, embedded as `h + (1 - e_0)`, which is exactly `iota_0(R^x)`.
  - So the globality node `leavitt-rank-models-kazhdan-fixed-ideals-are-global` applies, in degree `(1,0)`. `Gamma` is
    finitely generated, so audit Lemma 1 gives `Fix_r(sigma(Gamma)) = eM`.
- **Commutation.** `n = x' - 1 = e_1000 n e_1000`, and `e_1000 e_0 = 0`. So `n(S[0]hT[0] + 1 - e_0) = n` and
  `(S[0]hT[0] + 1 - e_0)n = n`, and `x'`, `y'` commute with `Gamma`. Then `P` commutes with `sigma(Gamma)`, and `PM = qM` is
  invariant.
- **Lemma 1.1.**
  - `sigma(s) q` lies in `qM`, so `sigma(s) q = q sigma(s) q`.
  - Hence `q sigma(s) q sigma(t) q = q sigma(st) q`, and `tau_q(s^-1) tau_q(s) = q`.
- **Theorem 1.2(2), the fixed case.**
  - Triviality of `tau_Q` gives `sigma(gamma) q = q`, so `qM <= Fix_r(sigma(Gamma)) = fM`, with `sigma(g) f = f` for all
    `g`. So `P = fP`.
  - `(1-f) sigma(g) f = 0` makes `sigma_W` multiplicative.
  - `N'_23 (1-f) = N'_23` gives corner product `(1-f) f P (1-f) = 0`. Corner locality (Section 47), applied to `sigma_W` on
    the rank ultraproduct `(1-f)M(1-f)`, makes `sigma_W` trivial.
  - Then `sigma(g) = 1 + f sigma(g)(1-f)`. The products `ab` vanish in `fM(1-f)`, so the image is abelian, and perfection
    of `R^x` finishes.
- **Injectivity.** A nontrivial `tau_Q o iota_0` is injective by simplicity. It has normalized rank `rk(P) > 0`, since `P != 0`
  by corner locality.
- **Theorem 1.2(3).**
  - `iota_0 o iota_P' = iota_(0P')`, because `S[0]S[P'] = S[0P']` and `T[P']T[0] = T[0P']`.
  - `(sigma(gamma) - 1) q = q (sigma(gamma) - 1) q` turns the model's corner product into `q N^(0P')_23 N^(0P')_12 q`, which
    corner locality makes nonzero.
- **Corollary 1.3.** `q sigma(u) P sigma(u)^-1 q != 0` and `P = qP`, so `q sigma(u) q != 0`.
- **Remark 1.4.** The nested defect pieces lie inside `Q` because of the left factor `q`. The descent has no uniform bound,
  and the artifact says so accurately.

## 53. Characteristic-three rank models of the ternary Leavitt units: moving z iff nontrivial (lane w3-gate-char3): PASS, second derivation

Items checked: `ternary-leavitt-rank-models-move-z-iff-nontrivial`, route `ternary-leavitt-rank-models-move-z-proof`, the OPEN gate
`ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`, and `ternary-leavitt-char-three-rank-model-gate-2026-09-12.md`
Sections 1 to 3. The assigned verifier is `w3-vf-linear`; this is a second derivation.

- **Lemma 1.1.** As in Sections 11 and 46: `PG` is simple, `G` is perfect, and `z` is central.
- **Lemma 1.2(a).** `A (x) A - A' (x) A' = (A - A') (x) A + A' (x) (A - A')` and `rank(X (x) Y) <= n rank X`, so the squaring map is
  well defined, multiplicative and unit-preserving on rank ultraproducts.
- **Lemma 1.2(b).**
  - Under `v (x) w -> v w^T`, `ker(A (x) A - I) = {X : AX = XB}` with `B = A^-T`. That is the intertwiner space, of dimension
    `sum_nu sum_(i,j) min(a_i(nu), b_j(nu)) <= sum_nu g(nu) m(nu^-1)`, because `B` has the Jordan types of `A^-1`.
  - The sum is at most `n max g`, so `g(nu*) >= (1 - delta) n`, and `rk(A - nu*) <= delta n`.
  - If `nu* != nu*^-1`, then `m(nu*^-1) <= delta n` and `sum_(nu != nu*) g <= delta n`, so the sum is at most `2 delta n^2`.
    That is less than `(1 - delta) n^2` exactly when `delta < 1/3`, a contradiction.
  - So `nu* = +-1`, which lies in `k` (characteristic not two).
- **Lemma 1.2(c).** Representatives of a unit have corank `o(n_i)`, so they can be made invertible within rank `o(n_i)`, and the
  squared defect stays rank-null. Then (b) gives the signs, which are omega-almost constant.
- **Theorem 2.1.**
  - *(2) implies (3).* `ker sigma <= <z>`, and `iota^-1(<z>) = 1` by the established embedding claim.
  - *(1) implies (6).* `f = 2(1 - sigma(z))` is a nonzero central idempotent, and `z` maps to `-f` in the renormalized corner.
  - *(6) implies (4).* `T = sigma (x) sigma` has `T(z) = 1`. If `T` were trivial, (c) would make `sigma` a homomorphism into
    `{+-1}`, which perfection kills, contradicting `sigma(z) = -1`.
  - *(4) implies (5).* Simplicity of `PG`.
  - *(5) implies (3).* `pi o iota` is injective, since `iota(G)` meets `<z>` trivially.
- **Corollary 3.1.** `G` contains `w` and `d`, so `anti-central-rank-models-kill-ternary-corner-witnesses` with `Gamma = G` applies
  (Section 46).
- **The gate node's `refuted_by`.** The corner claim refutes existence, by the contrapositive of Corollary 3.1. The instance claim
  at `K = F_3`, `n = 2` refutes it through `G = GL_3(R) = EL_3(R)`. Both are correct.
- **Remark 3.4.** `ker sigma >= iota_P(G)`, which is not inside `<z>`, forces `ker sigma = G`. The extraction needs both identities
  in odd characteristic. Correct.

## 54. Haar law on the signed diagonal and the characteristic-three root normal form (6601af31f, lane w3-gate-char3): PASS, second derivation

Items checked: `anti-central-rank-models-see-haar-measure-on-signed-diagonal`, `ternary-rank-model-root-element-torus-normal-form`,
routes `anti-central-haar-diagonal-proof` and `ternary-root-element-torus-normal-form-proof`, and artifact Sections 4 and 5. The
assigned verifier is `w3-vf-linear`; this is a second derivation.

- **Theorem 4.1, half split.**
  - `tau_X tau_C = tau_(X Δ C) = tau_(X∖C)`, and `sigma(z) = -1` gives `phi(eps_-) = 4 = 1`.
  - `phi(Q_C) = 2(1 - sigma(tau_C))` and `phi(Q_(X∖C)) = 2(1 + sigma(tau_C))` are orthogonal idempotents summing to 1.
  - `V`, which lies in `H` and so in `Gamma`, carries `C` onto `X∖C`, and `[g] Q_C [g]^-1 = Q_(gC)` (Section 20).
  - Equal ranks summing to 1 give `1/2` each.
- **Theorem 4.1, atoms.**
  - `mu(c_S) = sum_(i in S) eps_i` makes `Q_(c_S)` the sum of `1_(A_eps)` over `chi_S(eps) = -1`.
  - Additivity gives `hat a(S) = 1 - 2 rho(phi(Q_(c_S)))`.
  - The three cases: `hat a(empty) = 1`, since `Q_empty = 0`. `hat a([n]) = -1`, since `Q_X = 4 eps_- = eps_-`. Every other
    `S` gives 0 by the half split.
  - Inversion gives `a_eps = 2^-n(1 - (-1)^|eps|)`, which is `2^(1-n)` for odd `eps`, equal to `lambda(A_eps)`.
  - Clopens of `M_-` are finite unions of atoms at a single code. PASS.
- **Proposition 5.1.**
  - *The torus.* `tau_0 = diag(-1,1,1)` under the code `(0,10,11)`. The elements `tau_11 = diag(1,1,-1)` and
    `tau_0 tau_10 = diag(-1,-1,1)` commute with `1 + E_12`. So `P_eta N P_eps = 0` unless `eta` is `eps` or `eps'`, and
    `N = D + A`.
  - *The reflection.* `tau_0 x_12(1) tau_0 = x_12(-1)`, and `x_12(1)^3 = x_12(3) = 1` gives `N^3 = 0` in characteristic
    three, with `(1+N)^-1 - 1 = -N + N^2`. Conjugation by `sigma(tau_0)` multiplies `P_eta N P_eps` by `eta_1 eps_1`,
    which is `+1` on `D` and `-1` on `A`. So `D - A = -D - A + N^2`, and `D = 2N^2 = -N^2`.
  - *Squares.* `N^2` is weight-preserving, so its flipping part `DA + AD` vanishes. `D^2 = N^4 = 0`, so `N^2 = A^2`,
    `N = A - A^2`, and `0 = DA + AD = -2A^3 = A^3`.
  - *(b).* `N^2 = 0` iff `A^2 = 0` iff `D = 0`.
  - *(c).* By Theorem 4.1 at the code `(0,10,11)`, the odd sign patterns `(-,+,+)`, `(+,-,+)`, `(+,+,-)` and `(-,-,-)` each
    have rank `1/4`, and `eps -> eps'` pairs them as stated.
  - Parts (a) and (b) hold for every rank model, not only anti-central ones.
- **Remark 5.2.** On a free `F_3[Z/3]`-module, `(x - 1)^2 != 0`, because `F_3[x]/(x^3 - 1) = F_3[x]/((x-1)^3)`. So projective
  content of level groups violates `A^2 = 0`. The claim about the twisted regular representation's Haar law is prose and was not
  re-derived.

**Section 54 addendum (fbcba57d8, bookkeeping and Attempts entries).** The citations of Section 54 on both claims are accurate. The
Attempts entries on `projective-ternary-group-is-f3-linear-sofic` and `rank-models-of-el3-satisfy-the-two-root-identities` also check.
- A nontrivial model of `PG` gives an injective, z-moving model of `G` (Section 53). An anti-central model squares to a model of
  `PG`. `F_3`-linear soficity of `PG` implies the existence gate.
- I completed the prose step that Section 54 had left underived: the twisted regular representation of a level group has the Haar
  law and violates `A^2 = 0`.
  - *Setting.* `H_k = GL_(2^k)(F_3)` contains `z = -I` and the depth-`k` torus `T_k` of sign matrices, one reflection per leaf.
  - *Decomposition.* `z` is central, so Mackey gives `Res_(T_k) Ind_(<z>)^(H_k)(sign) = ⊕_(T_k \ H_k) Ind_(<z>)^(T_k)(sign)`.
    Over `F_3`, `Ind_(<z>)^(T_k)(sign)` is the sum of the characters `chi` of the elementary abelian 2-group `T_k` with
    `chi(z) = -1`, each once.
  - *Haar law.* These characters are the sign patterns with an odd number of minus signs, so every odd pattern has weight `2^(1-2^k)`.
    That is the Haar law at the depth-`k` code.
  - *Projectivity.* `sign` is projective over `F_3[<z>]`, since `|<z>| = 2`, and induction preserves projectivity. So the
    restriction to `x_12(F_3) ~= Z/3` is free, and `(x - 1)^2 != 0` there.
  - This is exact for the finite group, which is all the Attempts entry claims.

**Section 50 addendum: quantitative truncation bound (cd762e2b8, artifact Proposition 3.1b) PASS.**
- **Lemma 3.1a.**
  - Intersection bound: `v = ex = fy` gives `v = (e - e^2)x + efy`, so `dim(im e cap im f) <= rank(e - e^2) + rank(ef)`.
  - Sum bound: `ex = (e+f)ex - fex + (e - e^2)x`, and symmetrically for `f`.
  - Combining with `rank e + rank f = dim(im e + im f) + dim(im e cap im f)` gives the stated inequality.
- **Compression errors.** `(ST)_W - S_W T_W = P S (1-P) T|_W`. Its rank is at most `d_T(W)`, because `1 - P` kills `W` on
  `TW + W`.
- **Almost-idempotents.**
  - `sum e_C = P . 1|_W = 1_W` exactly.
  - `e_C^2 - e_C` and `e_C e_D` are compression errors of rank at most `beta dim W`.
- **Rounding the units.** `sigma(h_i)` is injective, so `ker S_i` embeds in `sigma(h_i)W cap ker P`. That maps injectively into
  `(sigma(h_i)W + W)/W`, giving corank at most `beta dim W` and hence invertible `A_i` within that rank.
- **Covariance defect.** Replacing `A_i` by `S_i` costs `2 beta`. Exact covariance cancels the main terms. The two compression
  errors cost `d_(rho(1_C)) + d_(h_i) <= 2 beta + beta`, using `d_(T+T') <= d_T + d_(T')`. So `eps <= 5 beta`.
- **Counting.**
  - With `e_[0] = e_[00] + e_[01]` exactly, Lemma 3.1a gives `m([0]) >= m([00]) + m([01]) - 6 beta`.
  - `|m(h_i C) - m(C)| <= eps` then gives `m([0]) <= 2eps + 6beta`, and likewise `m([1]) <= 2eps + 6beta`.
  - Subadditivity on `e_[0] + e_[1] = 1_W` gives `1 <= 4 eps + 12 beta <= 32 beta`.

## 55. Transvection displacement, forced truncated shifts, moving-level normal form (lane w3-gate-construct): PASS, second derivation

Items checked:
- `transvection-displacement-forces-exact-local-embedding`;
- `natural-compressor-extension-fails-at-toeplitz-commutator`;
- `rank-models-are-exact-representations-at-moving-finite-levels`;
- their routes, the OPEN `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`, and
  `el3-rank-model-compressor-extension-2026-09-12.md` Sections 1, 2 and 4.

The assigned verifier is `w3-vf-linear`; this is a second derivation.

**Lemma 1.** `Fix(g) <= Fix(g_p)`. `P` restricted to `<g_p>` is free over a local group algebra, so `dim Fix(g_p) = n/|g_p|`, and the
displacement of `g` is at least `n/2`.

**Lemma 2.** `AB - 1 = (A-1)B + (B-1)`, and `u z^-1 u^-1 - 1` has the rank of `z - 1`.

**Lemma 3.**
- *First commutator.* Since `m >= 4`, there is `phi != 0` vanishing on `v, zv, z^-1 v`. Put `u = 1 + v (x) phi`.
  - With `A = zv (x) phi o z^-1` and `B = v (x) phi`, all of `A^2`, `B^2`, `AB = phi(z^-1 v) zv (x) phi` and `BA = phi(zv) v (x) psi`
    vanish.
  - So `[z,u] = 1 + A + B = 1 + N` with `N^2 = 0`, and `N != 0` because `zv` and `v` are independent.
- *Second commutator, when `rk N = 2`.* Pick `w` with `alpha(w) = 1` and `chi != 0` vanishing on `a, b, w`.
  - `chi o N = 0` gives `chi o y^-1 = chi`, so `y u'' y^-1 = 1 + yw (x) chi`.
  - `chi(w) = 0` then gives `[y, u''] = 1 + Nw (x) chi`, a transvection.
- *Bound.* Two applications of Lemma 2 give displacement at least `1/4`. Transvections are conjugate.

**Theorem 4.**
- `pi(tau(g))pi(tau(h)) - pi(tau(gh)) = pi(tau(gh))(pi(z_k) - 1)`, so a relator error costs at least `d_k n_k/4` unless `z_k = 1`.
  Hence `tau_k` is multiplicative on `F`, omega-almost everywhere.
- `tau_k(1) = 1` follows from multiplicativity and invertibility.
- `sigma(g) != 1` forces `tau_k(g) != 1`. Multiplicativity on `F^-1 F` then gives injectivity, so `G` is LEF.

**Corollary 5.**
- *(a)* A fixed element sent to a transvection has displacement tending to `rk(sigma(g_0) - 1) > 0`, by injectivity.
- *(b)* A projective share `alpha` gives `d_k >= alpha/2`.
- *(c)* A finitely presented LEF group is residually finite, and `R^x` is infinite and simple, so it is not. This relies on the cited
  `leavitt-unit-group-finitely-presented`.
- *(d)* The same lemmas run inside `M` on `F_K = SL_fin(F_2)`.

**Proposition 7.** I redid it entrywise.
- *Relations.* `t0 e_ab = e_(a-1,b)`, `t0 e_0b = 0`, `e_ab s0 = e_(a,b-1)` and `e_a0 s0 = 0`. The commutation pairs in (Σ4) satisfy the
  Steinberg rule `j != k`, `i != l`.
- *Commutators as conjugation.* For commuting involutions, `[q,u] = w` iff `q u q^-1 = wu`, and `[u,q] = w` gives the same.
- *Rank-one factors.* Over `F_2`, `1 + v (x) phi` determines `v` and `phi`.
- *`X^`.* (Σ1) gives `X delta_a^(2) = delta_a^(2) + delta_(a-1)^(1)` for `a >= 1` and `X delta_0^(2) = delta_0^(2)`. The (Σ4)
  commutations fix `V^(1)` and `V^(3)`.
- *`Y^`.* (Σ2) gives `delta_b^(2)* o Y^-1 = delta_b^(2)* + delta_(b-1)^(3)*`. With the other functionals fixed, `Y^-1 = 1 + S_N E_23 = Y^`.
- *`Z^`.* (Σ5), using that `u_21` and `u_23` commute, gives `delta_b^(1)* o Z^-1 = delta_b^(1)* + delta_b^(3)*`, so `Z^ = 1 + E_13`.
- *Uniqueness.* Each image is determined on a basis or by all coordinate functionals.
- *The failing relation.* `BA = 0` reduces the commutator to `1 + T_N S_N E_13 = 1 + (1 - P_(N-1)) E_13`, and multiplying by `Z^^-1` in
  characteristic two gives `u_13(N-1, N-1)`.
- *Corollary 8.* The index swap is a conjugation in `GL_(3N)(F_2)`.

**Lemma 9 and Proposition 10.**
- `U = V_0 cap ∩_h s(h)^-1 V_0` is invariant: for `v in U`, `s(h)s(k)v = s(hk)v` lies in `V_0`.
- `s` is exact on `U`, and `s(1)` is an invertible idempotent there, hence the identity.
- `rho` agrees with `s` on `U`, so `rk(rho(h) - s(h)) <= codim U`.
- The diagonal choice of levels is sound.

**Corollary 11.**
- *(b)* Rounding the finitely many generators and extending along fixed words gives a level-factoring model with the same limit.
  Theorem 4 then gives a contradiction.
- *(c)* Algebraic check that `D` commutes with `H_M`. Here `gamma_M = x_12(sum_(j=1..M) e_(j-1,j))` and `c = t0 - sum_(j=1..M) e_(j-1,j)`.
  - `c e_ab = e_(a-1,b)[a >= 1] - e_(a-1,b)[1 <= a <= M] = 0` for `a < M`.
  - `e_ab c = e_(a,b+1) - e_(a,b+1)[b+1 <= M] = 0` for `b < M`.
  - So `x_12(c)` commutes with every root element of `H_M`, including `x_21` and `x_31`, which need both products to vanish.
  - If all three corrections were `o(1)`, level-`(M+1)` matrix algebra gives the error `rho_k(u_13(M,M))`, whose displacement tends
    to `c_0`.

**Open claim.**
- Normal subgroups of `E` inside the simple `L = GL_fin(F_2)` are `1` or `L`.
- Residual finiteness of the Laurent quotient puts the radical inside `L`.
- The payoff through `J <= R` and simplicity is correct as stated.

**Section 55 addendum (68553d2f4: Attempts entry and wording fix).** The "odd order" wording in Remark 7 is now fixed. I spot-checked the new
Attempts entry on the OPEN `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`. It is prose, not an established claim.
- **Criterion.** If `psi : a -> a^-1`, `c -> c` extends to an endomorphism of `E`, the truncations `E_N` are exact on bounded words at
  both ends. That makes `E` LEF, hence sofic. A sofic approximation linearizes to a head-retaining rank model, so the claim would be
  false. The logic is sound as a conditional criterion.
- **Partial check.**
  - A root-form lift needs `[x_12(S+f), x_23(T+h)] = x_13(1)`, that is `(S+f)(T+h) = 1`. On the Fock module this makes `S + f`
    surjective.
  - `S` is injective with one-dimensional cokernel, so it has index `-1`, and finite-rank `f` preserves the index.
  - A surjective operator has index `dim ker >= 0`, so this is impossible. Correct.
- The general finitary corrections are correctly recorded as undecided.
