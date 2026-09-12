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
