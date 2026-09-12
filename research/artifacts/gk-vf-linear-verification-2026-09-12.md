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
