# Inverse defects on the anti-central summand of the ternary Leavitt group algebra

Lane `gk-l3-kernel`, 2026-09-12. Supports the Cairn claims
`ternary-anti-central-kernel-has-klein-idempotents`,
`ternary-anti-central-pairs-visible-or-invisible`,
`ternary-anti-central-failures-transfer-into-kernel-corners`, the open claim
`ternary-anti-central-kernel-unitization-not-directly-finite`, and the routes
`ternary-invisible-pair-refutes-surjunctivity` and
`anti-central-corner-gives-invisible-kernel-pair`.

## 0. Setting

* `k = F_3`, `R = L_k(1,2)`, `G = R^x`, `S = k[G]`, and `pi : S -> R` the evaluation, a unital
  ring homomorphism.
* `z = -1` is central in `G` of order two, and `eps_+- = 2(1 +- [z])` are central orthogonal
  idempotents with `eps_+ + eps_- = 1`. `S_- = eps_- S`. Since `pi(z) = -1`, `pi(eps_+) = 0` and
  `pi(eps_-) = 1`, so `pi_- = pi|S_-` is unital.
* `K_- = ker pi_- = eps_- ker pi`, an ideal of `S_-`, and `K_-^+ = F_3 eps_- + K_-`.
* `tau : S -> F_3` is the coefficient of `[1]`. It is a trace, `tau(xy) = tau(yx)`, and
  `tau(eps_-) = 2`.
* Words: `S[alpha] = s_(alpha_1)...s_(alpha_k)`, `T[beta] = t_(beta_l)...t_(beta_1)`, and the
  cylinder idempotents `q_gamma = S[gamma] T[gamma]`. For every `m`,
  `sum_(|gamma| = m) q_gamma = 1`, and `T[gamma] S[gamma'] = delta_(gamma gamma')` for
  `|gamma| = |gamma'|`.

## 1. A Klein idempotent in the kernel

**Theorem 1.** Put

    h1 = q_00 + q_01 - q_10 - q_11 = s0 t0 - s1 t1,
    h2 = -q_00 - q_01 + q_10 - q_11.

Then `h1, h2` are commuting involutions in `G`, `H = <h1, h2>` has order four and does not
contain `z`, and

    E = [1] + [h1] + [h2] + [h1 h2]

is an idempotent of `S` with `pi(E) = 0`. So `q = eps_- E` is a nonzero idempotent of `K_-`, with
`tau(q) = 2`.

*Proof.*
* Each `h_i` is a `+-1` combination of the orthogonal idempotents `q_gamma`, `|gamma| = 2`, which
  sum to `1`. So `h_i^2 = 1`, and `h1 h2 = h2 h1 = -q_00 - q_01 - q_10 + q_11`.
* The four elements `1, h1, h2, h1h2` have distinct sign patterns on the nonzero `q_gamma`, and
  none has pattern `(-1,-1,-1,-1)`, which is `z`. So `|H| = 4` and `z` is not in `H`.
* `E [h] = E` for `h` in `H`, so `E^2 = 4E = E` in characteristic three.
* `pi(E) = (1 + h1)(1 + h2) = (2q_00 + 2q_01)(2 q_10) = 0` by orthogonality.
* `H x <z>` is a subgroup of order eight, and `q = 2(1 - [z]) E` has coefficient `2` on `[1]`.
  So `q != 0` and `tau(q) = 2`.

**Consequences.**
* `eps_- - q` is an idempotent in `eps_- + K_-` other than `eps_-`, hence not a unit. So `K_-` is
  not contained in the Jacobson radical of `S_-`, and a product of lifts landing in `eps_- + K_-`
  need not be invertible. Radical perturbation of lifts is dead over `F_3`.
* `q` is never `>= eps_-` in the Murray--von Neumann order, since `pi(q) = 0`.
* **Why Klein constants.** Over `F_2` the kernel idempotent was `[1] + [g] + [g^2]` for an
  order-three unit (`leavitt-corner-kernel-not-jacobson-radical`). Over `F_3` the order-three unit
  `g = 1 + s0 t1` gives `n = [1] + [g] + [g^2] = (1 - [g])^2` in `ker pi` with `n^2 = 0`, a
  nilpotent. That obstruction does not transport, and the Klein constants of level two replace it.

## 2. Visibility

**Theorem 2.** Let `a, c` in `S_-` with `c a = eps_-`, and suppose `a c` lies in `p S_- p` for an
idempotent `p` with `pi(p) != 1`. Then `pi(a) pi(c) != 1`.

*Proof.* If `pi(a) pi(c) = 1`, then `1 = pi(p) y pi(p)` for some `y`. Multiplying on the left by
`pi(p)` gives `pi(p) = 1`. QED

**Corollary 2a.** Every solution of the corner equation `c e_- b = eps_-` gives the pair
`(e_- b, c e_-)`, whose range lies under `e_-`, and `pi(e_-) = 2(1 + w) != 1`. Every swap-separated
pair `c a = eps_-`, `c[w]a = 0` of `ternary-twisted-algebra-has-swap-separated-one-sided-pair` has
range idempotent `p = ac` with `p[w]p = 0`, so `pi(p) != 1`. Both are visible. The kernel cannot
supply a corner solution by itself: every solution evaluates to an honest one-sided pair of `R`.

## 3. The anti-central dichotomy

**3.1 The orbit theorem holds over every field.** The proofs of Lemma 1, Lemma 2 and Theorem 3 of
`research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md` use only the Leavitt
relations, with one change in Lemma 1.
* There `y = sum_(alpha in A) c_alpha S[alpha]` has nonzero coefficients.
* Then `T[w] T[alpha*] x S[gamma] S[w] = c_(alpha*)`, a nonzero scalar, and one divides by it.
* (M3) runs over `k^(X)` with the same non-periodic sequence.

So for `R = L_(F_3)(1,2)`, every pair `beta alpha = 1 != alpha beta` is `(w^(-1) s0, t0 w)` for a
unit `w`.

**3.2 Theorem 3.** Let `a, c` in `S_-` with `c a = eps_- != a c`, and put `delta = eps_- - ac`.
* **(V3)** If `pi(delta) != 0`, let `w` be the unit of 3.1 for `(pi(a), pi(c))`. Then
  `a' = [w] a` and `c' = c [w^(-1)]` satisfy `c' a' = eps_- != a' c'`, `pi(a') = s0` and
  `pi(c') = t0`.
* **(I3)** If `pi(delta) = 0`, then `r = pi(a)` lies in `G`. Then `a' = [r^(-1)] a` and
  `c' = c [r]` satisfy `c' a' = eps_- != a' c'`, `pi(a') = pi(c') = 1`, and `eps_- - a'c'` lies in
  `K_-`.

*Proof.* Translation by the units `[w]` and `[r]` of `S`, which commute with `eps_-`, preserves
`c a = eps_-`, and it conjugates `ac`, so `a'c' != eps_-`. The evaluations follow as in Theorem 4
of the binary artifact.

**3.3 Corollary.** `S_-` fails direct finiteness if and only if
* **(V3*)** some lift of `s0` in `S_-` is left invertible in `S_-`; or
* **(I3*)** `K_-^+` is not directly finite.

In (V3*) the partner can be taken over `t0`. If `pi(a) = s0`, `c a = eps_-` and
`gamma = pi(c) s1`, put `v = 1 + s0 gamma t1`, a unit with inverse `1 - s0 gamma t1` because
`t1 s0 = 0`. Then `v s0 = s0` and `pi(c) v^(-1) = t0`, so `[v] a`, `c [v^(-1)]` lie over
`(s0, t0)`.

**3.4 Trace replaces augmentation.** In `k[G]` a defect is never equivalent to `1`, because the
augmentation kills Leavitt families. `S_-` has no augmentation, since `eps(eps_-) = 0`. But `tau`
works:
* `tau(ac) = tau(ca) = 2`, so `tau(delta) = 0 != 2 = tau(eps_-)`;
* so a defect is never equivalent to `eps_-`, and a defect is never a single Klein idempotent.

**3.5 Unit criterion.** (V3*) holds iff there are `alpha0`, `beta0` in `S_-` with
`pi(alpha0) = s0`, `pi(beta0) = t0` and `u = beta0 alpha0` a unit of `S_-`.
* Then `beta' = u^(-1) beta0` is a left inverse over `t0`.
* Always `u` lies in `eps_- + K_-`, and Theorem 1 shows that set contains non-units. The kernel
  must turn the product of lifts into a unit, and a nilpotent `u - eps_-` suffices.
* The swap cross term of the corner equation is condition (X) of
  `ternary-twisted-algebra-has-swap-separated-one-sided-pair`.

## 4. Every failure transfers into a kernel corner

**Theorem 4.** Define

    delta4(g) = sum_(|gamma| = 2) S[gamma] g T[gamma]    (g in G),
    mu(x) = delta4_*(x) E                                 (x in S),

where `delta4_*` is the linear extension of `g -> [delta4(g)]` and `E` is the idempotent of
Theorem 1. Then `mu` restricts to an injective ring homomorphism `S_- -> q S_- q`, with
`mu(eps_-) = q`, image inside `K_-`, and `pi mu = 0`. Consequently, if `c a = eps_- != a c` in
`S_-`, then

    A = (eps_- - q) + mu(a),     C = (eps_- - q) + mu(c)

satisfy `C A = eps_- != A C`, with `A - eps_-` and `C - eps_-` in `K_-`.

*Proof.*
* **Homomorphism, injective on G.** `delta4` is a homomorphism `G -> G`, by
  `T[gamma] S[gamma'] = delta_(gamma gamma')` and `sum q_gamma = 1`. It is injective, since
  `T[00] delta4(g) S[00] = g`.
* **Commutation.** Every `h` in `H` is `sum lambda_h(gamma) q_gamma`, so
  `h delta4(g) = sum lambda_h(gamma) S[gamma] g T[gamma] = delta4(g) h`. Hence `E` commutes with
  `delta4_*(S)`.
* **mu is multiplicative.** `mu(x) mu(y) = delta4_*(x) delta4_*(y) E^2 = mu(xy)`.
* **Scalars.** `delta4(-1) = -1`, so `mu(eps_-) = eps_- E = q`, and `mu(S_-)` lies in `q S q`.
* **Injectivity.** If `delta4(g) h = delta4(g') h'`, then `delta4(g^(-1) g')` lies in `H`. Put
  `delta4(x) = h''`. Applying `T[gamma] ( . ) S[gamma]` gives `x = lambda_(h'')(gamma)` for every
  `gamma`. So `h''` is scalar, `h''` is `1` or `-1`, and `-1` is not in `H`. Hence `g = g'` and
  `h = h'`. The products `delta4(g) h` are therefore distinct group elements, and `mu` is
  injective.
* **Evaluation.** `pi mu(x) = pi(delta4_*(x)) pi(E) = 0`, so `q S q` lies in `K_-`, an ideal
  containing `q`.
* **The pair.** `mu(a)` and `mu(c)` lie in `q S_- q`, so `(eps_- - q) mu(a) = 0` and
  `mu(c)(eps_- - q) = 0`. Then `C A = (eps_- - q) + mu(ca) = eps_-`, and
  `A C = (eps_- - q) + mu(ac) != eps_-` by injectivity. QED

**Corollary 4a.** The following are equivalent:
* `S_-` is not directly finite;
* `K_-^+` is not directly finite (I3*);
* `S_-` has a pair over `eps_-` with defect in `K_-`.

In particular (V3*) implies (I3*), and a solution of `ternary-anti-invariant-swap-corner-is-full`
implies (I3*). Searches may fix the invisible normal form without loss. This is the ternary analogue
of the binary universality of the invisible half found by lane `gk-l2-invisible`. The subgroup of
constants used here avoids `-1`, as it must, because `-1` is also a scalar of `delta4(G)`.

## 5. The invisible problem

(I3*) is open. The necessary conditions for a pair `(eps_- + v)(eps_- + u) = eps_-` strict are
these.
* **Defect.** `d = eps_- - (eps_- + u)(eps_- + v)` is an idempotent of `K_-` with `tau(d) = 0`. So
  `d` is not one Klein idempotent, whose trace is two.
* **No nilpotent parts.** `eps_- + n` with `n` nilpotent is a unit.
* **No finite-dimensional detection.** `G` is finitely generated, simple and infinite, and finitely
  generated linear groups are residually finite. So every finite-dimensional representation of `S`
  factors through the augmentation, where `[z]` acts as `1` and `eps_-` as `0`. `S_-` has no nonzero
  finite-dimensional representation at all.
* **Not a finite-subgroup projective.** The defect `d` satisfies `F_3[G] ~= F_3[G] (+) d F_3[G]`.
  * The additive 3-adic lifted trace of `lifted-trace-detects-finite-subgroup-projectives`, which
    is stated for every prime, gives `t_3(d) = 0`.
  * Every nonzero finite sum of finite-subgroup projectives has `t_3 = dim/|H| != 0`.
  * So `q`, `q - mu(q)`, and sums of orthogonal kernel character idempotents of the finite
    sign-constant groups at deeper levels are all excluded as defects. The mod-3 trace allows
    sums of three of them; the lifted trace does not.
  * A surviving defect must mix finite subgroups, for example `e - f` with `f < e` induced from
    different finite subgroups with equal lifted trace.

**Attempts.**
* **Kernel corners.** Via Theorem 4 they are universal, so they are exactly as hard as the whole
  problem; no easier sub-case is gained. No strict pair in any corner is known.
* **Radical perturbation.** Dead, by Theorem 1.
* **Traces mod 3.** They do not separate: `tau(q) = tau(eps_-) = 2`. Only the evaluation forbids
  `q >= eps_-`. The lifted trace separates finite-subgroup projectives from defects.
* **Proper corner self-embedding.** Dead as a shortcut. `mu` is a unital embedding of `S_-` into
  the proper corner `q S_- q`, but directly finite rings can have proper corner self-embeddings,
  and the telescoping tail `mu^m(error)` is nonzero at every finite depth. This is the same failure
  as over `F_2`, recorded on `leavitt-recursive-kernel-idempotents`.

## 6. What the kernel must contribute

* **To a corner solution:** nothing by itself (Theorem 2). A solution evaluates to an honest pair of
  `R` and, after one translation, lies over `(s0, t0)` (Theorem 3).
* **To a visible lift:** a unit in `eps_- + K_-` (3.5). By Theorem 1 this is a genuine condition.
* **To any failure at all:** everything. By Theorem 4 every failure is a kernel-corner failure, so
  any obstruction to the lift must already act inside `K_-^+`.

Nothing here decides existence either way.

## 7. Every finite-field host: roots of unity lower the level and add no room

This answers a relayed question: do the extra roots of unity in the hosts of
`leavitt-unit-group-algebras-split-over-scalar-characters`, such as `(q,d) = (4,2)` or the colimit
over finite fields, give the kernel normal forms more room?

*Reconciliation.* Lane `gk-l2-invisible` landed the general criterion in the same minute, as
`leavitt-invisible-half-universal-over-every-finite-field`: every field, every type `(1,d)`, cuts by
matrix constants, and existence at level one for every `(q,d) != (3,2)`, including `q = 2`, through
torus elements. That node is the Cairn claim. Theorem 7.1 below is its diagonal-constant instance,
kept here for its proof and its level count. Proposition 7.3 (base change) and the answer are what
this section adds. The Cairn claim `leavitt-identity-factor-failures-transfer-into-kernel-corners`
(verified by `gk-vf-linear`) is kept for Proposition 7.3 and the diagonal level count, and is keyed
`distinct_from` that node.

**Setting.**
* `q = p^r >= 3`, `d >= 2`, `L = L_(F_q)(1,d)`, `G = L^x`, `A = F_q[G]` and `pi : A -> L` the
  evaluation.
* `Z = F_q^x . 1`, with the central character idempotents `eps_chi`. `A_iota` is the
  Leavitt-visible factor, and `K_iota = ker(pi|A_iota)`.
* Level-`k` cylinders run over words `gamma` in `{0,...,d-1}^k`, with `q_gamma = S[gamma] T[gamma]`,
  `T[gamma] S[gamma'] = delta_(gamma gamma')` and `sum q_gamma = 1`.
* The diagonal constants are `D_k = { sum lambda(gamma) q_gamma : lambda : {0..d-1}^k -> F_q^x }`,
  a subgroup of `G` isomorphic to `(F_q^x)^(d^k)`. The coordinate characters are
  `ev_gamma(h) = lambda_h(gamma)`.
* `delta_k(g) = sum_(|gamma| = k) S[gamma] g T[gamma]`.

**Lemma 7.0.**
* `delta_k` is an injective homomorphism `G -> G`, since `T[gamma] delta_k(g) S[gamma] = g`.
* It fixes `Z` and commutes with `D_k`.
* `delta_k(G)` meets `D_k` in `Z`: if `delta_k(g) = h`, then `g = T[gamma] h S[gamma] = lambda_h(gamma)`
  for every `gamma`.

**Theorem 7.1.** Let `H <= D_k` with `H n Z = 1`, and let `psi` be a character of `H` different
from every `ev_gamma|H`. Put

    E = (1/|H|) sum_h psi(h)^(-1) [h],        mu(x) = delta_k*(x) E,        q_iota = eps_iota E.

Then:
* `mu : A -> A` is an injective ring homomorphism with `pi mu = 0`;
* `mu(eps_chi) = eps_chi E != 0`, and `mu(A_chi)` lies in the corner of `eps_chi E` for every `chi`;
* if `c a = eps_iota != a c` in `A_iota`, then `A' = (eps_iota - q_iota) + mu(a)` and
  `C' = (eps_iota - q_iota) + mu(c)` satisfy `C' A' = eps_iota != A' C'`, with `A' - eps_iota` and
  `C' - eps_iota` in `K_iota`.

So `A_iota` is not directly finite iff `F_q eps_iota + K_iota` is not directly finite.

*Proof.*
* **E is a killed idempotent.** `|H|` divides `(q-1)^(d^k)`, so it is prime to `p`, and the
  characters of `H` take values in `F_q`. `[h] E = psi(h) E` gives `E^2 = E`. By orthogonality of
  characters,
  `pi(E) = sum_gamma ((1/|H|) sum_h psi(h)^(-1) ev_gamma(h)) q_gamma = sum_(gamma : ev_gamma|H = psi) q_gamma = 0`.
* **mu is multiplicative.** `E` commutes with `delta_k*(A)`, and `E^2 = E`.
* **mu is injective.** `delta_k(g) h = delta_k(g') h'` forces `delta_k(g'^(-1) g) = h' h^(-1)`, which
  lies in `delta_k(G) n D_k n H = Z n H = 1`. So the products are distinct group elements, and the
  coefficient of `mu(x)` at `delta_k(g)` is `x_g/|H|`.
* **Scalars and corners.** `delta_k` fixes scalars, so `mu(eps_chi) = eps_chi E`. Since `eps_chi`
  is central, `mu(x) = mu(eps_chi) mu(x) mu(eps_chi)` for `x` in `A_chi`.
* **Evaluation.** `pi mu(x) = pi(delta_k*(x)) pi(E) = 0`.
* **The pair.** `mu(a)` and `mu(c)` lie in `q_iota A q_iota` with `q_iota <= eps_iota`, so the cross
  terms vanish. `C'A' = eps_iota - q_iota + mu(ca) = eps_iota`. `A'C' != eps_iota` because
  `mu(ac) != mu(eps_iota)`. Finally `pi(A') = pi(C') = 1`. QED

**Theorem 7.2 (level criterion, diagonal constants only).**
* A triple `(k, H, psi)` with `H` diagonal, as in 7.1, exists iff `q >= 3`. Matrix constants do
  more: `leavitt-invisible-half-universal-over-every-finite-field` gives level-one cuts for every
  `(q,d) != (3,2)`, including `q = 2`.
* The least level is `k = 1` iff `q >= 4`, or `q = 3` and `d >= 3`.
* For `(q, d) = (3, 2)` the least level is `2`, and Theorem 4 is that instance.

*Proof.*
* **q = 2.** `D_k` is trivial.
* **Level 1.** Take `H = {lambda : lambda(0) = 1}`, isomorphic to `(F_q^x)^(d-1)`. It meets `Z`
  trivially and has `(q-1)^(d-1)` characters, against at most `d` coordinate characters. So a
  missing character exists when `(q-1)^(d-1) > d`, which holds for `q >= 4` and for `q = 3`, `d >= 3`.
  For `(3,2)`, the subgroups of `D_1 = {+-1}^2` meeting `Z = {+-1}` trivially are `1`, `<(1,-1)>` and
  `<(-1,1)>`. On each, the two coordinate characters exhaust the characters.
* **Level 2 for q >= 3.** `H = {lambda : lambda(0^k) = 1}` at `k = 2` has
  `(q-1)^(d^2 - 1) >= 2^(d^2 - 1) > d^2` characters. QED

**Proposition 7.3 (base change).** Let `F_q <= F_q'`, `G_q <= G_q'`, and let `eps'` be the identity
character idempotent of `F_q'[G_q']`. Then `x -> eps' x` sends a pair `c a = eps_iota != a c` of
`F_q[G_q]` to a pair over `eps'`, and it sends kernel elements to kernel elements.
* `eps' eps_iota = eps'`, and `eps' = ((q-1)/(q'-1)) sum_t t^(-1) [t] eps_iota`, where `t` runs
  over a transversal of `F_q'^x / F_q^x`.
* The cosets `t G_q` are disjoint because `G_q n F_q'^x = F_q^x`. So `eps' delta != 0` for the
  defect `delta`.
* `pi'(eps' x) = pi(x)`, because `L_(F_q) -> L_(F_q')` is injective.

This extends gk-lp-hosts' extension-field statement for corner solutions to arbitrary pairs and
to kernel pairs.

**Answer.**
* **No extra room.** On every finite-field host the invisible form is universal
  (`leavitt-invisible-half-universal-over-every-finite-field`), and for `A_iota` by Theorem 7.1.
  The kernel problem on a host is exactly that host's direct-finiteness question for `A_iota`,
  neither easier nor harder.
* **What extra roots of unity do.** They lower the diagonal amplification level from `2` to `1`
  (Theorem 7.2). That is cosmetic.
* **The colimit.** Its only extra room is host monotonicity (Proposition 7.3), which the
  extension-field statement already records.
* **F_2.** There are no diagonal constants. The binary transfer uses matrix constants instead
  (lane `gk-l2-invisible`).
* **Scope.** The dichotomy of Section 3 is not claimed for `d >= 3`. There `V(L) = {0} u Z/(d-1)`,
  so defect classes need not be free, which is why the cyclic twist requires `m = 1 mod (d-1)`.
  Theorem 7.1 uses no orbit theorem and holds for every `d`.

**Remark 7.4 (other factors: an untested idea).** Extra roots of unity do add Leavitt-invisible
factors `A_chi`.
* **Isomorphisms.** Coefficientwise Frobenius and the inverse-adjoint `g -> (g*)^(-1)` (with
  `s_i* = t_i`) are automorphisms of `G`. They give `A_(iota^j) ~= A_(iota^(j'))` whenever
  `j'` lies in `+-p^Z j` modulo `q - 1`.
* **A tensor evaluation.** The factor `A_(iota^2)` carries the unital evaluation
  `g -> g (x) g : A -> L (x) L`, since `[lambda] -> lambda^2`.
* **Its kernel corners.** Theorem 7.1 transfers into the kernel of that evaluation whenever `psi`
  is not a product `ev_gamma ev_gamma'`.
* **Not examined.** Whether a corner equation has an image solution in `L (x) L`.

## 8. Mixed-subgroup defect candidates

The lead's unit: build idempotents `f < e` in `K_-` from different finite subgroups of `G`, with
equal lifted traces, and test whether `e - f` can be the defect of a pair over `eps_-`; or exclude
such defects.

**8.0 The exact test.** For idempotents `f < e` of `S_-`, put `d = e - f`.
* **Criterion.** `d` is the defect of a pair over `eps_-` iff `eps_- - d ~ eps_-`.
* **Sufficient.** `e ~ f`. Then `eps_- - d = (eps_- - e) + f ~ (eps_- - e) + e = eps_-`, as sums
  of orthogonal idempotents.
* **Necessary.** `[d] = 0` in `K_0(F_3[G])`. So `t_3(d) = 0`, and the Hattori–Stallings class sums
  `sum_(g in C) d(g)` vanish in `F_3` for every conjugacy class `C`. These are additive invariants.
  They are inert on the target itself (Theorem B(i) of lane `gk-l3-obstruct`'s
  `research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md`), but they do filter a
  proposed defect.

**8.1 Theorem (no characteristic-zero lift).** Let `G` be any group, `p` a prime, and `d` a nonzero
idempotent of `M_n(F_p[G])`. Suppose `d` is the coefficientwise reduction of an idempotent
`D` of `M_n(Z_p[G])` with finite support. Then:
* `t_p([d]) = T(D)` is a nonzero element of `Z_p`, so `[d] != 0` in `K_0(F_p[G])`;
* for every `m >= 0`, `d (+) 0_m` is not the defect `1 - ac` of any pair `ca = 1` in
  `M_(n+m)(F_p[G])`.

In particular, no defect over `eps_-` in `S_-` (padded by `eps_+`), and no difference `e - f` for an
infinite idempotent `e ~ f < e`, has a finite-support idempotent lift over `Z_3`.

*Proof.*
* **The complete ring.** Work in `C = c_0(G, Z_p)`, with the continuous cyclic trace `T`, the sum
  of diagonal identity coefficients (`lifted-trace-finite-subgroup-proof`). Elements of `1 + pM(C)`
  are invertible. Two idempotent lifts `E, E'` of one idempotent are conjugate by
  `W = E'E + (1 - E')(1 - E)`, so `T(E) = T(E')`. By that route, `t_p([d])` is `T` of any idempotent
  lift of `d`, and here `D` is one.
* **Direct check for defects.** Suppose `ca = 1` and `1 - ac = d (+) 0_m`. Choose finite-support
  lifts `A0, C0`. `C0 A0 = 1` modulo `p`, so it is invertible. Put `X = (C0 A0)^(-1)` and
  `P = A0 X C0`, an idempotent lifting `ac`. Then `1 - P` lifts `d (+) 0_m`, and
  `T(1 - P) = (n + m) - T(X C0 A0) = 0`. `D (+) 0_m` is another lift, so `T(D) = 0`.
* **Kaplansky positivity.** The coefficients of `D` generate a finitely generated field inside
  `Q_p`, and it embeds in `C`. The image of `D` is an idempotent `x` of `M_n(C[G])`, with `T(x)` the
  image of `T(D)`.
  * In `M_n(C*_r(G))` the trace `T` is positive and faithful. `T(y*y) = sum ||y_ij delta_1||^2`, and
    `y_ij delta_1 = 0` forces `y_ij = 0`, because right translations commute with left convolution.
  * The projection `p = x x* (1 + (x - x*)(x* - x))^(-1)` satisfies `x p = p` and `p x = x`
    (Blackadar, *K-Theory for Operator Algebras*, Proposition 4.6.2).
  * So `T(x) = T(p x) = T(x p) = T(p) = T(p* p) >= 0`, with equality only if `p = 0`, and then
    `x = p x = 0`.
* **Conclusion.** `T(D) = 0` would force `D = 0`, hence `d = 0`. So `T(D) != 0`, and neither
  conclusion can fail. QED

*Trust surface.* Blackadar's similarity proposition and faithfulness of the canonical trace on
`C*_r(G)`; the latter is proved inline. This is the classical route to Kaplansky's theorem
(Kaplansky 1969; Montgomery 1969) that `0 < tau(e)` for nonzero idempotents of `C[G]`.

**8.2 Constants at every level form one locally finite group.**
* `Theta_(2^k) : GL_(2^k)(F_3) -> G` satisfies `Theta_(2^(k+1))(a (x) I_2) = Theta_(2^k)(a)`, because
  `S[gamma] T[gamma'] = S[gamma 0] T[gamma' 0] + S[gamma 1] T[gamma' 1]`.
* So finitely many constants from any levels lie in one finite subgroup `Theta(GL_(2^K)(F_3))`. That
  covers the Klein groups at different prefix levels, `D_8` and `Q_8` inside `GL_2(F_3)`, `z`, `w`,
  `d = s0 t0 - s1 t1`, and the idempotents `eps_-`, `e_-`, `q`.
* Every candidate built from constants alone is supported in a finite subgroup. There, for `f < e`,
  `[e] - [f]` has positive lifted trace (`lifted-trace-detects-finite-subgroup-projectives`), so it
  is excluded.
* A mixed candidate needs a finite subgroup outside the constants, such as `u H u^(-1)` for a
  non-constant unit `u`, for instance from Thompson's group `V`.

**8.3 Linear characters are ordered only by containment.** Let `H1, H2` be finite subgroups of `G`
of order prime to `p`, let `psi_i : H_i -> F_p^x` be linear characters, and put
`e = E_(psi1)`, `f = E_(psi2)` in `F_p[G]`. Then `f e = f` iff `H1 <= H2` and `psi2|H1 = psi1`. In
that case `e, f` lie in `F_p[H2]` and are excluded as in 8.2.

*Proof.*
* Lift by Teichmüller characters to `E`, `F` in `Z_p[G]`, and put `K = H1 n H2`.
* The representations of `g = ab` (`a` in `H2`, `b` in `H1`) as `h2 h1` are `(ak, k^(-1) b)` for `k`
  in `K`. So the coefficient of `F E` at `g` is `psi2(a)^(-1) psi1(b)^(-1) |K| / (|H1||H2|)` when
  `psi1|K = psi2|K`, and `F E = 0` otherwise.
* These coefficients are units of `Z_p`, so `f e` is `0` or has support exactly `H2 H1`.
* `f e = f != 0` forces `H2 H1 = H2`, hence `H1 <= H2` and `psi1 = psi2|H1`. The converse is direct.
  QED

**8.4 What survives.** A defect `e - f` built from finite subgroups must:
* use a finite subgroup outside the constants (8.2);
* not be a pair of linear-character idempotents (8.3);
* have no finite-support idempotent lift over `Z_3` (8.1). So `f < e` must hold modulo `3` for no
  pair of characteristic-zero lifts that satisfies it exactly. That needs cancellation modulo `3` in
  the coefficients of `F E - F`: sums of values of a non-linear irreducible character, or a subgroup
  of order divisible by `3`, where `F_3[H]` is not semisimple;
* satisfy `e ~ f`, or more generally `eps_- - d ~ eps_-` (8.0).

No such candidate was constructed. Mixed-subgroup defects are not excluded in general. By Theorem 4
every failure lives in a kernel corner, and a genuinely modular defect, one with no
characteristic-zero lift, is exactly what a failure would need. Equal lifted traces restrict nothing
further once 8.1 applies.
