# Adversarial audit of the state-upgrade counterexample chain

Lane `w5-red-upg`, 2026-09-12, audited at main tip ee2cd03f38.

**Chain audited.**
- The route `ternary-counterexample-from-rank-triviality-and-state-upgrade`, with target
  `ternary-anti-central-unit-class-is-nonpositive`.
- Then `nonpositive-unit-class-refutes-ternary-surjunctivity` into `ternary-leavitt-unit-group-nonsurjunctive`,
  which is listed in the goal's `refuted_by`.
- Also the sharper sibling route `ternary-counterexample-from-rank-kill-and-state-realization`.

**Notation.** G = L_(F_3)(1,2)^x, z = -1, eps_+- = 2(1 +- [z]), S_- = eps_- F_3[G], u = [eps_-] in K_0(S_-),
e_- = eps_- . 2(1 + [w]) with w = s0 t1 + s1 t0.

## 1. Verdict table

| # | Link | Nodes | Status on main | Verdict |
|---|---|---|---|---|
| 1 | G has no nontrivial characteristic-3 rank model | `leavitt-el3-rank-models-over-finite-fields-are-trivial` at K = F_3, n = 2 | OPEN, listed | **GAP (wiring only).** The route passes from models of EL_3(R) to models of G without citing `leavitt-gl-equals-el-and-perfect-unit-group`. Fixed in this landing. |
| 2 | a state on (K_0(S_-), u) gives a nontrivial characteristic-3 rank model | `ternary-anti-central-states-force-nontrivial-rank-models` | OPEN, listed | **PASS as logic.** The route uses the contrapositive in the right direction. The content is open. |
| 3 | no state, so k u <= 0, so u <= 0 | `anti-central-state-obstruction-equals-stable-finiteness` part 2; census Theorem A(b) and Remark | ESTABLISHED (gk-vf-linear §11) | **PASS**, re-derived |
| 4 | u <= 0 iff the swap corner is full | `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` (Theorem E) | ESTABLISHED | **PASS**, re-derived except one cited input (§2.4). The route does not need this link. |
| 5 | a one-sided pair | census Theorem A(c) (matrix pair from u <= 0); "Why it suffices" on `ternary-anti-invariant-swap-corner-is-full` (1x1 pair from the corner) | ESTABLISHED | **PASS**, both re-derived |
| 6 | pair, then strict linear automaton, then goal refuted | `stable-finiteness-failure-refutes-surjunctivity`; `nonpositive-unit-class-refutes-ternary-surjunctivity`; goal `refuted_by` | ESTABLISHED | **PASS** |

**Conclusion.**
- Given links 1 and 2, the chain refutes Gottschalk on G, with a strict linear automaton over the alphabet
  F_3^r.
- No link is FALSE. The one gap is a missing `requires` entry, and its content is established.
- Links 1 and 2 are open, so this is a conditional refutation and settles nothing yet.

## 2. Re-derivations

### 2.1 Link 1: wiring
- **What each side says.** `leavitt-el3-rank-models-over-finite-fields-are-trivial` quantifies over
  homomorphisms EL_3(R) -> M^x. The route's step 1 says "G_3 has no nontrivial characteristic-three rank
  model".
- **Missing step.** The three-leaf prefix code R ~= R^3 gives G ~= GL_3(R), and GL_3(R) = EL_3(R) over every
  field (`leavitt-gl-equals-el-and-perfect-unit-group`, Lean `glAll_eq_elementary`). So every model of G
  is a model of EL_3(R) on all of G.
- **Alternative.** Without GL = EL, triviality on EL_3(R) kills its normal closure in G. That closure is
  not central, so its image in PG = G/{+-1} is all of PG by simplicity, and perfection of G then gives
  all of G. This uses simplicity of PG and perfection of G, which are also not listed.
- **Trust surface.** The Lean-backed node was text-scanned for `sorry` and `axiom` by w4-r4-corner, and not
  rebuilt.
- **Field quantifier.** The triviality node fixes one field k of characteristic 3, while the upgrade
  allows matrix algebras over varying fields k_i of characteristic 3. This is harmless.
  - All the k_i embed in one algebraically closed field Omega of characteristic 3, and matrix rank does
    not change under field extension.
  - So prod_omega M_(n_i)(k_i)/d_omega embeds unitally and rank-preservingly in
    prod_omega M_(n_i)(Omega)/d_omega, and a nontrivial model stays nontrivial.

### 2.2 Link 2: logic only
- **Direction.** The upgrade says a state gives a nontrivial model. Route step 2 takes the contrapositive,
  no nontrivial model gives no state. That is the right direction.
- **"State" is the same object** in links 2 and 3: an additive map s: K_0(S_-) -> R, nonnegative on the
  cone of classes of finitely generated projectives, with s(u) = 1. Both node statements agree.

### 2.3 Link 3
- **Order unit.** Every finitely generated projective is a summand of some S_-^n, so u is an order unit
  (census §2).
- **State criterion** (census Theorem A(b)).
  - Put p(x) = inf{ m/n : n x <= m u }. It is finite because u is an order unit, and bounded below
    exactly when no k u <= 0.
  - p is subadditive and Q-homogeneous. For torsion t, p(t) and p(-t) are <= 0, so p is constant on
    torsion translates and passes to K_0 (x) Q.
  - p(u) = 1 and p(-u) = -1. Zorn's lemma extends q u -> q to an additive f <= p.
  - On the cone, -x <= 0 . u gives p(-x) <= 0, so f(x) >= 0.
- **The multiple.** If k u <= 0 then -u = (k-1)u + (-k u) lies in the cone, since u does.

### 2.4 Link 4: Theorem E at (q, d, m) = (3, 2, 2)
- **3 => 2.** The unital map M_2(S_-) -> S_- induces a monoid map F on V(S_-) with F(2u) = u.
  1. Pad to n = 2j, so (2j+1)u <= 2j u.
  2. Apply F: j u + F(u) <= j u.
  3. Iterating twice gives (j+1)u <= j u.
  4. Halving the size repeatedly reaches 2u <= u.
- **3 <=> 4.** [Q] = -u in K_0 iff Q (+) A (+) A^N ~= A^N for some N.
- **2 => 1.** This uses part 3 of `cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`, which I
  did not re-derive.
- **Hidden stability.** None. Items 1 through 5 are exactly equivalent, and the halving map absorbs
  stabilization.
- **Not needed by the route.** The route goes from u <= 0 straight to a matrix pair (link 5, first form).

### 2.5 Link 5
- **From u <= 0.**
  - There is Q with Q (+) S_-^k (+) S_-^r ~= S_-^r and k >= 1. Let phi: S_-^r -> S_-^r (+) X be this
    isomorphism, with X = S_-^k (+) Q nonzero.
  - With iota and p the inclusion and projection, A = phi^-1 iota and B = p phi give BA = 1 and
    AB = phi^-1 (iota p) phi != 1, since iota p kills X.
  - Pad with eps_+ 1_r to get a pair in M_r(F_3[G]).
- **From the corner c e_- b = eps_-.**
  - Put A = e_- b + eps_+ and C = c + eps_+. Then CA = 1.
  - If AC = 1, then e_- b c = eps_-, so eps_- lies in e_- S_- and e_- = e_- eps_- = eps_-.
  - But e_- != eps_-, since eps_- [w] != eps_- (w is not 1 or z). So AC != 1, and F_3[G] itself is not
    directly finite.
- **Hazard "full versus not directly finite".** The translation is correct in both uses. The matrix form
  suffices, and the corner form gives the 1x1 failure.

### 2.6 Link 6
- **Automata.** Take BA = 1 != AB over k[G] with k finite. The convolution automata satisfy
  tau_A o tau_B = tau_(BA) = id, under the node's convention, so tau_B is injective.
- **Not surjective.** If tau_B were surjective, it would be bijective with inverse tau_A. Then
  tau_(AB) = id, and AB = 1 because A -> tau_A is injective (evaluate at delta configurations).
- **Alphabet.** It is k^r. Gottschalk quantifies over every finite alphabet, and the goal lists
  `ternary-leavitt-unit-group-nonsurjunctive` in `refuted_by`.

### 2.7 Sibling route `ternary-counterexample-from-rank-kill-and-state-realization`
- **Step 1.** "Every Sylvester rank function on F_3[G] has rk(1 - [z]) = 0" is equivalent to "no N on S_-
  with N(eps_-) = 1". Pull back along the unital map x -> eps_- x, and extend by N(eps_- X). PASS.
- **Steps 2 and 3.** These are links 2 and 3 with (U1) in place of the full upgrade. PASS.

## 3. Scope
- **Links 1 and 2 are open.** This audit confirms the implications only, not that both hypotheses hold.
- **Exact reformulation.** Given link 2, link 1 is equivalent to the corner itself.
  - Link 1 gives no state (link 2), so the corner is full (Theorem E).
  - Conversely, a full corner forbids every nontrivial model (`ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`
    lists the corner in `refuted_by`, through `anti-central-rank-models-kill-ternary-corner-witnesses`).
  - So the chain loses nothing, and it gains nothing beyond a change of target.
