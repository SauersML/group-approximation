# Unconditional assembly: MF recognition on finite presentations is Pi-zero-two complete

This artifact is a full independent verification and self-contained
reassembly of the proof that, for the recursive coding of finite group
presentations,

```text
MF_fp    is Pi^0_2-complete,
NONMF_fp is Sigma^0_2-complete.                                  (A0)
```

Here `MF` is the operator-norm matricial (Carrion--Dadarlat--Eckhardt)
predicate: a countable group is operator-MF when it embeds into the unitary
group of the norm matrix corona `prod_n M_n / sum_n M_n`.  This is the
repository's `IsOperatorMF` and the predicate of
[[mf-recognition-has-a-pi2-upper-bound]].  Every step below was re-derived
in this audit; the proof is unconditional, with three classical or verified
literature inputs used as building blocks and named in Section 2.

## 1. What this audit adds to the chain already on main

The chain [[mf-recognition-finite-presentations-completeness-proof]] landed
at `a5ecf8399`/`cb548bb14` (2026-08-26).  This audit

1. re-derives every group-theoretic link (Section 4);
2. verifies the key literature input verbatim from the source PDF
   (Section 2), correcting a citation-numbering trap;
3. replaces the two remaining imported analytic steps (Ueda's corner
   realization of the universal C-star HNN extension, and the reduced von
   Neumann HNN normal form) by short self-contained arguments, packaged as
   the general theorem [[twisted-hnn-mf-permanence-with-corona-conjugator]]
   (Section 3); and
4. records why the universal HNN algebra is genuinely necessary: the
   concrete tensor-model representation of the rope group is provably NOT
   faithful (Section 3.4), so any assembly that stops at the explicit
   representation has a gap.  The earlier sessions' "conditional /
   free-entropy obstruction" verdicts concerned the strictly stronger
   reduced-C-star-norm (trace-regular / GKMP) convention and machine-engine
   compilers, not this theorem; see Section 5.

## 2. Verified inputs

**(L1) Shulman's amalgam criterion.**  T. Shulman, *The MF property for
amalgamated free products*, arXiv:2603.13564v2.  Theorem 16 (body
numbering):

> Let `A, B, C` be separable C-star-algebras and `theta_A : C -> A`,
> `theta_B : C -> B` be inclusions.  Then `A *_C B` is MF if and only if
> there exist embeddings `phi_A : A -> prod M_n / sum M_n` and
> `phi_B : B -> prod M_n / sum M_n` such that
> `phi_A o theta_A = phi_B o theta_B`.

Verified verbatim from the v2 PDF on 2026-08-26.  CITATION TRAP: the v2
introduction still advertises this statement as "Th. 20" (and the central
HNN theorem as "Th. 29") — stale v1 numbering.  In the v2 body the
amalgam criterion is **Theorem 16**, the central-HNN theorem is
**Theorem 25**, and the same file defines the universal C-star HNN
extension `<A, t | t^-1 B t = C, phi>` with existence, uniqueness, and its
universal property (Section 5 of the paper).  `A *_C B` denotes the FULL
(universal) amalgamated free product; only injective *-homomorphisms
("embeddings"), not unital ones, are required, and the non-unital case is
handled in the paper by forced unitizations.  We consume only the "if"
direction.

**(L2) Britton's lemma** (classical): the base group embeds in a group HNN
extension, and a word `g_0 t^{e_1} g_1 ... t^{e_k} g_k` with no pinch is
nontrivial.  Used for: `S_e = <F, F^v> = F *_{N_e} F^v` inside the central
rope, and for the FIN-branch embedding of the bridge value into the rope.

**(L3) Effective Higman embedding**
([[mikaelian-explicit-higman-embedding]]): an algorithm turning a
recursively enumerable presentation into a finite presentation `H_e =
<X_e | R_e>` plus embedding words.  Only the OUTPUT PRESENTATION and the
embedding words are consumed (to build a Mikhailova subgroup); no
approximation property of `H_e` is used, so the compiler never needs the
Higman host to be MF, RF, or anything else.

**Standard C-star facts** (with one-line proofs in place): MF passes to
C-star-subalgebras (restrict the corona embedding).  A finite direct sum of
MF algebras is MF.  `M_2(prod M_n / sum M_n) = prod M_{2n} / sum M_{2n}`
embeds into `prod M_m / sum M_m` (send the class of `(T_{2n})` to the class
of `(S_m)` with `S_m = T_{2 floor(m/2)} + 0`-padding; entrywise *-hom,
`limsup`-isometric).  Every separable C-star-subalgebra of a norm reduced
product `prod_n B_n / sum_n B_n` of MF algebras is MF: given finitely many
elements and polynomials, choose one late coordinate per required lower
norm estimate and take the finite direct sum of those coordinates — late
choices give the upper estimates, the direct sum gives all lower ones, and
a finite direct sum of MF algebras is MF; diagonalize over finite sets and
tolerances.  The subgroup inclusion `L(G) <= L(R)` of group von Neumann
algebras for `G <= R` (classical).

## 3. The analytic core, self-contained

### 3.1 Theorem (corona-conjugator HNN permanence)

See [[twisted-hnn-mf-permanence-with-corona-conjugator]].  Let

```text
R = < G, t | t s t^-1 = theta(s), s in S >                     (A1)
```

be a group HNN extension: `S <= G`, `theta : S -> theta(S) <= G` an
isomorphism.  Suppose `G` has a regular operator-MF realization: a
separable unital MF algebra `A`, a homomorphism `rho : G -> U(A)`, and a
tracial state `tr` on `A` with `tr(rho(g)) = delta_{g,1}` (this forces
`rho` injective).  Suppose some embedding `iota : A -> prod M_n / sum M_n`
admits a unitary `W` in `prod M_n / sum M_n` with

```text
W iota(rho(s)) W* = iota(rho(theta(s))),  s in S.              (A2)
```

Then `R` has a regular operator-MF realization; in particular `R` is
operator-MF.  Taking `theta = id`, `W = 1` recovers
[[regular-mf-central-hnn-closure]] with no further input.

### 3.2 Proof

Write `Q = prod M_n / sum M_n`, `D = C*(iota rho(G)) <= Q`,
`B_0 = C*(iota rho(S))`, `B_1 = C*(iota rho(theta S))`, and
`Theta = Ad(W)|_{B_0} : B_0 -> B_1`, a *-isomorphism carrying generators to
generators by `(A2)`.  Let `U` be the universal C-star HNN extension of `D`
by `Theta` (Shulman's definition, (L1)): the universal unital C-star
algebra generated by a unital copy of `D` and a unitary `u` with
`u b u* = Theta(b)`, `b in B_0`.

**Step 1: `U` embeds in a full amalgamated free product** (corner argument;
the idea is Ueda's, Illinois J. Math. 52 (2008) 705-725, and the proof
below is a self-contained universal-property computation).  Set
`C = B_0 + B_1` (C-star direct sum), `A_1 = M_2(D)`, `A_2 = M_2(B_0)`,
with unital inclusions

```text
iota_A(c_0, c_1) = diag(c_0, c_1)            in A_1,
iota_B(c_0, c_1) = diag(c_0, Theta^-1(c_1))  in A_2,           (A3)
```

and `P = A_1 *_C A_2` the full amalgam.  Both inclusions send the unit
`(1,1)` to `1` since `1 in B_0` and `1 in B_1`.  Let `e_{ij}` and `f_{ij}`
be the matrix units of `A_1` and `A_2`.  In `P`,

```text
e_11 = iota_A(1,0) = iota_B(1,0) = f_11 =: e,
e_22 = iota_A(0,1) = iota_B(0,1) = f_22.                        (A4)
```

Define `pi_D : D -> ePe` by `pi_D(d) = diag(d,0)` (a unital *-hom into the
corner) and `w = e_12 f_21 in ePe`.  Using `(A4)`:
`w w* = e_12 f_22 e_21 = e_12 e_22 e_21 = e` and
`w* w = f_12 e_22 f_21 = f_12 f_22 f_21 = f_11 = e`, so `w` is a unitary of
`ePe`.  For `b in B_0`, `diag(b,0) = iota_A(b,0) = iota_B(b,0)`, so

```text
w pi_D(b) w* = e_12 (f_21 diag(b,0) f_12) e_21
             = e_12 diag_{A_2}(0,b) e_21
             = e_12 iota_B(0,Theta(b)) e_21
             = e_12 diag_{A_1}(0,Theta(b)) e_21
             = pi_D(Theta(b)).                                  (A5)
```

By the universal property of `U`, there is `Phi : U -> ePe <= P` with
`Phi|_D = pi_D`, `Phi(u) = w`.  To see `Phi` is injective, map back: let
`Psi_1 : A_1 -> M_2(U)` be the entrywise inclusion `D <= U`, and
`Psi_2 : A_2 -> M_2(U)` be `Ad(diag(1,u))` composed with the entrywise
inclusion `B_0 <= U`.  On `C`: `Psi_1(iota_A(c_0,c_1)) = diag(c_0,c_1)` and
`Psi_2(iota_B(c_0,c_1)) = diag(c_0, u Theta^-1(c_1) u*) = diag(c_0,c_1)`.
So the pair induces `Psi : P -> M_2(U)`, and `Psi Phi` fixes every element
of `D` and sends `u` to `u` (both computed in the `(1,1)` corner).  Hence
`Phi` is injective and `U` embeds in `P`.

**Step 2: `P` is MF.**  Apply (L1) with
`phi_A = j o M_2(iota') : A_1 -> prod M_m / sum M_m` and
`phi_B = j o Ad(diag(1,W)) o M_2(iota'|_{B_0})`, where `iota'` is `iota`
corestricted, `M_2(Q) = prod M_{2n}/sum M_{2n}`, and `j` is the padding
embedding of Section 2.  On `C`:
`phi_A(iota_A(c_0,c_1)) = j(diag(iota c_0, iota c_1))` and
`phi_B(iota_B(c_0,c_1)) = j(diag(iota c_0, W iota(Theta^-1 c_1) W*)) =
j(diag(iota c_0, iota c_1))` by `(A2)`.  The compatibility hypothesis
holds, so `P` is MF, hence so are `ePe` and its subalgebra `U`.

**Step 3: the group embeds, with regular trace.**  `T := tr o iota^-1` is a
tracial state on `iota(A) >= D` with `T(iota rho(g)) = delta_{g,1}`.  The
GNS representation `pi_T` of `D` has orthonormal basis
`{ iota rho(g) xi_T : g in G }` (orthonormality is exactly the regular
character), so `pi_T(iota rho(g)) = lambda_G(g)` and `pi_T(D) <= L(G)`.  By
Britton (L2), `G <= R`; compose with the classical inclusion
`L(G) <= L(R)` to get a *-hom `pi : D -> L(R)` with
`pi(iota rho(g)) = lambda_R(g)`.  The pair `(pi, lambda_R(t))` is
covariant: `lambda_R(t) pi(b) lambda_R(t)* = pi(Theta(b))` holds on the
generators `iota rho(s)` because `t s t^-1 = theta(s)` in `R`, and two
*-homs agreeing on generators of `B_0` agree on `B_0`.  The universal
property of `U` gives `sigma : U -> B(l^2 R)` with
`sigma(iota rho(g)) = lambda_R(g)`, `sigma(u) = lambda_R(t)`.

Let `j_R : R -> U(U)` send the base `g` to the class of `iota rho(g)` and
`t` to `u`; the defining relations of `R` hold in `U`, so `j_R` is a
homomorphism, and `sigma o j_R = lambda_R` is injective, so `j_R` is
injective.  Finally `A' = C*(j_R(R)) <= U` is separable and MF, and
`tr' = tau_{L(R)} o sigma|_{A'}` is a tracial state with
`tr'(j_R(r)) = delta_{r,1}`.  So `(A', j_R, tr')` is a regular operator-MF
realization of `R`.  QED.

Note there is no reduced HNN normal form and no freeness estimate anywhere:
faithfulness on the group is bought entirely by the regular trace of the
BASE plus the left regular representation of `R` itself, and the
operator-norm approximation is bought by (L1) applied to the UNIVERSAL
algebra.  This is why the free-entropy obstruction to conjugating two
regular models of a free subgroup — real, and fatal for strongly convergent
models — never appears at this convention.

### 3.3 The two applications in the compiler

*Central rope.*  `Gamma_e = <K_e, v | [v, L_e]>` with `K_e` the product
witness — a direct product of finite-rank free groups times `F times P`,
hence residually finite.  A separating chain of finite quotients in their
left regular representations gives a regular realization `(A_0, rho_0,
tr_0)` of `K_e` inside a matrix corona, with `iota_0` the inclusion and
`W = 1`, `theta = id` on `S = L_e`.  Theorem 3.1 gives a regular
realization of `Gamma_e`.  (On every branch; residual finiteness of `K_e`
is branch-independent.)

*Twisted rope edge.*  `R_e = < Gamma_e times Q_e, u | u(s,1)u^-1 =
(s, tau_e(s)), s in S_e >` on `e in INF`, where `Q_e = H = B3(1)` is
residually finite.  Take the peer construction
([[regular-mf-tensor-sync-proves-twisted-rope-mf]], re-derived in Section
4): with `(A_1, rho_1, tr_1)` the regular realization of `Gamma_e` from the
previous step, `beta_n : H -> B_n` eventually separating finite quotients,
and `lambda_n : Gamma_e -> W_n` the graph-witness finite maps with
`ker(lambda_n|_{S_e}) <= ker(beta_n tau_e)` (RTS1, re-derived below), set
`G_n = image((lambda_n, beta_n))`, form the norm reduced product
`E = prod_n (A_1 tensor M_{|G_n|}) / sum_n (...)`,

```text
V(g,q) = [ rho_1(g) tensor L_n(lambda_n(g), beta_n(q)) ]_n,     (A6)
```

and `W = [1 tensor W_n]_n`, where `W_n` conjugates the two edge
restrictions of the left regular representation `L_n` of `G_n`; such `W_n`
exists because RTS1 makes the kernels of `s |-> (lambda_n(s),1)` and
`s |-> (lambda_n(s), beta_n tau_e(s))` EQUAL, and the restriction of the
regular representation of a finite group to two isomorphic-image subgroups
of equal index is the same multiple of the corresponding regular
representations.  Then `W V(s,1) W* = V(s, tau_e(s))` exactly, the
ultralimit trace `T = lim_omega (tr_1 tensor tr_{M_{|G_n|}})` satisfies
`T(V(g,q)) = delta_{(g,q),(1,1)}` (first factor kills `g != 1`; eventual
separation kills `q != 1`), and `A = C*(V(Gamma_e times Q_e), W) <= E` is a
separable MF algebra (Section 2) carrying the regular trace `T|_A` and the
conjugator.  Choosing any corona embedding `iota` of `A`, Theorem 3.1
applies with `S = S_e times 1`, `theta(s,1) = (s, tau_e(s))`, and yields a
regular operator-MF realization of `R_e`.

### 3.4 Why the universal algebra is necessary

The concrete representation `(V, W)` of `R_e` in `E` is NOT faithful: the
finite maps `lambda_n` kill the Mikhailova factor `K_e^0`, so for
`gamma in K_e^0` with `(gamma,1)` outside `S_e times 1` (Britton-nontrivial
commutator), `W` commutes with `V(gamma, 1)` although `[u, (gamma,1)] != 1`
in `R_e`.  Any assembly that asserts faithfulness of the explicit model is
therefore wrong; the group injectivity must be run at the universal
algebra, exactly as in Step 3 above.  (This also explains why no
strong-convergence estimate is needed: nothing about the explicit model's
Britton words is claimed.)

## 4. The compiler, re-derived link by link

All notation from `research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md`.

1. **Upper bound** ([[mf-recognition-has-a-pi2-upper-bound]]): the
   microstate normal form with the void-challenge escape disjunct removes
   the word-problem oracle, and each inner certificate is a finite system
   of polynomial (in)equalities over the reals, decidable by
   Tarski-Seidenberg.  `MF_fp in Pi^0_2`, `NONMF_fp in Sigma^0_2`.
   (Substantially kernel-checked: `MicrostateNormalForm.lean`.)
2. **Switch** ([[exact-second-level-non-mf-switch-unconditional-proof]]):
   the `E/1` ray with event stream from first-halting stages gives
   uniformly a countably generated recursive `S_c` with `S_c = 1` on
   `INF(c)` and `S_c = E` on `FIN(c)`; generatorwise proof re-checked, no
   embedding theorem used.  Seed `E` = the fixed finitely presented non-MF
   group with its MF-invisible mark (kernel-checked lane).
3. **Bridge** ([[bidirectional-hnn-bridge-trivial-value-is-residually-finite]]):
   `Q_e = B3(S_c)` is an HNN extension of `S_c * F(x,y)` (free-basis
   argument via the retraction killing `S_c`), is generated by `x,y,t`, and
   Tietze rewriting gives a uniform recursive `N_e normal F(x,y,t)`.
   Killing `S_c` gives `B3(S_c) ->> B3(1)`, so `N_e <= N_+` uniformly, with
   equality on `INF`; `B3(1) = (F_oo x F_oo) x| Z` embeds in
   `F_2 times F_2` (checked: the images of the two normal-closure free
   bases are free bases, and the image meets the diagonal cyclic subgroup
   trivially), so `H = B3(1)` is residually finite.  On `FIN`,
   `E <= S_c <= Q_e`.
4. **Mikhailova witness** ([[mikhailova-fiber-product-gives-regular-mf-benign-compiler]]):
   `M_e = <(x,x),(r,1)> = {(u,v) : u =_{H_e} v}` — one inclusion is by
   inspection; conversely `u =_{H_e} v` writes `uv^-1` as a product of
   conjugates of relators, and conjugation by diagonal pairs keeps
   `(N x 1)` inside the subgroup, with `(u,v) = (uv^-1,1)(v,v)`.  With
   `K_e^0 = F times F(X_e) times F(X_e)`, `i_e(f) = (f, w_f, 1)`,
   `L_e^0 = F times M_e`: membership `i_e(f) in L_e^0` iff `w_f =_{H_e} 1`
   iff `f in N_e` (injectivity of the Higman embedding), and the first
   coordinate makes `i_e` injective.
5. **Graph witness and finite CEP**
   ([[three-bridge-is-cyclic-fiber-product-with-finite-cep]],
   [[finite-cep-kernel-witness-synchronizes-rope]]): `H` is the kernel of
   the exponent-difference character `P = F_2 times F_2 -> Z`, so `H` is
   finitely generated normal with `P/H = Z`; given finite-index `J normal
   H`, the intersection `M` of the finitely many `Z`-conjugates of `J` is
   `P`-invariant, `P/M` is (finite)-by-`Z`, and quotienting the cyclic
   part by the order of its action gives finite `r : P -> C` with
   `ker(r|_H) = M <= J`.  The graph `L^g = graph(F -> H -> P)` is closed
   in `F times P` and `L^g intersect (F times 1) = N_+ times 1`.
6. **Product witness** ([[graph-witness-product-supplies-tensor-sync]]):
   `K_e = K_e^0 times K^g`, `L_e = L_e^0 times L^g`, `F` diagonal; the cut
   is `N_e intersect N_+ = N_e` by (T5).  Ambient = product of free
   groups, residually finite on EVERY branch.
7. **Central rope and `S_e`**: `Gamma_e = <K_e, v | [v,L_e]>`;
   `L_e intersect F = N_e` and Britton give
   `S_e = <F, F^v> = F *_{N_e} F^v`; `tau_e : S_e -> Q_e` is `q_e` on the
   first copy, trivial on the second (well-defined: both kill `N_e`).
8. **RTS1 on INF**: `lambda_n` kills `K_e^0`, maps `(f,p) in K^g` to
   `(r_n j q_+(f), r_n(p))` and `v` to the coordinate swap (well-defined:
   `L_e` lands on the diagonal, which the swap centralizes).  On `S_e`,
   `lambda_n(s) = (r_n j tau_0(s), r_n j tau_1(s))` where `tau_0 = tau_e`
   and `tau_1` is the opposite fold, so
   `ker(lambda_n|_{S_e}) <= ker(r_n j tau_e) <= ker(beta_n tau_e)` by the
   finite-CEP choice `ker(r_n j) <= ker(beta_n)`.
9. **Finite presentation** (T16): `R'_e = < Gamma_e times F, u |
   u(i(a),1)u^-1 = (i(a),a), u(i(a)^v,1)u^-1 = (i(a)^v,1), a in A >` is
   finite (`K_e` finitely presented, `L_e`, `F` finitely generated).  Both
   displayed relation families extend from generators to all `f in F`
   (both sides are homomorphic in `f`), and for `n in N_e`, `i(n)^v = i(n)`
   in `Gamma_e` forces `(1,n) = 1`, so the second factor descends to
   `Q_e`; the two canonical maps between `R'_e` and the abstract rope
   `R_e` are mutually inverse on generators.  So `e |-> code(R'_e)` is the
   computable output family.
10. **FIN branch**: the base `Gamma_e times Q_e` embeds in the HNN `R_e`
    (Britton), `E <= Q_e`, and operator-MF passes to subgroups (restrict
    the corona embedding); so `R_e` is not MF.
11. **INF branch**: Sections 3.3; `R_e` is regularly operator-MF realized,
    in particular MF.
12. **Completeness bookkeeping**: `INF` is `Pi^0_2`-complete (s-m-n
    construction re-checked in the switch note), so
    `INF <=_m MF_fp` and `FIN <=_m NONMF_fp`, giving `(A0)` with the upper
    bounds of item 1.

## 5. Notions, and what remains open

The theorem is about the operator-norm matricial-embedding predicate for
GROUPS (Definition 3 of Shulman's paper = CDE = the repository's
`IsOperatorMF`).  Three neighboring statements are NOT claimed and remain
open questions of independent interest:

- the trace-regular / reduced-norm strengthening (models strongly
  convergent to `C*_r(R_e)`, the GKMP convention): the INF branch above
  produces an abstract regular trace, not strong convergence; the
  free-entropy obstruction and the GKMP-machinery route
  ([[strong-convergence-fell-shifted-hnn-model]]) belong to THAT question,
  whose recognition problem also lacks a known `Pi^0_2` upper bound;
- hyperlinearity of the positive branch
  ([[mf-compiler-positive-branch-is-hyperlinear]]);
- the sofic analogue ([[sofic-safe-finite-presentation-compiler]]), where
  the tensor trick has no permutation counterpart compatible with
  Britton compression.

Also corrected: [[fp-mf-completeness-wall-is-route-independent]] asserted
the completeness target was EQUIVALENT to the machine-engine free-edge
permanence wall; the Mikhailova/graph-witness compiler shows the wall is
sufficient-side only, because its benign ambient is residually finite on
every branch and its twist lands in the residually finite bridge value.

## 6. Concurrent note

A parallel session's completion note,
`research/artifacts/regular-mf-tensor-sync-shulman-completion-2026-08-26.md`,
reached the same Shulman-plus-corner closure independently (and records the
same non-faithfulness caution).  This audit additionally re-proves the
corner embedding and the group-injectivity step self-containedly, fixes the
v1/v2 theorem-numbering trap for citations, and re-derives the entire
compiler chain link by link.
