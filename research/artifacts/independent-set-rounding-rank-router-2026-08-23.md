# Independent-set rounding and rank-router splice

Date: 2026-08-23

This note records the compiler interface obtained by combining the fixed
synchronous non-RU game in Cairn with the outcome-count-independent rounding
and synchronous independent-set reduction of Mančinska--Spaas--Spirig--
Vernooij, *Gap-preserving reductions and RE-completeness of independent set
games* (arXiv:2505.05253v2).  The deductions and constants below are accepted
as supplied.  Their purpose is not a literature survey: they replace the
nonlinear predicate/common-Gram interface by row PVM extraction and one
two-copy affine block router.

## 1. Sub-POVM completion without an alphabet loss

Let `0<=a_j<=1`, `s=sum_j a_j<=1`, and

```text
mu=tau(1-s),              eta=sum_j tau(a_j-a_j^2).
```

Adding `a_0=1-s`, applying the constant-nine simultaneous POVM
orthogonalization, and merging the deficit projection into one genuine
outcome gives an `m`-outcome PVM `(q_j)` with

```text
sum_j ||a_j-q_j||_2^2 <= 11 mu+9 eta.                 (ISR1)
```

There is no dependence on `m`.  If the `a_j` lie in prescribed coarse
corners `p_kMp_k`, the construction can be performed in each corner and the
resulting PVM refines the same coarse PVM, with the same summed bound.

## 2. The synchronous independent-set interface

For a fixed `t`-question synchronous game `G`, the sharp synchronous part of
the independent-set reduction says

```text
omega_s^*(G)<1-epsilon
 => omega_s^*(I(G))<1-zeta epsilon^2/t.                (ISR2)
```

Equivalently, target loss `delta` decodes source loss
`O(sqrt(t delta))`.  A tracial group decoder already produces one
synchronous family and therefore never pays the later fourth-root
almost-synchronous conversion.

Every target losing atom is a forbidden overlap of two projections and has
literal energy

```text
tau(P_i^u P_j^v)=||P_i^uP_j^v||_2^2.                 (ISR3)
```

Thus the arbitrary Boolean predicate disappears before groupification.
Universal invalid vertices may also be deleted: if a graph vertex is
adjacent to every other vertex, every perfect synchronous independent-set
strategy assigns it projection zero.

## 3. Flexible row PVMs from independent clocks

Let `Q` be the marked projection and let `U^N=1` have spectral projections
`E_v`.  Put `a_v=QE_vQ`.  Then `(a_v)` is a POVM in `QMQ` and

```text
D_Q=tau(Q)-sum_v tau(a_v^2)
   =sum_(v!=w)||E_vQE_w||_2^2
   <=Delta_N^(-2)||[Q,U]||_2^2,                       (ISR4)
Delta_N=2 sin(pi/N).
```

Simultaneous orthogonalization therefore gives a genuine PVM `(p_v)` on
`Q` with

```text
sum_v ||QE_vQ-p_v||_2^2
 <=9 Delta_N^(-2)||[Q,U]||_2^2.                       (ISR5)
```

One independent order-`N` clock per question allows arbitrary outcome
multiplicities.  No row needs to be conjugate to a common clock.

## 4. Pair-local overlap wordization

For one forbidden pair, take `S=P_j^v`, `A=1-2P_i^u`, and `B=1` in
`partial-isometry-swap-wordizes-one-bcs-gram-row`.  Its ordinary swap word
then satisfies

```text
4||P_i^uP_j^v||_2^2
 <=||C_(i,u;j,v)-1||_2^2
 <=20||P_i^uP_j^v||_2^2.                              (ISR6)
```

The projection source may depend on the forbidden pair, because all rows
already belong to one global PVM strategy.  This is a valid fallback and
shows precisely why the independent-set normal form removes the analytic
common-Gram gate.

## 5. Rank conjugacy is the stronger overlap detector

For arbitrary projections `P,Q`, let

```text
A=1-2P,       B=1-2Q,
R=diag(A,B),  S=diag(AB,1)
```

in `M_2(M)` with normalized trace.  For every unitary `U`, trace conservation
gives

```text
2||PQ||_2^2 <= ||URU^*-S||_2.                         (ISR7)
```

Indeed `tau_2(R)=1-tau(P)-tau(Q)` while
`tau_2(S)=1-tau(P)-tau(Q)+2tau(PQ)`.  Conversely, if `PQ=0`, then `P,Q`
are orthogonal and the negative spectral projections of `R` and `S` are
`diag(P,Q)` and `diag(P+Q,0)`.  They have the same center-valued trace, so
some unitary satisfies `URU^*=S`.

For forbidden pairs `f` with weights `alpha_f` and conjugacy-word defects
`e_f=||U_fR_fU_f^*S_f^*-1||_2^2`, weighted Cauchy--Schwarz yields

```text
sum_f alpha_f e_f
 >=4(sum_f alpha_f||P_fQ_f||_2^2)^2.                  (ISR8)
```

This converts the fixed independent-set gap into a fixed ordinary-word
energy floor once `R_f,S_f` have been authenticated.

## 6. Original interface and tensor-closure correction

The initially proposed algebraic object was a finite **hybrid rank router**.
Given the already decoded involution words
`A,B`, it must route

```text
R=diag(A,B),             S=diag(AB,1)                 (ISR9)
```

into two equal role blocks using ordinary group relators, with a
dimension-free robust decoding estimate.  For a perfect target strategy
every forbidden pair has `PQ=0`, so the converse above supplies the stable
letter satisfying `URU^*=S`; exact tracial completeness is automatic once
the routing identities are exact.

This appeared strictly smaller than the earlier static BCS target:

```text
old: nonlinear predicate + selected finite type + common Gram + alignment
new: independent row clocks + affine four-slot router + stable conjugacy.
```

The existing two-letter dihedral swap identity is relevant because it can
read one desired block intertwining while the unused complementary block
contributes only nonnegative energy.  It does not yet assemble both hybrids
in `(ISR9)`.  A finite nested D8 role tree, unequal-index proper-corner
router, or another canonical-trace two-cell seemed to be the remaining
task.

That universal formulation is refuted by
`hybrid-rank-router-tensor-closure-obstruction`.  Three exact admissible
scalar extensions in the negative marked sector tensor to an exact
representation with `A=B=-1`; universal routing gives `R=-I,S=I`, while the
tensor product still satisfies the conjugacy relator.  Thus no ordinary
group gadget can combine universal soundness with exact extension for every
zero-overlap pair.

The corrected interface is `source-specific-pointed-rank-router-face`: one
distinguished perfect tracial source, plus routing soundness only on a
non-tensor-closed global moment face containing canonical microstates.

## 7. Corrected conditional terminal

Apply `(ISR2)` to `oracularizable-tracial-nonru-game-exists`.  Exact
commuting completeness supplies a perfect tracial strategy for `I(G)`;
finite-dimensional strategies have fixed loss `delta_0>0`.  Independent
clocks extract the row PVMs on the marked corner.  If a hyperlinear
microstate kept the marked involution separated, the corner would have
fixed positive normalized trace.  Pointed source routing and `(ISR8)` would
then force a fixed relator-energy floor, contradicting vanishing microstate
defect.  Exact one-source completeness keeps the mark nontrivial.  Therefore
the source-specific pointed rank face is a terminal input to
`non-hyperlinear-group`; the universal hybrid router is not.

This route is independent of the Atlas, SL3, toric, and fixed-mass
same-Gram lanes.  It does not claim the pointed source face already exists.
