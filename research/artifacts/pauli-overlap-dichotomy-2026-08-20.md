# Ingestion audit: the overlap/holonomy dossier

Date: 2026-08-20

## 1. Novelty sweep: two of the three headline items were already nodes

| dossier item | verdict |
| --- | --- |
| (1) regular-graph overlap bound with `lambda_min` | **new**; its complete-graph case (2) is the existing `marked-copy-collision-forces-overlap-mass` |
| (3) three copies at `beta=3/7` give `9/49` | present (unordered form of the existing `18/49`) |
| (4)-(6) fixed finite-factor holonomy pays relator energy | **new** |
| (8) contraction capacity `M^2/q - M` | **new**; strengthens `gram-branching-capacity-with-overlap` from partial isometries to contractions |
| (9) the Pauli packet is already supercritical, `R=5/4`, forced `5/32` | **new, and unverified** -- see section 3 |
| (10) threshold lemma | already `soft-block-mass-yields-fractional-branch`, landed 2026-08-19 |
| (11) `rho(B)>1` suffices | already `fractional-source-branch-pressure`, landed 2026-08-19 |
| (12) tail-or-flat dichotomy and the `3/4 - 1/sqrt 2` gap | already `pauli-block-tail-or-flat-rigidity-dichotomy` and `constant-block-contraction-gap` |
| (15)-(16) transverse independence, `dist^2 + dist^2 >= c(1-c)`, `3/32` at `c=1/4` | **already present verbatim** as `tensor-independent-child-carrier-gap`, including the `3/32` |
| (17) Leavitt perfect-pairing endgame | **already present, and already refuted**: `rectangular-escape` shows the four-map pairing argument is evaded because the codomains grow, and it invalidates `rectangular-whole-map-extraction`. The live target is `same-orbit-closure`. |

The dossier's two most emphasized contributions -- section 7 ("where I'd depart
most radically") and section 8 ("an even more brutal finite endpoint") -- are
therefore both already in the graph, the second together with the reason it does
not close.  The dossier does reach the right conclusion about section 8 on its
own ("the giant open issue is ... prevent rectangular orbit enlargement"), which
is exactly `same-orbit-closure`.

## 2. What was verified before wiring

Three lemmas were re-derived here rather than transcribed:

- **(8)** Put `S = sum_a X_a X_a^*`, supported in `Q`.  Then `tau(S)=M_tot`,
  Cauchy--Schwarz against `Q` gives `tau(S^2) >= M_tot^2/q`, traciality gives
  `tau(S^2) = sum_(a,b) ||X_b^* X_a||_2^2`, and contractivity gives
  `sum_a ||X_a^*X_a||_2^2 = sum_a tau(|X_a|^4) <= M_tot`.  Subtracting yields
  `(CBC1)`.
- **(1)** With `G_ij = tau(Q_iQ_j)` positive semidefinite and `A` the adjacency
  matrix of an `r`-regular graph, `A >= (r/m)J + lambda_min(I - J/m)`.  Pairing
  with `G`, using `<I,G> = m beta` and `<J,G> = tau(S^2) >= (m beta)^2` for
  `S = sum_i Q_i`, gives exactly the stated bound; setting `r=m-1`,
  `lambda_min=-1` recovers the complete-graph case.
- **(4)** Compress to the corner: `||W-1||_2^2 >= tau(R)(2 - 2 Re tr(A)tr(H))`
  and `|tr H| <= 1`, so the minimum over all multiplicity behaviour is
  `2(1-|tr A|) tau(R)`.  For two distinct `S_3` reflections `[U,V]=(UV)^2` is
  rotation by 240 degrees, normalized trace `-1/2`, giving `(FHO3)`.

## 3. Subsequent closure of the headline number

**Update, 2026-08-21.**  The original audit below was correct when written,
but is now superseded by
`transported-coefficient-raw-character-isotropic-mixing`.  Its exact rational
block tables name `X_i=Q(comb^*B_i comb)Q` and give masses `3/8` and `1/4`.
Thus `M_tot=5/8`, `q=1/2`, and the overlap floor is `5/32`; the replay is
`experiments/verify_pauli_incoming_mass.py`.

### Original audit

The claim that carries the dossier's main structural conclusion -- "the existing
Pauli packet is ALREADY supercritical" -- rests on

```text
M_tot = 5/8   into a corner of trace   q = 1/2.
```

A grep of `notes/` for `5/8` and `5/32` returns nothing.  The packet notes
record `tau(E)=tau(R_0)=tau(R_1)=1/8`, `tau(F)=1/4`,
`tau(F_eps)=tau(G_eta)=1/8`, `tau(F_eps G_eta)=1/64`.  So `(PIM1)` names two
transported involutions that the notes do not identify and asserts a mass budget
the notes do not contain.  It is wired as an **open** claim,
`pauli-packet-incoming-mass-exceeds-corner-capacity`, with the recomputation
spelled out in its Attempts.  The general theorem it instantiates,
`contraction-branch-capacity-forces-collision`, is established independently.

## 4. A consistency check that a later reader will want

`(PIM3)` produces a canonical, supercritical configuration, which looks like it
should collide with `supercritical-network-needs-noncanonical-cuts`.  It does
not.  That gate forbids a canonical supercritical network whose *overlap
vanishes*; here the overlap is bounded below by `5/32` and the exact model pays
it as well.  Supercriticality of the mass budget is therefore a **budget**, not
an obstruction -- which is what makes the dossier's own framing correct: the
question becomes what the relations force the compulsory overlap to do, and that
is `mixed-relations-force-holonomy-or-transverse-recovery`.

The same falsification gate applies to that node as to its two neighbours in the
adjacent lanes: any derivation of the dichotomy from the overlap alone, not
using a property the exact atlas model fails, is wrong.
