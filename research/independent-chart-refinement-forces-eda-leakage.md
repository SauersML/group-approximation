---
rg: 2
id: independent-chart-refinement-forces-eda-leakage
kind: claim
title: Independent chart refinement creates an atomwise EDA leakage floor
distinct_from:
  raw-incidence-and-one-hot-pvms-tensor-separate: that gives a complete finite raw-incidence and one-hot counterpacket with saturation deficit 41/42; this tensors an arbitrary conductor edge, tracks its existing first-exit scalar exactly, and proves the atomwise EDA leakage cannot be derived from that ledger.
  folner-multiplicity-atlases-have-vanishing-first-exit: that constructs conductor carriers whose base first exits vanish; this shows that refining any such carrier by independent chart labels restores a fixed atomwise exit floor.
  equal-rank-denominator-edges-authenticate-decoded-atoms: that converts the atomwise section leakages into the desired chart saturation; this proves those atomwise leakages are a genuinely new mixed input rather than a consequence of carrier-level first exit.
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let `R,S` be
equal-trace projections with

```text
tau(R)=tau(S)=mu,                                      (ICR1)
```

and let `V` be unitary. Write the carrier-level first exit as

```text
L=||(1-S)VR||_2^2.                                    (ICR2)
```

Let `(P_i)_(i=1)^q` and `(Q_i)_(i=1)^q` be the two coordinate PVMs on
`l^2(Omega x Omega)`, where `|Omega|=q`. Thus

```text
tr(P_i)=tr(Q_i)=1/q,          tr(P_iQ_j)=1/q^2.         (ICR3)
```

In the tensor product define equal-rank decoded atoms and their transition
by

```text
E_i=R tensor P_i,       F_i=S tensor Q_i,
T=V tensor I.                                           (ICR4)
```

Then the complete atomwise section leakage is exactly

```text
sum_(i=1)^q ||(1-F_i)T E_i||_2^2
 =mu(1-1/q)+L/q.                                       (ICR5)
```

In particular, even if the carrier is transported perfectly (`L=0`), its
independent `q`-atom refinements pay `mu(1-1/q)`. For the arithmetic shell
`q=42`, the floor is `41mu/42`.

Every operator used in a conductor/root defect ledger may be extended as
`X tensor I`; all of its normalized Hilbert--Schmidt defects and all
carrier-level first exits are unchanged. The same is true for an exact raw
denominator incidence packet placed on another tensor factor. Consequently,
if a sequence of conductor atlases has `L->0` and carrier mass bounded below,
tensoring independent chart coordinates makes every old marginal/root/raw
ledger tend to zero while `(EDA11)` stays bounded below by `41mu/42`.

Therefore no dimension-independent inequality of the form

```text
sum_i EDA11_i <= C(carrierFirstExit+rootDefect+rawIncidence)  (ICR6)
```

can hold without an additional hypothesis coupling the decoded atoms to the
actual section transition. The needed positive statement cannot merely
refine carrier-level conductor bands and then invoke their first-exit
ledger. It must construct the chart atoms in a section-functorial label
algebra, or directly include the atomwise leakages on the right. This is the
exact remaining mixed-root Gram input.

Scope: the independent label refinement is not asserted to arise from the
full arithmetic root-word packet. Precisely, it violates the still-missing
requirement that decoded atoms be functorial functions of that packet. The
countermodel rules out deriving this requirement from the presently listed
carrier-level conductor, root-defect, and raw-incidence scalars; it does not
rule out a new mixed-root decoder which enforces it.
