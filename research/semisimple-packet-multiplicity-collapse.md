---
rg: 2
id: semisimple-packet-multiplicity-collapse
kind: claim
title: Compression collapse for semisimple packets via self-normalized multiplicity defects
distinct_from:
  compression-torsion-collapse: That established claim needs the orbit images to commute pairwise, so its discrete invariant is a joint spectral rank; this one allows any packet whose finite windows generate finite-dimensional C-star algebras, replacing joint eigenspace ranks by irreducible-module multiplicity vectors — Clifford and Weyl packets included, where joint spectral projections do not exist.
artifacts:
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
  - notes/FALSE_KAZHDAN_COMPRESSION_INDEX_TO_PHASE.md
---

Let `W` be countable, `pi` a norm-corona representation, `Lambda <= W`
Kazhdan, `s` a one-sided compressor of `Lambda`, and `k` an element whose
image has finite order, such that the images of every finite window of the
`Lambda`-orbit of `k` generate a finite-dimensional C-star algebra (of
dimension bounded in terms of the window alone), and which `pi` identifies
with its `s Lambda s^{-1}`-conjugates.  **Claim (open):** `pi` identifies
`k` with its entire `Lambda`-conjugation orbit.

**Proposed mechanism** — the reason to believe the theorem underneath the
involution proof is *a discrete defect can normalize itself*:

1. operator-norm perturbations of a fixed finite-dimensional C-star algebra
   correct to exact copies, so each window's packet algebra
   `A = (+)_j M_(n_j)(C)` can be exactified coordinatewise;
2. a failure of the desired identification then carries an integer
   **multiplicity defect vector** `m_n in N^r` — multiplicities of the
   irreducible `A`-modules on which the two sides disagree — which is `>= 1`
   somewhere whenever the relation fails and cannot fade continuously;
3. normalize at `‖m_n‖_1`: the defect supplies its own scale, and
   `scaled-kazhdan-transport` is already proved for arbitrary weights.  The
   open bookkeeping is exactification-covariance: the covariance errors must
   have Hilbert mass `o(‖m_n‖_1)`.

**What it would unify.**  Commuting lamps are the abelian case (`A`
commutative: multiplicity = joint spectral rank); Clifford lamps are finite
Clifford algebras; Weyl/Heisenberg packets `XY = zeta YX` are twisted finite
group algebras; matrix-unit packets are full matrix summands.  One
mechanism: *compression forces an impossible change in the
finite-dimensional module type of a packet* — the commuting/anticommuting
distinction stops being fundamental, and the central sign `u^2 = -1`
becomes one small example.

**K_0 reading and a trap.**  The multiplicity vector is a positive
K_0-type invariant: a rank-one projection has normalized trace `1/d_n` but
rank `1`, which is what dimension-normalized trace forgets.  It is NOT the
naive compression index — notes/FALSE_KAZHDAN_COMPRESSION_INDEX_TO_PHASE.md
shows `ind(PUP)` vanishes identically because `P` and `UPU^*` are already
internally Murray--von Neumann equivalent.  A viable invariant must compare
genuinely distinct module sectors, which the multiplicity vector does.
`corner-renormalization-cost` is the reason ambient normalization cannot
work here and the defect must self-normalize;
`kazhdan-tensor-type-transport` supplies the transport of fixed tensors at
every type and weight, but the exactification and integrality steps are the
genuinely new analysis.
