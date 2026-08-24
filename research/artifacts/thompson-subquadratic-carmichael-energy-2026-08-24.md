# Subquadratic Carmichael energy collapse — ingestion and audit (2026-08-24)

Source: user-supplied research note, "Subquadratic Carmichael energy collapse",
delivered inline together with a status report on the Thompson-`V`,
Leavitt/Steinberg, affine-Leavitt and signed-Hecke lanes.  The note's own
sandbox path (`/mnt/data/thompson-subquadratic-carmichael-energy-collapse.md`)
was not reachable from this session; the full text was pasted into the request
and is reproduced in substance below.  Nothing here is transcribed from a
journal article.

The note is explicit that it does **not** claim an unconditional
non-hyperlinear group, and that the existence of one is still open.  This
audit agrees, and it keeps `non-hyperlinear-group` open.

## 1. What the note contains

1. A collapse theorem: if `B in U(d)` admits arbitrarily large packets of
   unitary conjugates `X_1,...,X_M` whose **total squared Carmichael edge
   energy** `E_M = sum_(i<j) ||(X_iX_j)^2 - I||_2^2` is `o(M^2)`, then
   `||B-I||_2 <= ||B^3-I||_2`.
2. A corollary for Thompson `V` at the Bleak--Quick mark `b=(01 10 11)`:
   since `b^3=1` is a relator, `||U(b)^3-I||_2 <= C_b def_R(U)`, so the
   theorem forces `||U(b)-I||_2 <= C_b def_R(U)`, contradicting the regular
   character of a hyperlinear microstate sequence.
3. An identification of the remaining open lemma ("R5 square-function
   lemma") and a proposed `ell^2` Hodge/square-function shape for its proof,
   `e = T_M f + D^* q` with `||T_M||_(2->2) = O(sqrt M)`, giving the stronger
   sufficient bound `E_M <= C M def_R(U)^2`.
4. Status calls on the other lanes: the 2026 Leavitt non-sofic constructions
   do not by themselves give non-hyperlinearity; the affine-Leavitt route's
   spectral-carrier decoder is still open; the signed-Hecke route still needs
   its additive holonomy identity; the note recommends spending the next unit
   of effort on the Thompson square-function lemma instead.

Two external pointers accompanied the note (an EMS Press *Groups, Geometry and
Dynamics* 20 (2026) article recording non-hyperlinearity as open, and Zenodo
record 21840947 on Kaplansky direct finiteness for the first non-sofic group).
Neither was fetched or verified in this session, so **no citation node was
created from them**; they are recorded here as unverified pointers only.  The
graph's existing position — non-hyperlinearity open, the first non-sofic group
being the Leavitt unit group — is unchanged and needs no import.

## 2. The theorem, re-derived

Re-derived independently, step by step, before wiring.  It is correct.

Fix `r>0`.  The conjugacy orbit `O(B)={WBW^*}` is compact in normalized
Hilbert--Schmidt distance, so it has a finite cover by `N=N(d,B,r)` balls of
radius `r`.  Distributing `X_1,...,X_M` into cells with populations `m_a`,
Cauchy--Schwarz gives

```text
S_M = sum_a C(m_a,2) = (1/2)(sum_a m_a^2 - M) >= M^2/(2N) - M/2,
```

positive once `M>N`.  The same-cell pairs carry at most the total energy, so
some same-cell pair `(i,j)` has `e_(ij)^2 <= E_M/S_M`, and for it
`||X_i-X_j||_2 <= 2r`.

The engine is then a two-matrix inequality that needs no packet at all.  For
any `A,C in U(d)` that are unitary conjugates of `B`:

```text
A - I = A(I-A^3) + (A^4-I),                                   (E1)
(AC)^2 - A^4 = A(C-A)AC + A^3(C-A),                           (E2)
```

both verified by expanding.  Unitary invariance of `||.||_2` turns these into

```text
||B-I||_2 <= ||B^3-I||_2 + 2||A-C||_2 + ||(AC)^2-I||_2.       (CP)
```

Applying `(CP)` to the same-cell pair gives, for every `r>0` and every `M>N`,

```text
||B-I||_2 <= ||B^3-I||_2 + sqrt(E_M/S_M) + 4r.                (EFF)
```

If `E_M=o(M^2)` then `E_M/S_M -> 0` for each fixed `r` (`N` is fixed once `r`
and the model are fixed), and letting `r` decrease to `0` afterwards gives the
theorem.

**Where the dimension goes.** `N(d,B,r)` depends on `d`, but `M` tends to
infinity with `d` held fixed, so `N` never competes with anything.  This is
the note's own observation and it is right: there is no dimension-versus-defect
packing-rate problem.

## 3. Audit findings

### (a) The theorem is genuinely new here, and `(CP)` is its reusable kernel

`bounded-area-high-chromatic-conjugacy-collapse-proof` already performs the
`(E1)`/`(E2)` computation inline, but it obtains its close pair from an
`eta`-net colouring of a graph of unbounded chromatic number and then spends a
**uniform per-edge area certificate** on the one monochromatic edge.  The new
argument obtains its close pair by **counting energy against the number of
same-cell pairs**, so no per-edge certificate exists or is needed.  That is a
different mechanism, and it is the content worth landing.

### (b) The note's "materially weaker" framing does not survive

The note states that the subquadratic criterion is weaker than the repository's
uniform criterion and proposes replacing `thompson-v-r5-coherent-carmichael-family`
with it.  That is wrong in the aggregate direction, and the two criteria are in
fact **incomparable**:

* Uniform does not imply subquadratic.  `(CCF)` supplies only
  `e_(ij) <= C def_R(U)`, so `E_M <= C^2 def_R(U)^2 M(M-1)/2` — quadratic in
  `M` whenever the defect is positive, never `o(M^2)`.  The extreme instance
  is explicit: `d=3`, `B` the cyclic permutation matrix, `X_i=B` for all `i`.
  Then `X_i^3=I` exactly and `(X_iX_j)^2=B^4=B`, so every edge defect equals
  `||B-I||_2=sqrt2` uniformly, while `E_M=M(M-1)`.
* Subquadratic does not imply uniform.  Take `d=4`, `B` the 4-cycle
  permutation matrix (`B^4=I`), `W` the transposition matrix of `(1 2)`, and
  set `X_i=B` off a sparse set `S_M` with `|S_M|=ceil(sqrt M)` and
  `X_i=WBW^*` on it.  Bulk and within-`S_M` pairs give `(X_iX_j)^2=B^4=I`
  exactly; only the `<= M^(3/2)` mixed pairs are bad, each with
  `e_(ij)^2=3/2`, so `E_M=O(M^(3/2))=o(M^2)` while individual edges stay
  bounded away from `0` at a defect-free model.

Both criteria are sufficient for the collapse; neither dominates.  So the
uniform target must be **kept**, not replaced.  This is recorded as its own
established claim so a later session does not retire a live lane on the note's
framing.

### (c) The order-three mark is load-bearing, and the bound is sharp

For an involution `B^2=I` one has `B^3=B`, so the conclusion
`||B-I||_2 <= ||B^3-I||_2` is a tautology.  The theorem therefore says nothing
about involution marks — which is exactly why it is not refuted by
`affine-clone-model-defeats-pure-thompson-prefix-error-spreading`, whose mark
`e_empty` is an involution.  For `B^4=I` one has `B^3=B^*` and hence equality
`||B-I||_2 = ||B^3-I||_2`, so the inequality is attained and cannot be
improved to a strict one.  The sparse packet of (b) realizes that case with
`E_M=o(M^2)`, so the theorem cannot be strengthened to force `B=I` without the
cube relator.

### (d) The remaining lemma is, as far as anyone can show, strictly stronger
than the endpoint it feeds

Write `(ACE)` for the R5 subquadratic-energy property.  `(ACE)` implies
`thompson-v-one-word-strict-hs-ceiling` `(TV2)` by the theorem.  The converse
does not follow: `(TV2)` gives `||B-I||_2 <= C delta`, and the constant packet
then has `E_M <= 8C^2 delta^2 M^2`, which is `O(M^2)` and not `o(M^2)`.  So
`(ACE)` is not a weakening of the endpoint — it demands genuine cancellation
at a **fixed** model with a **fixed positive** defect, not merely a small
defect.  That is the load-bearing difficulty and it is recorded in the open
node's attempts rather than hidden.

The same point read positively: `(ACE)` is not a restatement of `(TV2)`
either.  It names an object `(TV2)` does not mention — an unbounded packet
inside one fixed `U(d)` — and it can fail while `(TV2)` holds.  It is a real
reduction, just not an easier-looking one.

### (e) The firewalls that do and do not apply

* `finite-mark-centralizer-commutator-area-is-proper` (and its averaged form
  `(FMC3)`) bound **filling area**, not matrix defect.  A large-area word can
  still have small normalized-HS defect, so neither the individual nor the
  averaged area divergence obstructs `(ACE)`.  The note is right about this.
  Note this was already the graph's stated position for the uniform target
  too, so it is not a new escape.
* `collective-centralizer-cycles-are-free-gauge-identities` remains the sharp
  constraint on the proposed Hodge shape: the free gauge part `D^* q` is
  exactly the component that telescopes to nothing.  A square-function proof
  must control the **common mode**, which cycle identities cannot see.  The
  note identifies this correctly as the missing ingredient.
* `orthogonal-centralizer-channels-retain-area-properness` says that merely
  putting the endpoint corrections into fixed orthogonal channels does not
  bound their area.  It does not obstruct an `ell^2` estimate on the combined
  edge errors, which is what the square-function target asks for.
* `literal-one-cell-carmichael-cliques-are-uniformly-finite` obstructs a fixed
  finite template list of edge words.  A square-function bound assigns no edge
  word template at all, so it is untouched.
* `affine-clone-model-defeats-pure-thompson-prefix-error-spreading` supports
  arbitrarily large **exact** Carmichael stars, but only inside finite affine
  subgroups whose regular representations have dimension growing with the star
  size.  `(ACE)` fixes `d` first, so the countermodel does not apply — and by
  (c) the model's own mark is an involution, on which the theorem is vacuous.

## 4. What was wired

* `subquadratic-carmichael-energy-collapse` (established) and its proof route.
* `carmichael-energy-uniform-criteria-incomparable` (established) and its
  proof route — finding (b), plus (c).
* `r5-subquadratic-carmichael-energy` (open) — the note's remaining lemma,
  with finding (d) and the firewall audit of (e) in its attempts.
* `carmichael-edge-hodge-operator-has-root-m-norm` (open) — the square-function
  target `E_M <= C M def_R(U)^2`, and its route into the previous node.
* `thompson-v-one-word-ceiling-from-subquadratic-energy` — the route from the
  new pair into the existing one-word ceiling, which the existing
  `nonhyperlinear-thompson-v-from-one-word-ceiling` already carries to the
  program goal.

Deliberately **not** wired: any retirement or demotion of
`thompson-v-r5-coherent-carmichael-family` (finding (b)); any citation node
built on the two unverified external pointers; any status change to the
Leavitt/Steinberg, affine-Leavitt or signed-Hecke lanes, whose open nodes
already say what the note says about them.
