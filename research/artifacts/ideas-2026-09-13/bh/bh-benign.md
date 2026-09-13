# Idea lane bh-benign (2026-09-13)

Target: `boone-higman-conjecture`. Lens: Higman's benign subgroups and the
internal logic of Higman's embedding theorem. This is an ideas file. No
claim is established by it, and no Cairn node is edited.

## Sources checked for this file

- **Benign subgroups.** Mikaelian, arXiv:2002.09728 (text extracted locally), §2.5:
  "a subgroup H of a finitely generated group G is called a benign subgroup in G,
  if G can be embedded in a finitely presented group K with a finitely generated
  subgroup L ≤ K such that G ∩ L = H".
- **Higman's characterization, as recalled there (§3.2).** "a set B is recursively
  enumerable in E if and only if A_B is benign in F_3", built step by step by the
  Higman operations. The final "Higman Rope Trick" embeds the group "using a free
  product with amalgamation and a HNN-extension".
- **Belk–Bleak–Matucci–Zaremsky, arXiv:2306.16356v3** (text extracted locally):
  - Theorem 3.6: "A finitely generated group has solvable word problem if and
    only if embeds into a computably presented simple group".
  - Corollary 3.7: "... if and only if it embeds into a simple subgroup of a
    finitely presented group".
  - Theorem 3.8 (Thompson): the finitely generated refinement.
  - Proposition 3.2, as used in the proof of 3.6: computably presented simple
    groups have solvable word problem.
  - The trick relation G′ = ⟨G, x, t | (v v^x)^t = v^x w⟩.
  - "(10) CAT(0) groups" in their list of open classes.
- **Solvable subgroup theorem** (Wikipedia, "CAT(k) group", verbatim): "any solvable
  subgroup of G is finitely generated and virtually free abelian".
- **Repo nodes:**
  - `boone-higman-conjecture`: Attempts 6–7 and "A strictly easier subproblem".
  - `decidable-groups-embed-in-decidable-edge-towers` (OPEN), with its Attempts.
  - `bh-embeddability-survives-decidable-edge-hnn` (OPEN).
  - `bh-embeddability-forces-decidable-edge-membership`.
  - `fa-subgroups-of-graph-towers-lie-in-base-pieces`.
  - `complexity-bounded-host-classes-are-not-universal`.
  - `boone-higman-thompson-simple-envelope`.

## A1. Benign kernels are decidable kernels; maximal kernels always exist at Δ₂

**Idea.** The root's normalized envelope Γ is finitely presented and contains a
finitely generated, computably presented simple S ⊇ G, and every proper normal
subgroup of Γ misses S. The conjecture asks for a maximal proper normal
M ⊲ Γ that is finitely normally generated. The benign relaxation asks only
that the preimage of M in a free group be benign, which by Higman's
characterization means recursively enumerable. Since S is simple, N ∩ S is 1
or S, so a normal subgroup N is proper iff s₀ ∉ N for one fixed nontrivial
s₀ ∈ S. Properness of ⟨⟨x₁,…,x_k⟩⟩ is therefore one non-membership question in
a normal closure of a finitely presented group, a Π₁ property. Zorn run with a
0′ oracle (keep a word x iff s₀ ∉ ⟨⟨M, x⟩⟩) then produces a Δ₂ maximal proper
normal M with Γ/M simple and containing G.

**Would prove.** Nothing new by itself. It pins the root's "strictly easier
subproblem" at a sharper level:
- M is r.e. ⇔ Γ/M is computably presented;
- by BBMZ Proposition 3.2, that holds ⇔ Γ/M has solvable word problem ⇔ M is recursive.

So a benign maximal kernel is the same as a decidable one, and a Δ₂ kernel
always exists.

**Kill test run.** Hand argument (simplicity of S, Proposition 3.2 checked in
the survey text).

**Verdict: killed as a route.** Recorded constraint: an r.e./benign maximal
kernel needs a way to build M together with a *positive* (Σ₁) certificate that
s₀ stays outside. The only available properness test is Π₁.

## A2. Kleene fixed-point envelope

**Idea.** Higman's embedding is uniform in an r.e. index, and Mikaelian
arXiv:2507.04347 makes it an explicit algorithm. Let f(e) be the index of the
finite presentation that Higman's construction outputs for the Boone–Higman
trick closure of the group presented by W_e. By Rogers's fixed-point form of the
recursion theorem there is e with W_e = W_{f(e)}. The group P = ⟨W_e⟩ is then
finitely presented, and it contains the simple trick closure of P, which contains P.

**Would prove.** If the fixed point forced P to *equal* its closure, P would be
a finitely presented simple group containing G.

**Kill test run.** At the fixed point one only gets an embedding cycle
P ↪ closure(P) ↪ P. Higman's output adds new letters, so the input is a proper
subgroup. Embedding cycles don't force isomorphism, let alone simplicity; for
example F₂ ↪ F₂ ∗ Z ↪ F₂.

**Verdict: killed.** Recursion theorems give set-level fixed points of
presentations, not group-level fixed points of constructions.

## A3. Decidably benign witnesses and a recursive Higman calculus

**Idea.** Call H ≤ F *decidably benign* if some benign witness (K, L) has K
finitely presented with solvable word problem and L with decidable membership
in K. The plan:
1. Characterize recursive sets B by Higman operations whose witnesses stay
   decidably benign.
2. Run the rope trick (amalgam plus HNN) with decidable edges.
3. Land in `boone-higman-via-decidable-edge-towers`, whose permanence premise
   `bh-embeddability-survives-decidable-edge-hnn` is OPEN.

**Would prove.** The tower premise
`decidable-groups-embed-in-decidable-edge-towers` from free bases, reducing
Boone–Higman to the single permanence claim.

**Kill test run.** `fa-subgroups-of-graph-towers-lie-in-base-pieces`: every
subgroup with property FA of an HNN/amalgam tower is conjugate into a base.
From free bases only trivial FA subgroups arise, so no free-base Higman
calculus reaches an infinite decidable Kazhdan input.
`decidable-groups-embed-in-decidable-edge-towers` Attempt 2 already records
this death for machine towers.

**Verdict: killed for FA inputs** (a relabelling of the recorded Attempt 2). For
non-FA inputs it survives only as a relabelling of the existing route.

**Residual question, unclear and low value.** Theorem 3 generates *all* r.e. sets
from Z and S. Recursive sets aren't closed under projection, so some Higman
operations must be existential in character, and a recursive-only calculus has
to replace them. Which operations these are, and whether their witnesses keep
decidable edge membership, wasn't checked.

## A4. Burger–Mozes-type simple amalgams as universal rope-trick containers

**Idea.** The rope trick's last step is an amalgam plus an HNN extension, and
Burger–Mozes groups are finitely presented simple amalgams (the survey cites
them as examples). Realize each rope-trick step inside a Burger–Mozes-type
simple lattice, so that simplicity comes from a normal-subgroup theorem
instead of relators.

**Kill test run.** Those lattices act properly and cocompactly on a product of
two trees, a CAT(0) space; this setting is standard and wasn't re-read. By the
solvable subgroup theorem (verbatim above), a CAT(0) group contains no solvable
subgroup that isn't virtually abelian. So BS(1,2), which is decidable, embeds
in no such host.

**Verdict: killed as universal hosts.** Recorded constraint: a universal host
class must escape CAT(0), in addition to the complexity wall of
`complexity-bounded-host-classes-are-not-universal`. BBMZ list CAT(0) groups
as an open *input* class; that is a different question.

## A5. A uniform Boone–Higman trick that certifies its own letters

**Idea.** The survey's trick G′ = ⟨G, x, t | (v v^x)^t = v^x w⟩ puts w in the
normal closure of v, at the cost of one new stable letter per pair (v, w).
- **Uniformize.** Replace the letters t_i by one rope-trick subgroup, or S-machine,
  that computes all pairs (v, w) from the decidable word problem, so finitely many
  letters implement every trigger.
- **Cover the machine too.** The machine's own letters are nontrivial elements, so
  the machine must certify words in its own letters as well: a quine, via the
  recursion theorem.

**Would prove.** A finitely presented group in which every nontrivial element
normally generates, that is, a finitely presented simple group containing G.

**Kill tests run.**
1. Hand fact: for any HNN extension K∗_φ, the quotient by ⟨⟨K⟩⟩ is ⟨t⟩ ≅ Z.
   Every stable letter lies outside the normal closure of its base, so the
   rope trick's HNN letter can never be absorbed by triggers on G alone.
   Triggers on the letters themselves are forced, which is where self-reference
   comes in.
2. Under self-reference, the trivial group satisfies every trigger equation. The
   recursion theorem gives a consistent program but no non-collapse. The usual
   non-collapse tool, Britton normal forms, breaks once triggers relate their
   own letters. This is the root's Attempt 6 obstacle: forcing normal generation
   endangers the base embedding.

**Verdict: unclear.** Firewall: a uniform trick needs a non-collapse invariant
that does *not* come from the trigger relators, for example an action of the
final group on a set where G acts faithfully, which survives adding triggers
on its own letters. First test: find any finitely presented group with
triggers on its own stable letters and a faithful G-action that visibly
survives the triggers.

## Summary of constraints from this lens

- Benignness is a finiteness notion for *membership* (G ∩ L = H with L finitely
  generated). Boone–Higman needs finiteness of *normal generation* of a maximal
  kernel. The benign calculus controls intersections with subgroups, never
  normal closures, so on its own it can't reach the simplicity half (A1, A5).
- Every stable letter of an HNN step maps onto Z modulo its base. Hence a
  rope-trick envelope can only become simple through triggers on its own letters,
  and any self-referential version must supply a non-collapse invariant from
  outside its relators (A5).
- Universal hosts must escape CAT(0) (A4) and bounded word-problem complexity
  (repo wall).
