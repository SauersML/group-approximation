# Renormalization stable letter: audited construction record

Date: 2026-08-20

## Verdict

The stable-letter pivot contains two useful exact transport calculations and
correctly identifies why a finite character-table contraction cannot finish
the hyperlinear problem.  It does **not** yet define an injective endomorphism
of the Thompson--Clifford base, and its proposed invariant-state-emptiness
endpoint is impossible.

The corrected decomposition is:

1. finite-core contraction is fenced by
   `finite-packet-cannot-realize-absorbing-contraction` and
   `fixed-depth-rank-mesh-has-zero-hs-density`;
2. the two abelian polynomial examples are exact and replayable;
3. a pure abelian ascending HNN extension is amenable and therefore cannot be
   the desired group;
4. the twisted Clifford map must still pass a presentation-level injective
   endomorphism audit; and
5. even if it passes, soundness cannot be proved by emptiness of invariant
   marked traces.  A tensor-stable finite-dimensional obstruction would still
   be needed.

## 1. The finite-core fence survives

The proposed Fence I is already present in stronger usable form.  If one
fixed finite packet forced a positive floor, a strict depth-`m` contraction,
and a bounded terminal quantity in every negative-sign representation, its
negative regular summand would give a zero-defect contradiction.  Meanwhile,
integer rank granularity at fixed depth is only `O(1/d)` and disappears under
tensor amplification.

This does justify moving the search toward relations involving an
infinite-order element.  It does not prove that every successful construction
must literally be an ascending HNN extension.

## 2. Exact abelian transport witnesses

Let `S` be the bilateral shift.  Over `Z/4Z`,

```text
(2I+S)^2=4I+4S+S^2=S^2.
```

Thus ghost-corrected doubling secretly becomes a pure shift after two steps.

On the discrete direct sum over `F_2`, `I+S` is injective.  Its Pontryagin
dual on the full shift is the cellular map

```text
y_i=x_i+x_(i-1).
```

It is surjective and has the two constant configurations as kernel.  Given a
target, one freely chooses one seed and recursively obtains the two lifts.
`experiments/renormalization_transport_audit.py` replays these identities.

The safe general conclusion is scoped.  For an abelian group `A` and an
injective endomorphism, the pure ascending HNN extension is the semidirect
product of the abelian direct-limit telescope by `Z`; hence it is metabelian,
amenable, and hyperlinear.  Pontryagin duality by itself does not prove the
broader claim that arbitrary nonamenable controllers attached to an abelian
core always admit the particular finite microstates demanded by a proposed
soundness theorem.

## 3. The twisted Clifford formula is not yet an endomorphism

The proposed substitution was written schematically as

```text
t u_k t^(-1)=v_k u_(2k+1)u_(2k).
```

An ascending HNN argument requires an injective endomorphism of a completely
specified base group.  The schematic formula omits data that already decide
whether it respects generator squares.  If three factors `a,b,c` pairwise
anticommute by `J` and `a^2=J^s_a`, etc., then

```text
(abc)^2=J^(s_a+s_b+s_c+3)=J^(s_a+s_b+s_c+1).
```

So three involutions square to `J`, whereas three factors each squaring to
`J` have product square `1`.  Neither uniform convention maps a generator to
a word with the same square.  A mixed fresh-cell convention may fix the
parity, but all pairwise commutators must then be checked.

There is a second, independent global obligation.  Transitivity of Thompson
`V` on sites does not automatically preserve binary parent-child incidence.
One must specify which tree-action relations normalize the substitution,
show that transported definitions agree, and prove injectivity.  A proper
image in one finite-window algebra is not an injectivity proof for the group.

Accordingly, Britton's lemma has not yet established `J != 1` in the proposed
`G_subst`.  It will do so after the endomorphism and injectivity statements are
proved.

## 4. The invariant-state endpoint is impossible

The decisive correction is elementary and general.  Let `A` be a unital
C-star algebra, let `alpha` be a unital endomorphism, and suppose
`alpha(J)=J`.  Starting from any marked trace `tau(J)=-1`, form

```text
tau_N=(1/N) sum_(k=0)^(N-1) tau after alpha^k.
```

Every `tau_N` remains tracial and marked.  Weak-star compactness supplies a
cluster point, and

```text
|(tau_N after alpha)(a)-tau_N(a)| <= 2||a||/N,
```

so the limit is invariant.  For the CAR algebra the point is even sharper:
its trace is unique, hence is invariant under every unital endomorphism.

Therefore the question

```text
Does the twisted substitution admit any invariant sign-alive trace?
```

has answer **yes** whenever the substitution really is a sign-preserving
unital endomorphism and the sign sector initially has a trace.  An Arf or
Pfaffian charge cannot make this invariant trace face empty.

This does not prove that the eventual HNN group is hyperlinear.  It changes
the required theorem: soundness would have to be a genuinely
finite-dimensional, normalized-Hilbert--Schmidt obstruction that survives
tensor amplification while coexisting with the exact invariant trace.  That
is precisely the difficult gap separating non-Connes-embeddable traces from
non-hyperlinear groups.

## 5. Correct live program

The construction now has two honest gates.

### Gate N1: group-theoretic endomorphism

Give the full base presentation and substitution; verify squares,
commutators, acting-group equivariance, injectivity, properness, and finite
presentability of the ascending HNN extension.

### Gate N2': finite-dimensional anomaly, not trace emptiness

Find a fixed finite word window and a dimension-free inequality saying that
every sufficiently multiplicative finite-dimensional model with the mark
alive pays positive normalized HS energy.  The inequality must be stable
under `U -> U tensor I_k` and must not contradict the invariant marked trace
above.

Until both gates are passed, `G_subst` is a valuable candidate architecture,
not a non-hyperlinear group.

