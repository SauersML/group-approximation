# STW Problem XCV: order-reflecting inner-cofinal Cu audit (2026-08-30)

## Existing graph and new threshold

The XCV proof graph was searched before adding this theorem.  The canonical
external map

```text
theta:Cu(A) tensor_Cu Cu(B) -> Cu(A tensor_min B)
```

is known to be an isomorphism when one factor is AF, and a Cu-morphism right
inverse is already known to suffice for purity.  Neither fact is assumed
here.  A right inverse makes `theta` surjective; the new theorem explicitly
allows concrete Cuntz classes outside the external image.

Two one-axiom nodes were already present.  Inner cofinality of the image for
way-below pairs transfers almost divisibility.  An additive order-preserving
right inverse transfers almost unperforation.  The new result replaces that
global pullback map by order reflection on the source together with the same
local inner cofinality.  This is an asymmetric local-to-global theorem:
concrete elements stay in the concrete semigroup, while only compactly
contained comparison windows are routed through the external image.

## Cu proof audit

The nontrivial step starts from `(n+1)x<=n y` in the concrete semigroup and
tests it on `x_0<<x`.  Inner cofinality supplies
`x_0<=theta(a_0)<<theta(a)<=x`.  Hence
`(n+1)theta(a_0)<<n y`.  If `y=sup y_j` is rapidly increasing, addition and
supremum compatibility give `n y=sup n y_j`, so the inequality is captured
at one `y_j<<y`.  A second inner-cofinal bracket places that `y_j` below
`theta(b_0)` while keeping a larger image element below `y`.  Only now is
order reflection invoked:

```text
theta((n+1)a_0)<=theta(n b_0)
  implies (n+1)a_0<=n b_0.
```

Almost unperforation of the abstract Cu tensor product gives `a_0<=b_0`,
and the brackets return `x_0<=y`.  Taking the supremum over way-below pieces
of `x` finishes the comparison.  No decomposition of `x` or `y` into
elementary tensor classes is used.

## Boundary

The theorem is a sufficient condition, not a claim that the canonical map
always reflects order or has an inner-cofinal image.  In particular, the
external Cu map is not assumed surjective, and the extra compact cross
classes already seen in XCV are not discarded.  They are allowed if all
their way-below windows satisfy the stated bracketing condition.  The general
pure-tensor permanence root remains open.
