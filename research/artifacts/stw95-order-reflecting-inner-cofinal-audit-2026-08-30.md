# STW Problem XCV: order-reflecting inner-cofinal Cu audit (2026-08-30)

## Existing graph and corrected threshold

The XCV proof graph was searched before adding this theorem.  The canonical
external map

```text
theta:Cu(A) tensor_Cu Cu(B) -> Cu(A tensor_min B)
```

is known to be an isomorphism when one factor is AF, and a Cu-morphism right
inverse is already known to suffice for purity.  The first version of this
node claimed that order reflection plus inner cofinality allowed concrete
classes outside the image.  A second audit found that this is impossible:
the two assumptions diagonalize to surjectivity.

Two one-axiom nodes were already present.  Inner cofinality of the image for
way-below pairs transfers almost divisibility.  An additive order-preserving
right inverse transfers almost unperforation.  The corrected result identifies
the exact threshold: inner cofinality alone is useful and local, but together
with order reflection it is equivalent to the external map being a
Cu-isomorphism.

## Diagonal surjectivity audit

Fix `x=sup x_n` with `(x_n)` rapidly increasing.  Inner cofinality first
places `x_1` below `theta(b_1)<<theta(c_1)<=x`.  Recursively,
`theta(b_(n-1))` and `x_n` are both way below `x`, so a single `z_n<<x`
dominates them.  A new inner bracket gives

```text
x_n,theta(b_(n-1))<=z_n<=theta(b_n)<<theta(c_n)<=x.
```

Order reflection yields `b_(n-1)<=b_n`.  For `b=sup b_n`, preservation of
suprema gives `x<=theta(b)<=x`, proving surjectivity.  No addition or purity
axiom is used in this abstract step.  Surjective order-embedding Cu-morphisms
are Cu-isomorphisms, and the converse inner-cofinal statement follows by
applying the inverse to `x'<<x`.

## Boundary

The theorem does not claim that the canonical map always reflects order or
has an inner-cofinal image.  It shows instead that these conditions cannot be
used to accommodate the extra compact cross classes already seen in XCV:
they force every concrete class into the image.  The general pure-tensor
permanence root remains open, and a genuinely nonsurjective proof must weaken
one of the two hypotheses.
