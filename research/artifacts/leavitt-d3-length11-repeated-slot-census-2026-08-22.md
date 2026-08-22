# Length-eleven repeated-slot census

The exact script
`research/artifacts/search-degree3-five-five-repeated.py` revisits the
degree-three `(1,5,5)` cyclic template after dropping the unnecessary
full-support/generating-packet condition.  Every free coefficient slot ranges
independently, with repetition, over

```text
{1,h,u,v,v^-1,a,b,c,d,r,p,e},
```

where `u=ab`, `v=cd`, `u^2=1`, `v^2=h`, and `h=[c,d] != 1` are evaluated in
the faithful twenty-leaf Bergman chart.  Equality of the common-carrier words
is evaluated in exact reduced normal form in the free product of three
coefficient copies.

Four symbolic branches were tested: source holonomy `u` against target
holonomy `v`; source `u` against `v^-1`; and both exhaustive normal-form
branches in which the source corner is the identity and the target corner is
`h`.  MSI array job `16665429` had 48 shards.  Every shard ended with
`tested 248832 hits 0`, for

```text
48 * 248832 = 11,943,936
```

exact replays and no hit.  This is a bounded-library fence, not an obstruction
for arbitrary Leavitt coefficient units.
