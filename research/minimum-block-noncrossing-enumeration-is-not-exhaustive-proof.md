---
rg: 2
id: minimum-block-noncrossing-enumeration-is-not-exhaustive-proof
kind: route
title: Exhibit a colored noncrossing partition outside every minimum branch
target: minimum-block-noncrossing-enumeration-is-not-exhaustive
requires:
  - leavitt-d4-l14-three-winner-boundary-needs-21-blocks
---

Consider the color word

```text
(0,1,0,2,1,2).
```

Its minimum number of monochromatic noncrossing blocks is four, attained for
example by

```text
{0,2}, {1}, {3,5}, {4}.
```

But

```text
{0}, {1,4}, {2}, {3}, {5}
```

is also a monochromatic noncrossing partition.  It refines no four-block
partition: merging either pair of equal-color singleton blocks crosses the
existing block `{1,4}`.  Hence a coefficient solution represented by this
five-block branch need not specialize any globally minimum-block branch.

The `schemes` routine used in the inverse `1;412` exploratory artifacts
retains only globally minimum block count.  Its output remains valid for the
branches it lists, but it is not a global certificate until the exact
29-, 31-, and boundary-color words receive a separate extension proof or an
all-maximal enumeration.  The same caution applies to the 21-block DP count
for the three-winner boundary.
