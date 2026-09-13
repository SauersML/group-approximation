# Driver (lane ex2-radu-superstrong-negative, 2026-09-13): run radu-second-tree-check.py with its part 2
# replaced by radu-h4-star-check-part2.py. Needs, in the working directory: radu-pgl2-core.py,
# radu-quaternion-invariants-check.py, radu-quaternion-order-normalizer-check.py, radu-second-tree-check.py
# (all in research/artifacts/). Run: /usr/bin/python3.11 radu-h4-star-check.py
# Checks that C = <a,b,c> fixes the S_3-vertex p of the second tree T' and computes its action on the star of p.
src = open("radu-second-tree-check.py").read()
old = 'exec(open("radu-second-tree-part2.py").read())'
assert old in src
exec(src.replace(old, 'exec(open("radu-h4-star-check-part2.py").read())'))
