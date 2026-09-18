# Independent completeness check of the backtracking enumerator for degree (3,3): test all 9! bijections
# A x B -> B x A for Klein-orbit closure and compare the count with vh_enum.enumerate_data.
import itertools, sys
from vh_enum import enumerate_data, valid, inv_arr
for pA, pB in ((0, 0), (1, 0), (1, 1)):
    iA, iB = inv_arr(3, pA), inv_arr(3, pB)
    corners = [(h, v) for h in range(3) for v in range(3)]
    targets = [(v, h) for v in range(3) for h in range(3)]
    brute = sum(1 for p in itertools.permutations(targets) if valid(dict(zip(corners, p)), 3, 3, iA, iB))
    bt = len(enumerate_data(3, pA, 3, pB)[2])
    print(f"(3,{pA})x(3,{pB}) brute={brute} backtrack={bt}"); assert brute == bt
