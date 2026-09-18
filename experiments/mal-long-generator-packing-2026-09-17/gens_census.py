"""Census: words t with <H, t> = F(a,b), H = <a, b_{m-d}>; which double cosets H t H occur."""
import sys
from fg import Subgroup, reduced_words
from packing import w_stage

d, L = int(sys.argv[1]), int(sys.argv[2])
H = Subgroup(["a", w_stage(d)])
tot = out = 0
examples = []
for t in reduced_words(L):
    if H.generates_F2_with(t):
        tot += 1
        if not (H.in_double_coset("b", t) or H.in_double_coset("B", t)):
            out += 1
            if len(examples) < 20:
                examples.append(t)
print(f"d={d} L={L} w={w_stage(d)} generators={tot} outside Hb^+-1H={out}")
print(examples)
