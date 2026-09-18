# dual transducer B of the automaton K=<V4,t>: states x in X, input d in {a0,a1,a2} (read right to left),
# output d|_x, next state t(out_d(x)).
import sys, itertools as it
from aut import AUT
nm=sys.argv[1]
out,sec=AUT[nm]; t=out[3]
B_out={x:tuple(sec[d][x] for d in range(3)) for x in range(3)}
B_sec={x:tuple(t[out[d][x]] for d in range(3)) for x in range(3)}
for x in range(3): print('b%d'%x,'out',B_out[x],'sec',B_sec[x])
def act(b,w):
    r=[]
    for d in w:
        r.append(B_out[b][d]); b=B_sec[b][d]
    return tuple(r)
for n in range(1,9):
    W=list(it.product(range(3),repeat=n))
    orb={W[0]}; todo=[W[0]]
    while todo:
        w=todo.pop()
        for b in range(3):
            u=act(b,w)
            if u not in orb: orb.add(u); todo.append(u)
    print(n,len(orb),3**n)
