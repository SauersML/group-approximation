# Regular-language iteration for the parity condition of the dual B = B332V.
# E = {d : #0(d) even};  I_{j+1} = I_j  cap  b0^{-1} I_j  cap  b1^{-1} I_j  cap  b2^{-1} I_j.
# The largest B-invariant subset of E (all lengths at once) is the intersection of the I_j.
# Each I_j is regular (B is a synchronous transducer); we minimise and watch for stabilisation.
import sys
from aut import AUT
out,sec=AUT[sys.argv[1] if len(sys.argv)>1 else '332V']; t=out[3]
Bo=[tuple(sec[d][x] for d in range(3)) for x in range(3)]
Bs=[tuple(t[out[d][x]] for d in range(3)) for x in range(3)]
X=range(3)
def minimize(D):
    # D=(start, delta dict q->(q0,q1,q2), accepting set); reachable part then Moore partition refinement
    s,dl,F=D
    reach={s}; todo=[s]
    while todo:
        q=todo.pop()
        for x in X:
            r=dl[q][x]
            if r not in reach: reach.add(r); todo.append(r)
    Q=sorted(reach,key=repr)
    cls={q:(q in F) for q in Q}
    while True:
        sig={q:(cls[q],)+tuple(cls[dl[q][x]] for x in X) for q in Q}
        ids={}; new={}
        for q in Q:
            new[q]=ids.setdefault(sig[q],len(ids))
        if len(set(new.values()))==len(set(cls.values())): cls=new; break
        cls=new
    n=len(set(cls.values()))
    ndl={}; 
    for q in Q: ndl[cls[q]]=tuple(cls[dl[q][x]] for x in X)
    nF={cls[q] for q in Q if q in F}
    return (cls[s],ndl,nF)
def inter(Ds):
    starts=tuple(D[0] for D in Ds)
    dl={}; todo=[starts]; seen={starts}
    while todo:
        q=todo.pop(); dl[q]=[]
        for x in X:
            r=tuple(D[1][qi][x] for D,qi in zip(Ds,q)); dl[q].append(r)
            if r not in seen: seen.add(r); todo.append(r)
    F={q for q in seen if all(qi in D[2] for D,qi in zip(Ds,q))}
    return (starts,dl,F)
def pre(b,D):
    s,dl,F=D; st=(b,s); ddl={}; todo=[st]; seen={st}
    while todo:
        c,q=todo.pop(); ddl[(c,q)]=[]
        for x in X:
            r=(Bs[c][x], dl[q][Bo[c][x]]); ddl[(c,q)].append(r)
            if r not in seen: seen.add(r); todo.append(r)
    return (st,ddl,{p for p in seen if p[1] in F})
def canon(D):
    # canonical form via BFS numbering from start
    s,dl,F=D; num={s:0}; order=[s]; i=0
    while i<len(order):
        q=order[i]; i+=1
        for x in X:
            r=dl[q][x]
            if r not in num: num[r]=len(order); order.append(r)
    return tuple((tuple(num[dl[q][x]] for x in X), q in F) for q in order)
def nonempty_lengths(D,nmax):
    # which lengths 1..nmax have a word in the language
    s,dl,F=D; cur={s}; res=[]
    for n in range(1,nmax+1):
        cur={dl[q][x] for q in cur for x in X}
        res.append(any(q in F for q in cur))
    return res
E=(0,{0:(1,0,0),1:(0,1,1)},{0})
I=minimize(E); hist=[canon(I)]
for j in range(1,200):
    for b in range(3):
        I=minimize(inter([I,pre(b,I)]))
        if len(I[1])>60000: break
    c=canon(I)
    print('j',j,'states',len(c),'nonempty lengths 1..12:',''.join('1' if z else '0' for z in nonempty_lengths(I,12)),flush=True)
    if c==hist[-1]: print('STABLE at j',j); break
    hist.append(c)
    if len(c)>200000: print('too big'); break
