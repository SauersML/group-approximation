"""Certificate for the examples on X = {0,1,2} (permutations written as image tuples):
   t = (1, 1, t)(0 1 2)       ternary odometer: t(0w)=1w, t(1w)=2w, t(2w)=0 t(w)
   a = (a, t, t^-1)(1 2)      a(0w)=0 a(w), a(1w)=2 t(w), a(2w)=1 t^-1(w)
   b = (a, b, a)(0 2)         b(0w)=2 a(w), b(1w)=1 b(w), b(2w)=0 a(w)
G1 = <t, a> (activity degree 1) and G2 = <t, a, b> (activity degree 2).
Checks for each: (1) activity degrees of the minimized generating automaton; (2) a nucleus, i.e. the
contraction certificate; (3) the space of sum-invariant characters via the nucleus criterion;
(4) chi = t-exponent sum agrees with every relation among reduced words of length <= 16 (G1) or 10 (G2).
Run: python3 verify_example.py  (about a minute, well under 1GB)."""
from sumchar import *
from relsearch import relsearch
I=(0,1,2); R=(1,2,0); T12=(0,2,1); T02=(2,1,0); Rinv=(2,0,1)
base=[(I,(0,0,0)), (R,(0,0,1)), (T12,(2,1,3)), (Rinv,(3,0,0))]
for label, st, names, L, gens in [
        ('G1 = <t,a>', base, ['1','t','a','T'], 16, [1,2,3]),
        ('G2 = <t,a,b>', base+[(T02,(2,4,2))], ['1','t','a','T','b'], 10, [1,2,3,4])]:
    print('=====', label)
    A=fix_inverses(Automaton(3,st,names=list(names)))
    nm=lambda w:''.join(A.names[s] for s in w) or '1'
    deg,rep=activity_degree(A)
    print('activity degrees of minimized nontrivial states:',sorted(deg.values()))
    B,nms,N,U=sum_invariant_characters(A)
    U.refine()
    print('nucleus size',len(N))
    for c,w in sorted(N.items(),key=lambda kv:(len(kv[1]),kv[1])):
        p,ks=A.act(w)
        kn=[]
        for k in ks:
            kc=U.cls[U.id[A.reduce(k)]]
            kn.append(nm(N[kc]) if kc in N else '?'+nm(k))
        print('  ',nm(w),'= (',', '.join(kn),')',p)
    print('dimension of sum-invariant characters:',len(B))
    for x in B:
        vals={nm(nms[j]):x[j] for j in range(len(x))}
        s=vals.get('t')
        print('  normalized chi on nucleus:',{k:str(v/s) for k,v in vals.items()})
    print('inverses (state -> inverse state):',{A.names[s]:A.names[A.inv[s]] for s in gens})
    chi={s:0 for s in range(A.nstates)}
    chi[1]=1; chi[A.inv[1]]=-1
    n,k,bad=relsearch(A,gens,chi,L,maxwords=3000000)
    print('relation check up to length',L,': words',n,'elements',k,
          'relations violating t-exponent sum:',len(bad))
