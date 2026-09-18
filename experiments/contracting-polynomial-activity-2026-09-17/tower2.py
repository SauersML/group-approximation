"""Family on X={0,1,2}: a_0=t=(1,1,t)(0 1 2); a_1=(a_1,t,t^-1)(1 2);
for j>=2, a_j fixes letter f_j=(j-1) mod 3 with section a_j there, swaps the other two letters,
and has section a_{j-1} at both of them.  Checks degree, nucleus, sum-invariant characters of <t,a_1..a_n>."""
from sumchar import *
import sys
I=(0,1,2); R=(1,2,0); Rinv=(2,0,1)
trans={0:(0,2,1),1:(2,1,0),2:(1,0,2)}
NMAX=int(sys.argv[1])
for n in range(1,NMAX+1):
    st=[(I,(0,0,0)),(R,(0,0,1)),(trans[0],(2,1,3)),(Rinv,(3,0,0))]  # 0:1 1:t 2:a_1 3:T
    idx={1:2}
    for j in range(2,n+1):
        f=(j-1)%3; ch=[idx[j-1]]*3; ch[f]=len(st)
        idx[j]=len(st); st.append((trans[f],tuple(ch)))
    A=fix_inverses(Automaton(3,st,names=['1','t','a1','T']+['a%d'%j for j in range(2,n+1)]))
    deg,_=activity_degree(A)
    try:
        B,nms,N,U=sum_invariant_characters(A)
    except (ValueError,MemoryError,RecursionError) as e:
        print('n',n,'max degree',max(deg.values()),'no nucleus',flush=True); continue
    nm=lambda w:''.join(A.names[s] for s in w)
    print('n',n,'max degree',max(deg.values()),'nucleus',len(N),'dim',len(B),
          [{nm(nms[j]):str(x[j]) for j in range(len(x)) if len(nms[j])==1} for x in B],flush=True)
