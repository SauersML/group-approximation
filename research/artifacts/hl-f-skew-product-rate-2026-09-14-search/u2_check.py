# u2 = C * (a^2 R2 a^-2)(a R1^-1 a^-1)(a^2 R1^-1 a^-2): verify both Fox derivatives vanish in Z[Z^2]
# (so the closed walk of u2 in the grid Cayley graph of Z^2 has zero 1-chain, i.e. u2 lies in F2''),
# and evaluate u2 on certificate pairs (last letter acts first).
import importlib.util, sys
spec=importlib.util.spec_from_file_location('fox','fox.py'); fox=importlib.util.module_from_spec(spec)
sys.argv=['x']; 
src=open('fox.py').read().split("R1='bAABaaBAba'")[0]; exec(src)
R1='bAABaaBAba'; R2='bAAABaaaBAAbaa'; C='abAB'
def invw(w): return ''.join(ch.swapcase() for ch in reversed(w))
def red(w):
    st=[]
    for ch in w:
        if st and st[-1]==ch.swapcase(): st.pop()
        else: st.append(ch)
    return ''.join(st)
P='aa'+R1+'AA'+'a'+R1+'A'+'aa'+invw(R2)+'AA'
u2=red(C+invw(P))
print('u2 =',u2,len(u2))
print('d u2/da =',fox(u2,'a'),' d u2/db =',fox(u2,'b'))
print('C == u2 * P freely:', red(u2+P)==red(C))
def inv(Pm):
    Q=[0]*len(Pm)
    for i,x in enumerate(Pm): Q[x]=i
    return Q
def word(wd,A,B):
    M={'a':A,'A':inv(A),'b':B,'B':inv(B)}; cur=list(range(len(A)))
    for ch in reversed(wd):
        Pm=M[ch]; cur=[Pm[x] for x in cur]
    return cur
def moved(Pm): return sum(1 for i,x in enumerate(Pm) if i!=x)
certs={'x12':([1,2,3,0,5,6,7,4,9,8,11,10],[4,5,8,9,1,0,10,2,3,11,7,6]),
 's10':([1,2,3,4,0,6,7,8,9,5],[3,4,5,1,7,8,9,0,6,2]),
 'x16':([0,4,6,8,9,1,12,2,13,11,7,5,14,3,10,15],[0,5,7,2,11,9,13,3,6,1,14,15,10,8,12,4]),
 'torus3xZ2':([7,6,8,9,10,11,12,13,14,15,16,17,0,1,2,3,4,5],[2,3,5,4,1,0,8,9,10,11,7,6,14,15,16,17,12,13]),
 'Z2wrZ5':([2,3,4,5,6,7,8,9,0,1],[6,7,8,9,1,0,2,3,5,4])}
for k,(A,B) in certs.items():
    m1,m2,mc,mu=moved(word(R1,A,B)),moved(word(R2,A,B)),moved(word(C,A,B)),moved(word(u2,A,B))
    print(k,'m1',m1,'m2',m2,'mc',mc,'2m1+m2',2*m1+m2,'moved(u2)',mu)
