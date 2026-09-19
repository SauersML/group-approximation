import sys
sys.path.insert(0,'/home/user/group-approximation/experiments/h4-artin-complex-6cycles-2026-09-17')
from garside import Coxeter, Artin
MD={'H4':{(0,1):3,(1,2):3,(2,3):5},'A4':{(0,1):3,(1,2):3,(2,3):3},'B4':{(0,1):3,(1,2):3,(2,3):4}}
name=sys.argv[1] if len(sys.argv)>1 else 'H4'
W=Coxeter(4,MD[name]); G=Artin(W)
def inv(w): return [-g for g in reversed(w)]
def nf(w): return G.word(w)
def eq(x,y): return nf(x)==nf(y)
def com(x,y): return x+y+inv(x)+inv(y)
P3,P2,P1=[1,1],[1,2,2,-1],[1,2,3,3,-2,-1]
a=P2+P3; b=P1+P3
c=[4,4]; d=[-3,4,4,3]; w=[2,3,4,4,-3,-2]
print('b = s3^-1 a s3 :',eq(b,[-3]+a+[3]))
print('[c,a]=1',eq(com(c,a),[]),' [d,b]=1',eq(com(d,b),[]),' [w,b^-1 a]=1',eq(com(w,inv(b)+a),[]))
print('[c,b]!=1',not eq(com(c,b),[]),' [d,a]!=1',not eq(com(d,a),[]),' [w,a]!=1',not eq(com(w,a),[]))
u=w+c; v=w+d; k=com(u,a)
print('[u,a]=[v,b]',eq(k,com(v,b)),' k!=1',not eq(k,[]),' [u,b]!=k',not eq(com(u,b),k),' [v,a]!=k',not eq(com(v,a),k))
