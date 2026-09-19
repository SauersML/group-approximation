from prof import *
n=600
for d in [0,1,2,3,5,8]:
    be,ga=150,100; al=n-be-ga
    print('theta=be+%d'%d, profile(arcx(n,be+d,al,be,ga),60,60))
