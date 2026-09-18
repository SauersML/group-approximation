/* Monte Carlo on Cay(F2 x Z, S_rig): P(|C|>=n). Vertices: F2 word encoded via hash table of (parent index, letter, height). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint64_t s[2];
static inline uint64_t rotl(const uint64_t x,int k){return (x<<k)|(x>>(64-k));}
uint64_t nxt(void){uint64_t s0=s[0],s1=s[1],r=s0+s1;s1^=s0;s[0]=rotl(s0,55)^s1^(s1<<14);s[1]=rotl(s1,36);return r;}
double U(void){return (nxt()>>11)*(1.0/9007199254740992.0);}
/* tree nodes: id, parent id, last letter (0..3: a,A,b,B), children ids */
#define MAXT 4000000
int tpar[MAXT], tlet[MAXT], tch[MAXT][4]; int ntree;
int child(int t,int l){ /* move from tree node t by letter l */
  int inv = l^1;
  if(t && tlet[t]==inv) return tpar[t];
  if(tch[t][l]<0){ tpar[ntree]=t; tlet[ntree]=l; for(int k=0;k<4;k++) tch[ntree][k]=-1; tch[t][l]=ntree; ntree++; }
  return tch[t][l];
}
/* hash for vertices (tree,height) and edges */
#define HS (1<<24)
uint64_t *vkey; uint64_t *ekey; unsigned char *eval; uint32_t *vep,*eep; uint32_t EP=1;
uint64_t vk(int t,int h){return ((uint64_t)t<<32)|(uint32_t)(h+1000000);}
int vins(uint64_t k){uint64_t i=(k*0x9E3779B97F4A7C15ULL)>>40; while(vep[i]==EP){ if(vkey[i]==k) return 0; i=(i+1)&(HS-1);} vep[i]=EP; vkey[i]=k; return 1;}
int eget(uint64_t k,double p){uint64_t i=(k*0xC2B2AE3D27D4EB4FULL)>>40; while(eep[i]==EP){ if(ekey[i]==k) return eval[i]; i=(i+1)&(HS-1);} eep[i]=EP; ekey[i]=k; eval[i]=U()<p; return eval[i];}
int main(int argc,char**argv){
  double p=atof(argv[1]); int T=atoi(argv[2]); int N=atoi(argv[3]); s[0]=atoi(argv[4])*7919+1; s[1]=12345;
  int Da[3]={0,1,3}, Db[3]={0,1,4};
  int gl[14],gd[14]; int g=0;
  for(int i=0;i<3;i++){gl[g]=0;gd[g++]=Da[i]; gl[g]=1;gd[g++]=-Da[i];}
  for(int i=0;i<3;i++){gl[g]=2;gd[g++]=Db[i]; gl[g]=3;gd[g++]=-Db[i];}
  gl[g]=-1;gd[g++]=1; gl[g]=-1;gd[g++]=-1;
  vkey=calloc(HS,8); ekey=calloc(HS,8); eval=calloc(HS,1); vep=calloc(HS,4); eep=calloc(HS,4);
  int *st=malloc(sizeof(int)*2*(N+20));
  int cnt[8]={0}; int thr[8]; int nthr=0; for(int n=10;n<=N;n*=10) thr[nthr++]=n;
  for(int trial=0;trial<T;trial++){
    EP++; ntree=1; for(int k=0;k<4;k++) tch[0][k]=-1; tpar[0]=0; tlet[0]=-1;
    int sp=0, size=1; vins(vk(0,0)); st[sp++]=0; st[sp++]=0;
    while(sp && size<N){
      int h=st[--sp]; int t=st[--sp];
      for(int k=0;k<14;k++){
        int t2 = gl[k]<0 ? t : child(t,gl[k]); int h2=h+gd[k];
        uint64_t a=vk(t,h), b=vk(t2,h2); uint64_t lo=a<b?a:b, hi=a<b?b:a; uint64_t ek = lo*0x100000001B3ULL + (hi<<1) + (hi>>31);
        ek = ek ? ek : 1;
        if(eget(ek,p) && vins(b)){ size++; st[sp++]=t2; st[sp++]=h2; if(size>=N) break; }
        if(ntree>MAXT-10) {size=N;break;}
      }
    }
    for(int j=0;j<nthr;j++) if(size>=thr[j]) cnt[j]++;
  }
  printf("p=%g T=%d:",p,T); for(int j=0;j<nthr;j++) printf(" P(>=%d)=%.4f",thr[j],(double)cnt[j]/T); printf("\n");
}
