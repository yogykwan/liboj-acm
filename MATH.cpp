///////////////////////////////////Math Library by YogyKwan
#include<cstdio>
#include<cmath>
#include<cstring>
#include<iostream>
#include<ctime>
#include<cstdlib>
#include<algorithm>
#include<queue>
#pragma comment(linker, "/STACK:36777216")
using namespace std;
typedef long long LL;
const double inf=1e9;
const double eps=1e-8;
const double pi=acos(-1.0);
const int maxn=110;
const int mod=1000000007;
const LL base=100000000LL;

struct BINT{
	LL s[maxn];
	int l;
	void input(LL t){
		l=-1;
		memset(s,0,sizeof(s));
		do{
			s[++l]=t%base;
			t/=base;
		}while(t);
	}
	void output(){
		printf("%lld",s[l]);
		for(int i=l-1;i>=0;--i) printf("%08lld",s[i]);
	}
    friend BINT operator +(BINT a,BINT b){
        LL d=0;
        a.l=max(a.l,b.l);
        for(int i=0;i<=a.l;++i){
            a.s[i]+=b.s[i]+d;
            d=a.s[i]/base;
            a.s[i]%=base;
        }
        if(d) a.s[++a.l]=d;
        return a;
    }
    friend BINT operator -(BINT a,BINT b){
        LL d=0;
        for(int i=0;i<=a.l;++i){
            a.s[i]-=d;
            if(a.s[i]<b.s[i]) a.s[i]+=base,d=1;
            else d=0;
            a.s[i]-=b.s[i];
        }
        while(a.l && !a.s[a.l]) --a.l;
        return a;
    }
    friend BINT operator *(BINT a,int b){
        LL d=0;
        for(int i=0;i<=a.l;++i){
            a.s[i]=(a.s[i]*b)+d;
            d=a.s[i]/base;
            a.s[i]%=base;
        }
        while(d){
            a.s[++a.l]=d%base;
            d/=base;
        }
        return a;
    }
    friend BINT operator /(BINT a,int b){
        LL d=0;
        for(int i=a.l;i>=0;--i){
            a.s[i]+=d*base;
            d=a.s[i]%b;
            a.s[i]/=b;
        }
        while(a.l && !a.s[a.l]) --a.l;
        return a;
    }
    friend BINT operator *(BINT a,BINT b){
        BINT c;
        memset(c.s,0,sizeof(c.s));
        for(int i=0;i<=a.l;++i){
            for(int j=0;j<=b.l;++j){
                c.s[i+j]+=a.s[i]*b.s[j];
                if(c.s[i+j]>base){
                    c.s[i+j+1]+=c.s[i+j]/base;
                    c.s[i+j]%=base;
                }
            }
        }
        c.l=a.l+b.l+10;
        while(c.l && !c.s[c.l]) --c.l;
        while(c.s[c.l]>base){
            c.s[c.l+1]+=c.s[c.l]/base;
            c.s[c.l++]%=base;
        }
        return a;
    }
};

struct MillerRabin_PollarRho{
    LL factor[30];
    int alpha[30],cntf;
    LL mul(LL a, LL b, LL p){
        LL rn=0, i;
        for(i=1; i<=b; i<<=1,a=(a+a)%p)
        if(b&i) rn=(rn+a)%p;
        return rn;
    }
    LL ksm(LL a, LL b, LL p){
        LL rn=1;
        for(; b; a=mul(a,a,p),b>>=1)
        if(b&1) rn=mul(rn,a,p);
        return rn;
    }
    LL gcd(LL a, LL b) {
        LL tmp; if(a<b) tmp=a,a=b,b=tmp;
        while(b) tmp=a%b, a=b, b=tmp;
        return a;
    }
    bool isprime(LL n){
        int i,S=10;
        if(n==2) return true;
        if(n<2 || !(n&1)) return false;
        LL a,x,y, u=n-1; int t=0;
        while((u&1)==0) t++, u>>=1;
        for(i=0; i<S; i++){
            a=rand()%(n-1)+1;
            x=ksm(a,u,n);
            for(int j=1; j<=t; j++){
                y=mul(x,x,n);
                if(y==1 && x!=1 && x!=n-1) return false;
                x=y;
            }
            if(x!=1) return false;
        }
        return true;
    }
    void rho(LL n){
        if(isprime(n)) { factor[cntf++]=n; return; }
        LL x,y,z,c,d; int i,j;
        while(1){
            x=rand()*rand()%(n-1)+1,
            c=rand()*rand()%(n-1)+1;
            for(y=x,i=j=2; ; i++){
                x=(mul(x,x,n)+c)%n;
                z=x-y; if(z<0) z=-z;
                d=gcd(z,n);
                if(d>1 && d<n) { rho(d); rho(n/d); return; }
                if(x==y) break;
                if(i==j) y=x,j<<=1;
            }
        }
    }
    void get_factor(LL n){
        if(n==1){
            cntf=0;
            return;
        }
        int i,tot=0;
        cntf=0;
        rho(n);
        sort(factor,factor+cntf);
        tot=1;alpha[0]=1;
        for(i=1;i<cntf;++i){
            if(factor[i]==factor[i-1]) ++alpha[tot-1];
            else{
                factor[tot]=factor[i];
                alpha[tot++]=1;
            }
        }
        cntf=tot;
    }
};

struct EulerSieve{
    int prime[maxn>>2],cntp;
    bool np[maxn+10];
    int euler[maxn];
    int inv[maxn];
    int mobius[maxn];
    int power(int a,int b){
        int ans=1;
        while(b){
            if(b&1) ans*=a;
            a*=a;
            b>>=1;
        }
        return ans;
    }
    void Euler_Sieve(){
        euler[1]=1;
        inv[1]=1;
        mobius[1]=1;
        int i,j;
        LL temp;
        for(i=2;i<=maxn;++i){
            if(!np[i]){
                prime[cntp++]=i;
                euler[i]=i-1;
                inv[i]=power(i,mod-2);
                mobius[i]=-1;
            }
            for(j=0;j<cntp && (temp=i*prime[j])<=maxn;++j){
                np[temp]=1;
                if(i%prime[j]){
                    euler[temp]=euler[i]*(prime[j]-1);
                    inv[temp]=inv[i]*inv[prime[j]];
                    mobius[temp]=-mobius[i];
                }else{
                    euler[temp]=euler[i]*prime[j];
                    inv[temp]=inv[i]*inv[prime[j]];
                    mobius[temp]=0;
                    break;
                }
            }
        }
    }
    void get_inv(){
        inv[1]=1;
        for(int i=2;i<=maxn;++i){
            inv[i]=(1LL*(mod/i)*inv[mod%i])%mod;
            inv[i]=(1LL*inv[i]*inv[i])%mod;
            inv[i]=(1LL*inv[i]*i)%mod;
        }
    }
};

struct Gauss_Elimination{
    int gcd(int a,int b){
        for(int t;t=b;b=a%b,a=t);
        return a;
    }
    int lcm(int a,int b){
        return a/gcd(a,b)*b;
    }
    int Gauss (int coe[][maxn],int equ,int var,int *x,int p,int *inv){
        int i, j, mr, row, col;
        int ta, tb, l, tmp;
        row = col = 0;
        while ( row < equ && col < var ){
            mr = row;
            for ( i = row + 1; i < equ; i++ ) if ( abs(coe[i][col]) > abs(coe[mr][col]) ) mr = i;
            if ( mr != row ) for ( j = col; j <= var; j++ ) swap ( coe[row][j], coe[mr][j] );
            if (!coe[row][col]){
                col++;
                continue;
            }
            for ( i = row + 1; i < equ; i++ ){
                if (coe[i][col]){
                    l = lcm(abs(coe[i][col]), abs(coe[row][col]));
                    ta = l / abs(coe[i][col]), tb = l / abs(coe[row][col]);
                    if ( coe[i][col] * coe[row][col] < 0 ) tb = -tb;
                    for ( j = col; j <= var; j++ )
                        coe[i][j] = ((coe[i][j]*ta-coe[row][j]*tb)%mod+mod) % mod;
                }
            }
            row++; col++;
        }
        for ( i = row; i < equ; i++ ) if(coe[i][var]) return -1;
        if (row<var) return var-row;
        for ( i = var - 1; i >= 0; i-- ){
            tmp = coe[i][var];
            for ( j = i + 1; j < var; j++ ) tmp = ((tmp-coe[i][j]*x[j])%mod+mod)%mod;
            x[i] = ( tmp *inv[coe[i][i]]) % mod;
        }
        return 0;
    }
};

struct HighPrecision_FFT{
    struct complex{
        double r,i;
        complex(double real=0.0,double image=0.0){
            r=real;	i=image;
        }
        // 以下为三种虚数运算的定义
        complex operator + (const complex o){
            return complex(r+o.r,i+o.i);
        }
        complex operator - (const complex o){
            return complex(r-o.r,i-o.i);
        }
        complex operator * (const complex o){
            return complex(r*o.r-i*o.i,r*o.i+i*o.r);
        }
    }x1[maxn],x2[maxn];
    char a[maxn>>1],b[maxn>>1];
    int sum[maxn]; // 结果存在sum里
    void brc(complex *y,int l) // 二进制平摊反转置换 O(logn)
    {
        register int i,j,k;
        for(i=1,j=l/2;i<l-1;i++)
        {
            if(i<j)	swap(y[i],y[j]); // 交换互为下标反转的元素
                                    // i<j保证只交换一次
            k=l/2;
            while(j>=k) // 由最高位检索，遇1变0，遇0变1，跳出
            {
                j-=k;
                k/=2;
            }
            if(j<k)	j+=k;
        }
    }
    void fft(complex *y,int l,double on) // FFT O(nlogn) // 其中on==1时为DFT，on==-1为IDFT
    {
        register int h,i,j,k;
        complex u,t;
        brc(y,l); // 调用反转置换
        for(h=2;h<=l;h<<=1) // 控制层数
        {
            // 初始化单位复根
            complex wn(cos(on*2*pi/h),sin(on*2*pi/h));
            for(j=0;j<l;j+=h) // 控制起始下标
            {
                complex w(1,0); // 初始化螺旋因子
                for(k=j;k<j+h/2;k++) // 配对
                {
                    u=y[k];
                    t=w*y[k+h/2];
                    y[k]=u+t;
                    y[k+h/2]=u-t;
                    w=w*wn; // 更新螺旋因子
                } // 据说上面的操作叫蝴蝶操作…
            }
        }
        if(on==-1)	for(i=0;i<l;i++)	y[i].r/=l; // IDFT
    }
    void print_a_mul_b(){
        int l1,l2,l;
        register int i;
        while(scanf("%s%s",a,b)!=EOF)
        {
            l1=strlen(a);
            l2=strlen(b);
            l=1;
            while(l<l1*2 || l<l2*2)	l<<=1; // 将次数界变成2^n
                                            // 配合二分与反转置换
            for(i=0;i<l1;i++) // 倒置存入
            {
                x1[i].r=a[l1-i-1]-'0';
                x1[i].i=0.0;
            }
            for(;i<l;i++)	x1[i].r=x1[i].i=0.0;
            // 将多余次数界初始化为0
            for(i=0;i<l2;i++)
            {
                x2[i].r=b[l2-i-1]-'0';
                x2[i].i=0.0;
            }
            for(;i<l;i++)	x2[i].r=x2[i].i=0.0;
            fft(x1,l,1); // DFT(a)
            fft(x2,l,1); // DFT(b)
            for(i=0;i<l;i++)	x1[i]=x1[i]*x2[i]; // 点乘结果存入a
            fft(x1,l,-1); // IDFT(a*b)
            for(i=0;i<l;i++)	sum[i]=x1[i].r+0.5; // 四舍五入
            for(i=0;i<l;i++) // 进位
            {
                sum[i+1]+=sum[i]/10;
                sum[i]%=10;
            }
            l=l1+l2-1;
            while(sum[l]<=0 && l>0)	l--; // 检索最高位
            for(i=l;i>=0;i--)	putchar(sum[i]+'0'); // 倒序输出
            putchar('\n');
        }
    }
};

struct Catlan_Number{
    BINT h[maxn];
    void Catlan(){
        h[1].input(1LL),h[2].input(1LL);
        for(int i=3;i<maxn;++i){
            h[i]=h[i-1]*(4*i-6)/i;
        }
    }
    BINT com[maxn<<1][maxn<<1];
    void Com(){
        int i,j;
        for(int i=1;i<(maxn<<1);++i){
            int j;
            com[i][0].input(1LL);
            for(j=1;j<=(i>>1);++j) com[i][j]=com[i-1][j-1]+com[i-1][j];
            for(;j<=i;++j) com[i][j]=com[i][i-j];
        }
    }
    BINT Catlan(int n){
        BINT a;
        if(n<=2) a.input(1LL);
        else a=com[2*n-2][n-1]/n;
        return a;
    }
};
///////////////////////////////////Math Library by YogyKwan

int main(){
}
