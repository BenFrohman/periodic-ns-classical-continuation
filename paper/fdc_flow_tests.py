import numpy as np
N=48; L=2*np.pi; x=np.arange(N)*L/N
X,Y,Z=np.meshgrid(x,x,x,indexing='ij'); k=np.fft.fftfreq(N,1/N)
K=np.array(np.meshgrid(k,k,k,indexing='ij'))
def d(f,i): return np.real(np.fft.ifftn(1j*K[i]*np.fft.fftn(f)))
def analyze(name,u):
    G=np.array([[d(u[i],j) for j in range(3)] for i in range(3)])  # G[i,j]=du_i/dx_j
    S=0.5*(G+G.transpose(1,0,2,3,4))
    w=np.array([G[2,1]-G[1,2],G[0,2]-G[2,0],G[1,0]-G[0,1]])
    m=np.sqrt((w**2).sum(0)); M=m.max(); hi=m>=0.5*M
    t=w/np.maximum(m,1e-14)
    St=np.einsum('ij...,j...->i...',S,t); a=(t*St).sum(0)
    bend=St-a*t; b=np.sqrt((bend**2).sum(0))
    # B_F (local projected, F=enstrophy): dω += -κ|ω|^2 Π_u ω,  Π_u ω = ω - c u
    c=(u*w).sum()/(u*u).sum(); kap=1.5
    # contribution to Dτ/Dt = (I-ττ)(Δω)/|ω| = -κ|ω|^2 (-(c)(I-ττ)u)/|ω|
    uperp=u-(t*u).sum(0)*t
    contrib=kap*m*c*uperp
    proj=(contrib*bend).sum(0)   # sign of d/dt(|bend|) proxy: <B_F term, bend>
    # Lipschitz proxy of S tau on high set
    gx=np.sqrt(sum((d(St[i],j))**2 for i in range(3) for j in range(3)))
    print(f"{name:10s} |w|inf={M:7.3f} max|bend|hi={b[hi].max():.3e} max|bend|/|w| hi={(b[hi]/m[hi]).max():.3e} "
          f"helicity c={c:+.3e} <BF,bend>hi: min={proj[hi].min():+.2e} max={proj[hi].max():+.2e} |grad(S tau)|hi={gx[hi].max():.2e}")
A,B,C=1,0.8,0.6
analyze("ABC",np.array([A*np.sin(Z)+C*np.cos(Y),B*np.sin(X)+A*np.cos(Z),C*np.sin(Y)+B*np.cos(X)]))
analyze("2-mode",np.array([np.sin(Y)+0.5*np.sin(Z),0*X,0.3*np.sin(X)]))
# periodized Burgers vortex: Gaussian swirl + strain (strain non-periodic; use periodic proxy)
r2=(np.sin((X-np.pi)/2)*2)**2+(np.sin((Y-np.pi)/2)*2)**2; g=np.exp(-r2/0.5)
analyze("Burgers~",np.array([-(Y-np.pi)*g-0.5*np.sin(X),(X-np.pi)*g-0.5*np.sin(Y),np.sin(Z)]))
rng=np.random.default_rng(0)
for s in range(3):
    uh=(rng.normal(size=(3,N,N,N))+1j*rng.normal(size=(3,N,N,N)))*np.exp(-(K**2).sum(0)/8)
    kk=(K**2).sum(0); kk[0,0,0]=1; uh-=K*(K*uh).sum(0)/kk
    u=np.real(np.fft.ifftn(uh,axes=(1,2,3))); u/=np.abs(u).max()
    analyze(f"rand{s}",u)
