# To add a new cell, type '# %%'
# To add a new markdown cell, type '# %% [markdown]'
# %% [markdown]
# # Defining the field $\mathbb{F}_q$ and the polynomial ring $\mathbb{F}_q[T]$
# %% [markdown]
# Define base field:

# %%
# Define base field by prime power:
import sys

q = Integer(sys.argv[1])

# %% [markdown]
# Calculate the field $F_q$:
# 
# ($g$ is a generator of the multiplicative group of $F_q$)

# %%
Fq = GF(q,'g')
g = Fq.gen()

# %% [markdown]
# Define the polynomial rings $\mathbb{F}_q[T]$, $\mathbb{F}_q[T,X]$, and $\mathbb{F}_q[T][X]$:

# %%
FqT.<T> = Fq[]
FFqT.<T> = FunctionField(Fq)
FqTX.<T,X> = Fq[]
FFqT_X.<X> = FFqT[]
sep_TX = FqTX.hom([T,X],FFqT_X)

# %% [markdown]
# # Helper Functions
# %% [markdown]
# ## Polynomial algebra and number theory
# %% [markdown]
# ### Factors of a polynomial

# %%
def prime_factors(p):
    return set(pr for pr,n in list(p.factor()))

def cross_multiply(l):
    if len(l) == 0:
        return set(1)
    else:
        return set(p*q for p in l[0] for q in cross_multiply(l[1:]))

def all_factors(p):
    list_of_powers = [set(pr^i for i in range(n+1)) for pr,n in list(p.factor())]
    return cross_multiply(list_of_powers)

def is_monicList(l):
    for p in l:
        if p != 0:
            return p.is_monic()
    return False

# %% [markdown]
# ### Euler $\varphi$ function

# %%
from functools import reduce

def qNorm(p):
    return q^p.degree()

def product(iterable):
    return reduce(operator.mul, iterable, 1)

def EulerPhi(n, p):
    pfs = prime_factors(p)
    pf_norms = [qNorm(pf) for pf in pfs]
    return qNorm(p)^n * product(1-pfn^(-n) for pfn in pf_norms)

# %% [markdown]
# ### Extended gcd of a list of polynomials

# %%
def my_xgcd(l):
    if len(l) < 2:
        raise ValueError
    elif len(l) == 2:
        return l[0].xgcd(l[1])
    else: # len(l) > 2
        xgcd_rest = my_xgcd(l[1:])
        pgcd = l[0].xgcd(xgcd_rest[0])
        # + here is tuple concatenation:
        return pgcd[:2] + tuple(pgcd[2]*xgcd_rest[i] for i in range(1,len(l)))

# %% [markdown]
# ### List of polynomials modulo a polynomial

# %%
@cached_function

def numsMod_deg(n):
    if n == 0:
        return [0]
    elif n > 0:
        highMonos = [c*FqT(T)^(n-1) for c in Fq]
        return [hm+num for hm in highMonos for num in numsMod_deg(n-1)]
    else:
        raise ValueError

def numsMod(p):
    p = FqT(p)
    return numsMod_deg(p.degree())

# numsMod(T^2+T)

# %% [markdown]
# ### Lists of pairs modulo a polynomial

# %%
@cached_function

def pairsMod_deg(n):
    nums = numsMod_deg(n)
    return [(n1,n2) for n1 in nums for n2 in nums]

def pairsMod(p):
    p = FqT(p)
    return pairsMod_deg(p.degree())

def nonzeroPairs_deg(n):
    return [(n1,n2) for n1,n2 in pairsMod_deg(n) if (n1,n2) != (0,0)]

def nonzeroPairs(p):
    p = FqT(p)
    return nonzeroPairs_deg(p.degree())

@cached_function

def monicPairs_deg(n):
    return [pair for pair in nonzeroPairs_deg(n) if is_monicList(pair)]

def monicPairs(p):
    p = FqT(p)
    return monicPairs_deg(p.degree())

# %% [markdown]
# ### Lists of cusps

# %%
@cached_function

def cusps(p):
  p = FqT(p)
  return [(p1,p2) for p1,p2 in monicPairs(p) if p.gcd(p1).gcd(p2) == 1]
    
@cached_function

def biCusps(p):
  p = FqT(p)
  cc = cusps(p)
  xgcd_coeffs = [my_xgcd(c+(p,))[1:] for c in cc]
  # return [(c,(-x[1],x[0])) for c,x in zip(cc,xgcd_coeffs)]
  return [((c[0],-x[1]),(c[1],x[0])) for c,x in zip(cc,xgcd_coeffs)]

# biCusps(T^2)

# %% [markdown]
# ### List of pairs congruent to another pair modulo a divisor of a polynomial

# %%
# list of all pairs mod `p` which are congruent to the pair `r` modulo `m`,
# where `m` is a divisor of `p`

def pairsCongruentMod(r, m, p):
  m, p = FqT(m), FqT(p)
  if p % m != 0: raise ValueError
  n = FqT(p/m)
  return [(m*t1+r[0], m*t2+r[1]) for t1,t2 in pairsMod(n)]

# pairsCongruentMod((1,0), T, T^2+T)

# %% [markdown]
# ## Reduction of list of Eisenstein pairs using known relations

# %%
import itertools

def reducedTwoPairs(p):
  p = FqT(p)
  # list of (indices of) Eisenstein series of weight 1
  nnzPairs = nonzeroPairs(p)
  # list of products of two Eisenstein series of weight 1
  nnzTwoPairs = list(itertools.product(nnzPairs,repeat=2))
  
  # passing between products of two Eisenstein series and columns
  to_idx_dict = dict(zip(nnzTwoPairs,range(len(nnzTwoPairs))))
  to_twoPair_dict = dict(zip(range(len(nnzTwoPairs)),nnzTwoPairs))
  
  # constants
  zero, one = FqT.zero(), FqT.one()
  
  # dict-form of matrix of relations
  matrix_dict = {}
  r = 0
  def add_row(d): # `d` is a dict mapping twoPairs to matrix entries
    nonlocal r
    for k,v in d.items():
      matrix_dict[(r,to_idx_dict[k])] = v
    r += 1
  
  # scaling of left and right elements of product
  for l in Fq:
    if l != zero and l != one:
      for p1,p2 in nnzTwoPairs:
        lp1 = (l*p1[0], l*p1[1]) # l * p1
        add_row({(lp1,p2): l, (p1,p2): -one})
  # print(r+1, "scaling relations")
  
  # swapping of elements of products of distinct elements
  for p1,p2 in itertools.combinations(nnzPairs,2):
    add_row({(p1,p2): one, (p2,p1): -one})
  # print(r+1, "with swapping relations")
  
  # relations arising from additivity of e_Lambda(z)
  for pa,pb in nnzTwoPairs:
    pab = (pa[0]+pb[0], pa[1]+pb[1]) # pa + pb
    if pab == (zero, zero): continue

    if pa == pb:
      add_row({(pa,pb): one, (pab,pb): -one-one})
    else:
      add_row({(pa,pb): one, (pab,pb): -one, (pab,pa): -one})
  # print(r+1, "with adding relations")
  
  # linear relations arising from factorisation of `p`
  for m in prime_factors(p):
    n = FqT(p/m)
    for s in nonzeroPairs(n):
      for k in nnzPairs:
        d = {}
        for t in pairsCongruentMod(s, n, p):
          d[(t,k)] = one
      
        ms = (m*s[0],m*s[1]) # m * s
        if (ms,k) in d.keys():
          d[(ms,k)] = d[(ms,k)] - m
        else:
          d[(ms,k)] = -m
      
        add_row(d)
  # print(r+1, "with linear factor relations")
  
  # square quadratic relations arising from factorisation of `p`
  for m in prime_factors(p):
    n = FqT(p/m)
    for s in nonzeroPairs(n):
      d = {}
      for t in pairsCongruentMod(s, n, p):
        d[(t,t)] = one
      
      ms = (m*s[0],m*s[1]) # m * s
      if (ms,ms) in d.keys():
        d[(ms,ms)] = d[(ms,ms)] - m^2
      else:
        d[(ms,ms)] = -m^2
      
      add_row(d)

  # other quadratic relations arising from factorisation of `p`, for `q = 2`
  if q == 2:
    for m in prime_factors(p):
      n = FqT(p/m)
      for s in nonzeroPairs(n):
        d = {}
        for t1,t2 in itertools.combinations(pairsCongruentMod(s, n, p), 2):
          d[(t1,t2)] = one
        
        ms = (m*s[0],m*s[1]) # m * s
        for u in nonzeroPairs(m):
          nu = (n*u[0],n*u[1]) # n * u
          if (ms,nu) in d.keys():
            d[(ms,nu)] = d[(ms,nu)] - m
          else:
            d[(ms,nu)] = -m
        
        add_row(d)
  
  nrows, ncols = r+1, len(nnzTwoPairs)
  # print("Matrix of relations dimensions:", nrows, ncols)
  mat = matrix(FFqT, nrows, ncols, matrix_dict, sparse=True)
  # those which are not pivot columns of the echelonised form:
  # print("Calculating nonpivots:")
  non_pivots = mat.nonpivots()
  non_pivot_twoPairs = [to_twoPair_dict[col] for col in non_pivots]
  return non_pivot_twoPairs

# reducedTwoPairs(T^2)

# %% [markdown]
# ## Drinfeld module functions
# %% [markdown]
# ### Frobenius endomorphism and ring of skew polynomials:

# %%
frob = FqTX.hom([FqTX(T)^q,FqTX(X)^q])
frob
SkewTX.<tau> = FqTX['tau',frob]
# SkewTX
# phiaT = T +T*tau +tau^2; phiaT(T)

# %% [markdown]
# ### $\varphi^{\pi A}_p(x)$ for a polynomial $p \in \mathbb{F}_q[T]$, output in $\mathbb{F}_q(T)[X]$:

# %%
phi_hom = FqT.hom([T+tau],SkewTX)

@cached_function

def phiA(p):
    return sep_TX(phi_hom(FqT(p)).operator_eval(X))

# (phiA(T^2+T)/phiA(T+1)/phiA(T)*phiA(1))(1/X).parent()

# %% [markdown]
# ### Most primitive factor of $\varphi_p^{\pi A}(x)$, output in $\mathbb{F}_q(T)[X]$:

# %%
@cached_function

def primPhiA(p):
    p = FqT(p)
    primes = list(prime_factors(p))
    return FFqT_X(phiA_inclExcl_div(p,primes))

def phiA_inclExcl_div(p,l):
    if len(l) == 0:
        return phiA(p)
    else:
        first, rest = l[0], l[1:]
        num = phiA_inclExcl_div(p,rest)
        denom = phiA_inclExcl_div(p/first,rest)
        return num / denom

# primPhiA(T^2+T) == phiA(T^2+T) / phiA(T+1) / phiA(T) * phiA(1)
# primPhiA(T^2+T).parent()

# %% [markdown]
# ### $\pi e_A \left(\frac{r}{N}\right) = e_{\pi a} \left(\frac{\pi r}{N}\right)$

# %%
@cached_function

def FqT_adj(N):
    # ext = FFqT_X.quotient(primPhiA(N), 'e1')
    why.<e> = FFqT[]
    poly = primPhiA(N)(e)
    ext.<e> = FFqT.extension(poly)
    return ext, e

# FqT_N, e = FqT_adj(T^2+T); FqT_N


# %%
@cached_function

def eA(r,N):
    ext, e1 = FqT_adj(N)
    return phiA(r % N)(e1)


# eA(T^3+T^2-T, T^2+T)
# eA(T^3+T^2-T, T^2+T).parent()

# %% [markdown]
# ## Expansions of Eisenstein series
# %% [markdown]
# ### Integrality factor

# %%
@cached_function

def int_factor(N):
    return FqT(N).radical()

# int_factor(T^2+T).parent()

# %% [markdown]
# ### Expansion of an Eisenstein series at $\infty$

# %%
# X-expansion of an Eisenstein series at infinity to order 'omax',
# exclusive; currently only works if omax < |N|
# 1 / (eA(r2,N) + phiA(r1,1/X))
@cached_function

def E2SeriesInfinity(r,N):
    r1,r2 = r
    r1 %= N; r2 %= N
    deg, lc = r1.degree(), r1.lc()

    radical = int_factor(N)
    omax = qNorm(N)

    if deg == -1: # r1 == 0 mod N
        return radical / eA(r2,N)
    else:
        frac = 1 -X^(q^deg) * (eA(r2,N)+phiA(r1)(1/X)) / lc
        # return from fraction field to polynomial ring
        fracfield = frac.parent()
        sect = fracfield.coerce_map_from(fracfield.ring()).section()
        frac = sect(frac)
        imax = omax - q^deg
        inexp = 0
        for i in range(imax+1):
            inexp += frac^i
        return radical * X^(q^deg) * inexp / lc +O(X^omax)

# E2SeriesInfinity((T,T+1), T^2), E2SeriesInfinity((T,1), T^2)
# E2SeriesInfinity((1,T), T^2).parent()

# %% [markdown]
# ### Series expansion of a product of Eisenstein series at a cusp

# %%
@cached_function

def E2Series(r,biCusp,N):
    ((a,b),(c,d)) = biCusp
    R = [((a*r1+c*r2) % N, (b*r1+d*r2) % N) for r1,r2 in r]
    p = product(E2SeriesInfinity(rbc,N) for rbc in R) +O(X^qNorm(N))
    return p
    # return (R,p)

def E2Series_list(r,biCusp,N,deg):
    if deg > qNorm(N):
        print (deg, qNorm(N))
        raise ValueError(f"series expansion to {deg} > {qNorm(N)} terms requested`")

    series = E2Series(r,biCusp,N)
    l = series.list()
    if len(l) >= deg:
        return l[:deg]
    else: # len(l) < deg
        return l +[0]*(deg-len(l))

# E2Series([(1,0),(T,2),(2,T+1)], ((0,1),(-1,0)), T^2+T)
# E2Series_list(((1,0),(T,2),(2,T+1)), ((0,1),(-1,0)), T^2+T, 15)

# %% [markdown]
# ### Coefficients of a product of Eisenstein series at all cusps, flattened and ordered by the exponent of the parameter at $\infty$

# %%
def E2SeriesAllCusps(r, N, cutoff):
    bcs = biCusps(N)
    # cutoff for the expansion at each cusp
    cusp_cut = ceil(cutoff/len(bcs))
    # dict of series expansions at each cusp
    all = {bc:E2Series_list(r,bc,N,cusp_cut) for bc in bcs}
    # flatten lists of coefficients and order by index/exponent
    out = [all[bc][i] for bc in bcs for i in range(cusp_cut)][:cutoff]
    return out

# %% [markdown]
# # Rank function

# %%
import os
import time
import datetime
import pickle
import pprint
# import smtplib

def printTemp(*args):
    print("\r", *args, end='')

def stats(N):
    start = time.time()

    N = FqT(N)
    printTemp("Beginning calculation of statistics for", N)

    printTemp("Forming set of Eisenstein pairs")
    redTwoPairs = reducedTwoPairs(N)

    printTemp("Calculating t-expansions of Eisenstein pairs")
    cutoff = 2 * qNorm(N) * EulerPhi(2,N) / (q^2-1)
    cuts = [E2SeriesAllCusps(r, N, cutoff) for r in redTwoPairs]
    printTemp("Creating final matrix of coefficients")
    mat = matrix(cuts)
    r, c = mat.nrows(), mat.ncols()
    printTemp(f"Matrix has dimensions {r}×{c}")

    rank2 = qNorm(N) * EulerPhi(2,N) / (q^2-1) + EulerPhi(2,N) / (q-1)
    printTemp(f"Rank of all weight 2 modular forms is {rank2}\n")

    printTemp("Calculating rank of the matrix of coefficients,",
              f"with {mat.nrows()} rows and {mat.ncols()} columns")
    E2rank = mat.rank()
    printTemp(f"Rank of matrix is {E2rank}\n")

    n_nnz = sum(map(
        lambda row: sum(map(lambda entry: entry != 0, row)),
        mat
    ))
    n_mat = mat.nrows() * mat.ncols()

    end = time.time()


    return {
        "q": q,
        "N": N,
        "N, factored": N.factor(),
        "number of cusps": len(biCusps(N)),
        "finalMatrix": mat,
        "number of nonzero entries": n_nnz,
        "fraction of nonzero entries": n_nnz / n_mat,
        "rank": E2rank,
        "full rank of weight 2 D-modular forms": rank2,
        "time taken": str(datetime.timedelta(seconds=end-start))
    }

def send_and_save(N, pw=""):
    out = stats(N)

    # # Send mail from Python
    # # sending mail from inside Sage won't work on the HPC
    # server = smtplib.SMTP("smtp.office365.com", 587r)
    # server.ehlo()
    # server.starttls()
    # server.login("liambaker@sun.ac.za", pw)
    # server.sendmail(
    #     from_addr="liambaker@sun.ac.za", to_addrs="liambaker@sun.ac.za",
    #     msg=f"Subject: Results for q = {q} and N = {N}\n\n{pprint.pprint(out,width=10)}"
    # )
    # server.quit()

    # set working directory to script location
    abspath = os.path.abspath(__file__)
    dname = os.path.dirname(abspath)
    os.chdir(dname)

    # save output to text file to be picked up by Linux `mail` program
    with open(f"results/q = {q}, N = {N}.txt", 'w') as file:
        pprint.pprint(out, width=10, stream=file)
    
    # pickle output
    with open(f"results/q = {q}, N = {N}.pickle", 'wb') as file:
        pickle.dump(out, file)

# iterate over all polynomials of a requested degree
def iterate_deg(deg, pw=""):
    for pre_N in numsMod_deg(deg):
        N = T^deg +pre_N
        send_and_save(N, pw)

# get requested degree from command line and iterate
Ndeg = Integer(sys.argv[2])
iterate_deg(Ndeg)

# %% [markdown]
# # Exotic Relations

# %%
import time
import datetime

def printTemp(*args):
    print("\r", *args, end='')

def exoticRelations(N):
    start = time.time()

    N = FqT(N)
    printTemp(f"Beginning calculation of statistics for {N}")

    printTemp("Forming set of Eisenstein pairs")
    redTwoPairs = reducedTwoPairs(N)

    printTemp("Calculating t-expansions of Eisenstein pairs")
    cutoff = 2 * qNorm(N) * EulerPhi(2,N) / (q^2-1)
    cuts = [E2SeriesAllCusps(r, N, cutoff) for r in redTwoPairs]
    printTemp("Creating final matrix of coefficients")
    mat = matrix(cuts)
    r, c = mat.nrows(), mat.ncols()
    printTemp(f"Matrix has dimensions {r}×{c}")

    printTemp("Finding exotic relations between products",
              "of two Eisenstein series")
    rel_coeffs = mat.kernel().basis()
    print(f"\r{len(rel_coeffs)} relations:")
    ind_R2P = {i:r for i,r in enumerate(redTwoPairs)}
    rel_strings = [
        f"{ri+1}: 0 = " + " + ".join(
            f"({c!s}) * E2[{ind_R2P[i][0]!s}] * E2[{ind_R2P[i][1]!s}]"
            for i,c in enumerate(coeff_list) if c != 0
        ) for ri, coeff_list in enumerate(rel_coeffs)
    ]
    for eqn in rel_strings: print(eqn)
    # rank of products of two Eisenstein series
    E2rank = mat.nrows() - len(rel_coeffs)

    n_nnz = sum(map(
        lambda row: sum(map(lambda entry: entry != 0, row)),
        mat
    ))
    n_mat = mat.nrows() * mat.ncols()

    end = time.time()


    return {
        "q": q,
        "N": N,
        "N, factored": N.factor(),
        "number of cusps": len(biCusps(N)),
        "redTwoPairs": redTwoPairs,
        "finalMatrix": mat,
        "number of nonzero entries": n_nnz,
        "fraction of nonzero entries": n_nnz / n_mat,
        "rank": E2rank,
        "time taken": str(datetime.timedelta(seconds=end-start))
    }
