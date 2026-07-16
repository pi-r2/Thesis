
snova_params = [
#(v,o,q,l,"name")
(37,17,16,2, "Ia"),
(25,8,16,3,  "Ib"),
(24,5,16,4,  "Ic"),

(56,25,16,2, "IIIa"),
(49,11,16,3, "IIIb"),
(37,8,16,4, "IIIc"),

(75,33,16,2, "Va"),
(66,15,16,3, "Vb"),
(60,10,16,4, "Vc"),
]


VOXparams =[(251,8,9,6,6,"I"),
(251,4,5,13,6,"Ia"),
(251,5,6,11,6,"Ib"),
(251,6,7,9,6,"Ic"),
(1021, 10, 11, 7, 7,"III"),
(1021, 5, 6, 15, 7,"IIIa"),
(1021, 6, 7, 13, 7,"IIIb"),
(1021, 7, 8, 11, 7,"IIIc"),
(4093, 12, 13, 8, 8,"V"),
(4093, 6, 7, 17, 8,"Va"),
(4093, 7, 8, 14, 8,"Vb"),
(4093, 8, 9, 13, 8,"Vc")
]


mrVOXparams =[
(251,4,7,13,6,"Ia"),
(251,5,9,11,6,"Ib"),
(251,6,11,9,6,"Ic"),

(1021, 5, 9, 15, 7,"IIIa"),
(1021, 6, 11, 13, 7,"IIIb"),
(1021, 7, 13, 11, 7,"IIIc"),

(4093, 6, 11, 17, 8,"Va"),
(4093, 7, 13, 14, 8,"Vb"),
(4093, 8, 15, 13, 8,"Vc")
]


UOVparams = [
["Is", 16, 160, 64],
["Ip", 256, 112, 44],
["III", 256, 184, 72],
["V", 256, 244, 96]
]



#QRUOV

#(q,v,m,l)
#I
QRIa = (7, 740, 100, 10, "Ia")
QRIb = (31, 165, 60, 3, "Ib")
QRIc = (31, 600, 70, 10, "Ic")
QRId = (127, 156, 54, 3, "Id")
#III
QRIIIa = (7,1100, 140, 10, "IIIa")
QRIIIb = (31, 246, 87, 3, "IIIb")
QRIIIc = (31, 890, 100, 10, "IIIc")
QRIIId = (127, 228, 78, 3, "IIId")
#V
QRVa = (7, 1490, 190, 10, "Va")
QRVb = (31, 324, 114, 3, "Vb")
QRVc = (31, 1120, 120, 10, "Vc")
QRVd = (127, 306, 105, 3, "Vd")

QRparams = ( QRIa, QRIb, QRIc, QRId,  
          QRIIIa, QRIIIb, QRIIIc, QRIIId,
           QRVa, QRVb, QRVc, QRVd
          )

hp_params = [
    
    [2^6, 48, 56, 8, '128'],
    [2^9, 64, 72, 8, '192'],
    [2^12, 88, 96, 8, '256']
]

### Cost of an arithmetic operation in gates
def gates(q):
    """
    Return the cost of one multiplication in Fq in gates following NIST methodology.
    """
    return log(3*2*(log(q, 2)**2 + log(q,2)),2)

def dreg_semi_reg(n,m, verbose=False) :
    """ 
    HS of a semi-regular quadratic system m in n variables.   
    """
    R.<t> = PowerSeriesRing(ZZ)
    h = (1-t^2)^(m)/(1-t)^(n) 
    #print(list(h))
    L = list(h)
    for i in range(len(L)) :
        if L[i] <= 0 :
            if verbose :
                print(L[i])
            return i
    return len(L)+1

def cost_semi_reg(n,m,q) :
    """
    Compute the bit cost of solving a semi regular system of n variables m equatoins in Fq assuming "sparse solver"
    """
    d = dreg_semi_reg(n,m)
    
    mini= float(log(binomial(n + d, d)**2 * binomial(n, 2),2))
    k_min = 0
    for k in range(1,m-1) :
        d = dreg_semi_reg(n-k,m)
        
        temp = float(log(q^k * binomial(n-k + d, d)**2 * binomial(n-k, 2),2))
        
        if temp < mini :
            mini = temp 
            k_min = k
    print("kmin", k_min)
    return mini + float(log(3*2*(log(q, 2)**2 + log(q,2)),2))


###Direct attack
def thomae_wolf(n,m):
    """
    Return k such that a solution of a quadratic system in m eqs and n vars can be found by solving a systme in m-k eqs and vars.
    """
    r = 0
    while r*(m-1) <= n-m :
        r+=1
    return r-1

def cost_direct(n,m,q):
    """
    Cost of forging a signature of an MQ system over Fq in n vars and m eqs.
    """
    r = 0
    if q % 2 :
        if n > 2*m +2 :
            r=1 # Chap 10
    else :
        r = thomae_wolf(n,m)
    cost, k = cost_semi_reg(m-r,m-r,q)
    return cost, r, k

### Kipnis Shamir
def cost_ks(n,m,q) :
    """ 
    Cost of the Kipnis-Shamir attack against UOV(n,m,q)
    """
    return float(log(q^(n-2*m)*n^2.81, 2))

### Intersection 
def cost_inter(n,m,q):
    k = 2
    """while (n < (2*k-1)/(k-1)*m) and (k<=m) :
        k+=1
    k-=1
    """
    N_vars =  n*k - (2*k-1 )*m
    M_eqs = binomial(k+1,2)*m - 2*binomial(k,2)
    cost, i = cost_semi_reg(N_vars,M_eqs,q)
    return cost, i, k
