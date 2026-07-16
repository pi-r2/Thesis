load("UOV.sage")


### State of the art.

def KPG_induction(P, r, verbose=False) :
    """
    Implementation of the Kipnis, Patarin, Goubin algorithm to compute a linear subspace vanishing a collection of quadratic forms in fields of characteristic two.
    """
    n = P[0].dimensions()[0]
    m = len(P)
    FF = P[0].base_ring()

    ###Induction: step 0
    i=0
    s1 = [1] + [0 for _ in range(m-1)] + [FF.random_element() for  _ in range(n-m)]
    S1 = vector(s1)
    S = [S1]
    if verbose:
        print("The basis is iteratively computed, and S1 is chosen randomly:")
        print("S1=", S1)


    for i in range(1, m):
        ###Induction: step i
        R = PolynomialRing(FF, ['s'+str(i) for i in range(n-1)], n-1)
        si =  list(R.gens())[:i] + [1] + list(R.gens())[i:] 
        Si = vector(si)
        eqs = []
        for Sj in S :
            for p in P[:r]:
                eqs.append(Sj*p*Si + Si*p*Sj)
        I = Ideal(eqs)
        d = I.dimension()

        H = []
        j = 0
        while j < d and j < m-1 :
            H.append(R.gens()[j]) 
            j+=1
        while j < d :
            H.append(FF.random_element() + sum([FF.random_element()*x for x in R.gens()[m-1:]])) 
            j+=1        
        V = (Ideal(eqs+H).variety())[0]




        fSi = Si([V[s] for s in R.gens()])
        if verbose:
            print("S"+str(i+1)+"=", fSi)

        S.append(fSi)
    matS = matrix(FF, m,n, S)
    return matS




import itertools

def KipnisShamir(G, verbose = False) :
    """
    Perform a Kipnis-Shamir attack on G.
    This implementation follows the singular point formalism, but it is entirely equivalent to the original formulation.
    """
    o = len(G)
    n= G[0].dimensions()[0]
    v = n-o
    q = G[0].base_ring().cardinality() 
    
    def test(G,x):
        for g in G :
            if x*g*x != 0 :
                return False
        return True 

    r = o-1
    g = itertools.product(range(q),repeat=r)
    tries = 0
    if verbose:
        print(f"We expect q^(n-2m)=q^{n-2*o}=2^{float(log(q^(n-2*o),2))} tries before success.")
    print("We repeatedly choose a random linear combination of public key matrices, and compute the corresponding characteristic polynomial following Section 3.3.5.")
    for i in g :
        tries+=1
        guess =  [1] + list(i) 
        M = sum([guess[i]*G[i] for i in range(o)])
        if M.determinant() != 0:
            continue
        for x in M.kernel().basis():
            if test(G,x):
                r = (G[1].inverse()*M).charpoly()
                if verbose:
                    print(f"For instance, we choose the linear coefficients {guess} for the combination.")
                    print(f"The characteristic polynomial is {r.factor()}")
                    print("For each factor, we compute a basis of the corresponding eigenspace:")
                    print("If it is non-empty, then we have found a solution.")
                    for f,_ in r.factor() :
                        print(f,":" , f(M).right_kernel().basis())
                        try: 
                            y = (f(M).right_kernel()).basis()[0]
                            break
                        except:
                            continue
                    print(f"The number of attempts was q^{float(log(tries, q))}.")
                return x 
            else :
                continue
    raise Exception("Attack failed.")




def reconciliation(G, r, verbose=False) :
    """
    Given m matrices G1...Gm, find, if it exists, a (basis of a) linear subspace A of dimension m such that A.T G1 A = ... = A.T Gr A = (0)^m*m. 
    The algorithm begins by computing r vectors of A simultaneously, before completing the basis using linear algebra.
    """
    #
    F = G[0].base_ring()
    n = G[0].dimensions()[0]
    m = len(G)
    d=m
    id_block = identity_matrix(F, d)[:r,:]
    
    # Non-linear step.
    R = PolynomialRing(F, 'x', r*(n-m))
    M = matrix(r,n-m,R.gens())
    
    X = block_matrix(R, 1, 2, [id_block, M])
    if verbose:
        print("We define an indeterminate sub-basis of the oil space.")
        print(X)
        print("The polynomial system is then the entries of the matrices X^T.Pi.X for 1 <= i <=m.")
    eqs = []
    for g in G:
        eqs = eqs + (X*g*X.T).coefficients()

    codim = m*binomial(r+1,2)
    if verbose:
        print(f"The system has codimension {codim} and {r*(n-m)} variables.")
        if codim > r*(n-m) :
            print(f"By the existence of a UOV trapdoor, we know that it admits a solution.")
    return eqs, X





def intersection(G, o, ind = (0,1), verbose = False) :
    """ 
    Takes as input a UOV public key and returns the polynomial system modelling the intersection attack with k = 2 of Beullens.
    """

    i1, i2 = ind
    m = len(G)
    n = G[0].dimensions()[0]
    F = G[0].base_ring()
    R = PolynomialRing(F,'X',2*n-3*o) #Variable count from Beullens' criterion.
    x = vector([1] + [0 for _ in range(3*o-n-1)] + list(R.gens()))
    
    sys = []

    polar_forms = [g + g.T for g in G] #This is important in characteristic two and has no consequence in even characteristic.
    M1 = polar_forms[i1].inverse()
    M2 = polar_forms[i2].inverse()
    
    Mix = M1*x 
    Mjx = M2*x 
  
    if verbose :
        print("We consider an indeterminate vector X in the intersection of P1*O and P2*O.")
        print(x)
        print("The following two vectors, its pre-image by P1 and P2, are elements of O:")
        print(f"P1.inverse()X = {Mix}")
        print()
        print(f"P2.inverse()X = {Mjx}")
        print("Thus, we use the Reconciliation attack to model that property.")
    for e in range(len(G)) :
        Ge=  G[e]
        if e != i1 : # We avoid adding useless equations, note though that they do not slow down a solver if kept.
            sys.append(Mix *Ge*Mix)
        sys.append( Mix *Ge*Mjx )
        if e != i2 :
            sys.append(Mjx *Ge*Mjx)
    return sys, x





### Contributions.__


def key_recovery_from_one_vector(G,v) :
    """ 
    This function is the one that completes the attack.

    Given G a set of m quadratic forms admitting a common totally isotropic subspace O
    of dimension at least (n-m)/2, and v in O, find a basis of O as a whole.
    """
    m = len(G) 
    J = matrix([v*g for g in G]) 
    B = matrix(J.right_kernel().basis())
    B2 = []
    charac = G[0].base_ring().characteristic()
    for g in G :
        ghat = B*g*B.transpose()  #restriction of G to the kernel of J
       	if charac == 2 :
            ghat = ghat + ghat.transpose()
        for b in ghat.kernel().basis() :
            if len(B2) == 0 or b not in span(B2) :
                B2.append(b)
        if len(B2) == m :
            break
    B3 = matrix(B2)
        
    C = B3*B
    return C
    
def in_secret_subspace(G, v) :
    """
    This function takes as input a vector x and a UOV public key G, and returns True if the vector belongs to the secret subspace,
    and False otherwise. 
    """
    n = G[0].dimensions()[0]
    m = len(G)
    charac = G[0].base_ring().characteristic()

    for g in G : #Sanity check
        if v*g*v != 0 :
            return False
    
    J = matrix([v*g for g in G]) 
    B = matrix(J.right_kernel().basis())
    
    for g in G :
        ghat = B*g*B.transpose() #Restriction to K(v)
        if charac == 2 :
            ghat = ghat + ghat.transpose()
        if ghat.rank() > 2*(n-2*m) :
            return False 
    return True 
 


def one_vector_FOX(G,x,t, verbose = False) :
    """ 
    Perform a key recovery on FOX from one known vector in the secret UOV subspace, using an enumerative approach.
    Public key G, vector x, hp parameter t.
    Return [] if the attack failed. This is also a membership test for x in O. 
    """
    n = G[0].dimensions()[0]
    o = len(G)
    v = n-o
    c = v-o
    q = G[0].base_ring().cardinality()
    if verbose: 
        print("First, we compute the right kernel of the Jacobian of the system at x.")
    J = matrix([x*g for g in G]) #This is (1/2) the Jacobian of the public key evaluated at x.
    C=matrix(J.right_kernel().basis()) #This is the change of variables that restricts to the kernel of the Jacobian.
    if verbose :
        print(f"Then, we restrict the public key equations to this subspace, which has dimension {C.dimensions()[0]}.")
    G3 = [C*g*C.transpose() for g in G] #This is the restriction of the public key to the kernel of J.

    N = G3[0].dimensions()[0]
    R = PolynomialRing(GF(q), 'X', N-1)
    X = vector(list(R.gens())+[1]) # we arbitrarily choose to set one of the hyperplanes to xN=1 which dehomogenizes the equations.
    if verbose:
        print(f"Next, we compute a grevlex Grobner basis for the ideal defined by the equations of this restriction to which we add o-2t-1={o-2*t-1} hyperplanes to obtain a zero-dimensional intersection with Ot.")
    eqs = [X*g*X for g in G3]+[X*vector([GF(q).random_element() for _ in range(N)]) for _ in range(o-2*t-1)] #Here we add 1 less hyperplane to compensate for xN-1 which was accounted for earlier.
    gb = Ideal(eqs).groebner_basis(algorithm='libsingular:groebner')[::-1]
    if len(gb) == 1 :
        if verbose :
            print("The ideal is the trivial ideal.")
        return []    
    lgb = [ i.lt() for i in gb]
    
    
    
    M = [[gb[i].coefficient(X[j]) for j in range(N-1)] + [0]
                for i in range(o-1)]
    M = matrix(GF(q), M)
    for i in range(o-1) :
        M[i,-1] = gb[i]([0 for _ in range(N-1)])
    
    if verbose :
        print(f"There are {o-1} polynomials of the Groebner basis that are linear:")
        for g in gb[:o-1] :
            print(g)
        print("The intersection of the hyperplanes in the basis is Ot.")
    D = matrix((M.right_kernel()).basis())
    return D*C

def x_in_O(G,x,t) :
    l = one_vector_FOX(G,x,t)
    if l == [] :
        return False 
    return True 



def singularKipnisShamir(G, test_function, limit=None) :
    """
    Perform a Kipnis-Shamir attack using the singular point formalism.
    """
    m = len(G)
    n = G[0].dimensions()[0]
    F = G[0].base_ring()
    q = F.cardinality()
    R = PolynomialRing(GF(q), 'l')
    if limit is None:
        limit=q**(n-2*m+1)
    tries = 0
    while tries < limit:     
        tries+=1
        guess = [R.gens()[0], 1]+[F.random_element() for _ in range(m-1)]
        M = sum([guess[i]*G[i] for i in range(m)])
        for l, _ in M.determinant().roots() :
            for x in M(l).kernel().basis() :
                if test_function(x,G) :
                    print(f"Success after {tries} tries.")
                    return x  
                else :
                    continue
                    
                    