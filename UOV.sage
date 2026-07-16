
###UOV###
def complete_basis(B, E) :
    """
    This function takes as input a list of linearily independant vectors B in E and 
    completes them into a basis naively.
    If the list is empty, a random basis of E is returned
    """
    res = list(B) #Avoid modifying the input.
    if len(res) == 0 :
        b = E.random_element()
        while b.is_zero() :
            b = E.random_element()
        res.append(b)

    while len(res) != E.dimension() :
        b = E.random_element()
        if not(b in span(res)) :
            res.append(b)
    return res

    

def ROMKeyGen(q,m,v) :
    """
    This function generates a collection of random matrices representing generic quadratic forms.
    It returns a pair (A,F), G where (A,F) are identity matrices to be consistent with the non-ROM KeyGen. 
    """
    FF = GF(q)
    n = m+v
    G = [ matrix(FF,complete_basis([], FF**(n))) for _ in range(m)]
    if (q%2) != 0 :
        for i in range(m):
            G[i] = (G[i] + G[i].transpose())
    return (matrix.identity(n), [matrix.identity(n) for _ in range(m)]), G 

def upper(g) :
    """ 
    Given matrix g, return the upper triangular matrix induced by g.
    """
    n,_ = g.dimensions()
    res = copy(g)
    for i in range(n) :
        for j in range(i+1) :
            res[i,j] = 0
    return res 
    

def complete_basis(B, E) :
    """
    This function takes as input a list of linearily independant vectors B in E and 
    completes them into a basis naively.
    If the list is empty, a random basis of E is returned
    """
    res = list(B) #Avoid modifying the input.
    if len(res) == 0 :
        b = E.random_element()
        while b.is_zero() :
            b = E.random_element()
        res.append(b)

    while len(res) != E.dimension() :
        b = E.random_element()
        if not(b in span(res)) :
            res.append(b)
    return res

    


def KeyGen(q,o,v, m=None, verbose = False):
    """
    This function generates a key pair for UOV parameters o,v where o is the dimension of the oil subspace and v the dimension of the vinegar subspace.
    By default, m=o, but the optional parameter m controls the number of polynomials generated. 
    To do this, we sample random matrices with a block of zero of size to produce the private key.
    We sample a random invertible change of variables A, compute G = F circ A, and return the pair (A,F), G.
    (A,F) is the UOV private key, G is the UOV public key. The corresponding systems are obtained by evaluating the quadratic forms over FF[x1,...,xn].
    Important notice: This code is a demonstration tool and should not used for applications where security matters. 
    """
    if m is None :
        m = o
    n = o+v 
    FF = GF(q)
    RR = None 
    if verbose :
        RR = PolynomialRing(FF, 'x', n)
    
    #Define A
    A = matrix.identity(FF,n)
    for i in range(n-o) :
        for j in range(o) :
            A[n-1-i,j] = FF.random_element()
            
    #Define F, G
    F = []
    G = []
    for e in range(m):
        Fe = matrix(FF, n, n)
        B0 = matrix(FF,o,o)
        B1 = random_matrix(FF,o,v)
        B2 = random_matrix(FF,v,o)
        B3 = random_matrix(FF,v,v)
        Fe = block_matrix([[B0,B1],[B2,B3]])
        
        if FF.characteristic() != 2 : 
            Fe = FF(2)**(-1)*(Fe+Fe.transpose())
        Ge = A.transpose()*Fe*A
        F.append(Fe)
        G.append(Ge)
        
    if verbose :
        print("The public key system is:")
        x = vector(RR.gens())
        for Ge in G :
            print(x*Ge*x)
    return ((A,F), G) 
    
def Sign(PrK, M, depth = 0, verbose = False): 
    """
    Given a UOV private key (A,F), a target M, and a maximum number of allowed signature fails, attempt to produce a valid signature X of M.
    """

    max_depth = 10 #Fail after 10 retries (arbitrary value). Probability : (p_failure)^10 
    if depth > max_depth:
        raise Exception("The signature procedure has failed.")
    
    A,F = PrK
    q = A.base_ring().cardinality()
    m = len(F)
    n = F[0].dimensions()[0]
    v = n-m
    A_1 = A.inverse()
    FF = GF(q)
    RR = PolynomialRing(FF, 'x', m)
    X = RR.gens()

    #Generate random values for vinegar variables.
    Y_2 = [FF.random_element() for _ in range(v)]

    Y = vector(RR, list(X) + Y_2)

    #Use linear algebra to solve for oil variables.
    system = []
    for e in range(m):
        system.append(Y*F[e]*Y)
    if verbose:
        print("The signer solves the system: ", system)
    #This system is linear in x_1, ..., x_k 
    mat = [ [ 0 for _ in range(m)] for _ in range(m)]
    for i in range(m) :
        for j in range(m) :
            mat[i][j] = system[i].coefficient(X[j])

    S = matrix(FF, mat)
    B = vector([system[i]([0 for _ in range(m)]) for i in range(m)])
    target = M-B 

    try: 
        Y_1 = S.solve_right(target)
    except:
        print("The system is not invertible, we try again with different random values.")
        return Sign(PrK, M, depth+1, verbose) 
    Y_hat = vector(FF, list(Y_1) + Y_2) #Recombination
    
    if verbose :
        print("Number of retries : ", depth)
    
    #Use Secret Key to return an 'X' solution.
    return A_1*Y_hat

def Verify(M, X, G, verbose = False): 
    m = len(G)
    n = len(X)
    v = n-m 
    for e in range(m):
        if verbose :
            print("P"+str(e)+"(X)= ", X*G[e]*X,"and M"+str(e)+"= ", M[e])
        if not X*G[e]*X==M[e]:
            return False
    return True