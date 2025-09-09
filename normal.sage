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

def N(i,j,n) : 
    """ 
    Change of variables X_j = x_j - x_i
    """
    res = matrix.identity(n)
    if j > n-1 :
        return res
    res[j,i] = -1
    return res 

def M2(i,j,x,y,n) :
    """ 
    Change of variables X_i = xX_i + yX_j, 
                        X_j = xX_i - yX_j
    """
    res = matrix.identity(n)
    if j > n-1 :
        return res
    res[i,j] = y
    res[j,i] = y
    res[i,i] = x
    res[j,j] = -x
    return res 

def S(i,j,n) :
    """ 
    Change of variables X_i = x_j, X_j = x_i
    """
    res = matrix.identity(n)
    res[j,i] = 1 
    res[i,j] = 1
    res[j,j] = 0
    res[i,i] = 0
    return res

def find_N(g, i) :
    """ 
    Assume g[i,i] = 0 for all i. Look for j such that xij!=-xji. If it is not possible, this means there is a V of zeros, and we return -1. 
    """
    n = g.dimensions()[0]
    for j in range(n) :
        if g[i,j] != - g[j,i] :
            return j
    return -1

def quadric_normal_form(g, verbose = False, randomize=False) :
    """
    g is a (square) matrix representing a quadratic form, not necessarily symmetric. V(<x^Tgx>) is the quadric represented by the quadratic form g.
    g admits a diagonalisation:
    there exists a matrix A s.t. g(Ax) = x_1^2 + ... + + x_n-1^2 + ax_n^2, but only in characteristic different from 2.
    We return this matrix.
    """
    #Definitions
    FF = g.base_ring()
    q = FF.characteristic()
    if q == 2 :
        raise Exception("Ill-defined in characteristic 2.")
    n = g.dimensions()[0]
    A = matrix(FF,g) #Work copy of g
    B = matrix.identity(n) #Change of variables
    if randomize :
        B = matrix(FF, complete_basis([], FF**n))
        A = B.transpose()*A*B
    if verbose :
        print(A,'\n')
    #First, we make sure there is no zero on the diagonal of g:
    first_zero = n #Index of the first zero on the diagonal. 
    indices = []
    for i in range(n) :
        if g[i,i] == 0 :
            indices.append(i)
    for i in indices :
        j = find_N(A, i)
        if j != -1 :
            t = N(i,j,n)
        else : 
            t =  S(i,first_zero-1,n)
            first_zero-=1
        B = B*t
        A = t.transpose()*A*t 
        if verbose :
            print(A,'\n')
    #Now, we construct the triangular change of variables that turns A into a diagonal matrix.
    C = matrix(FF,n,n)
    
    for i in range(n-1) :
        
        if A[i,i] == 0 :
            if A[i+1,i+1] != 0 :
                j = i +1
            else :
                j = i+2
                while j < n :
                    if A[j,j]==0:
                        j+=1
                    else :
                        break 
            if j < n :
                t = S(i,j,n) 
                B=B*t 
                A = t.transpose()*A*t 
        C = matrix.identity(FF,n)
        for j in range(i+1,n) :
            if A[i,i] == 0 and A[i+1,i+1] == 0 and A[i,i+1] !=0 and A[i+1,i] != 0 : #hyperbolic square
                t = M2(i,i+1,1,1,n)
                B=B*t
                A = t.transpose()*A*t 
                if verbose :
                    print(A,'\n')
            C[i,j] = (A[i,j] + A[j,i])/(2*A[i,i]) #We do not assume symmetry, and A[i,i] is non-zero by the previous work and assertion.
        
        C1 = C.inverse()
        A = C1.transpose()*A*C1 
        B = B*C1
        if verbose :
            print(A,'\n')
   #We normalize each entry to one if they are squares.
    
    for i in range(n) :
        if A[i,i] == 0 :
            continue 
        if kronecker(A[i,i]**(-1), q) == 1 :
            C = matrix.identity(FF,n)
            C[i,i] = sqrt(A[i,i]**(-1))
            A = C.transpose()*A*C
            B = B*C
            if verbose :
                print(A,'\n')
    #We put all non square entries (ie anything that is not a one at this point) at the end of the diagonal
    first_non_square = n-1
    while first_non_square > 0 and legendre_symbol(A.diagonal()[first_non_square],q) == -1 :
        first_non_square-=1
    
    for i in range(n) : 
        if A[i,i] != 1 :
            if first_non_square < 0 or i >= first_non_square:
                break
            #swap 
            while A[first_non_square,first_non_square] != 1 and first_non_square > 0:
                first_non_square-=1 
            C = S(i,first_non_square,n)
            first_non_square-=1
            A = C.transpose()*A*C
            B = B*C
            if verbose :
                print(A,'\n')
            while legendre_symbol(A.diagonal()[first_non_square],q) == -1 :
                first_non_square-=1
    
    if first_non_square == n-1 : #If we have only squares, then the diagonal is currently the identity.
        return B 

    #Now we aim to turn the remaining non-ones to ones, except at most one. 
    #For this, we pair them up sequentially and do a simple change of variables. 
        
    for i in range(first_non_square+1,n-1,2) :
        if A[i,i] == 0 :
            continue 
        try :
            C = matrix.identity(FF,n)
            C[i,i] = sqrt(A.diagonal()[i]**(-1)*A.diagonal()[i+1])
            if C.determinant() == 0 : 
                continue
            A = C.transpose()*A*C
            B = B*C
            if verbose :
                print(A,'\n')
        except :
            pass
        a = A.diagonal()[i]
        b = A.diagonal()[i+1]
        x,y = root_solution(a,b,1,q)
        if x == 0 and y == 0 :
            continue 
        C = M2(i,i+1,x,y,n)
        A = C.transpose()*A*C
        B = B*C
        if verbose :
            print(A, '\n')
            print("Rank of the change of variables: ", B.rank(),'\n')

    #In case the form is degenerate, we put the zeros in front to facilitate the computation of isotropic subspaces.  
    first_zero = 0
    while A.diagonal()[first_zero] == 0 : 
        first_zero+=1
    for i in range(first_zero,n) :
        if A.diagonal()[i] == 0 :
            C = S(first_zero, i, n )
            A = C.transpose()*A*C 
            B= B* C 
            if verbose :
                print(A,'\n',B.rank(),'\n')
            while A[first_zero,first_zero]==0:
                first_zero+=1
    return B



def root_solution(a,b,c,p) :
    """ 
    find x,y st ax2 + by2 = c mod p via brute search.
    """
    
    for x in range(1,p) :
        for y in range(1,p) :
            if ((a*x**2 + b*y**2) % p) == (c % p):
                return (x,y)
    return (0,0)


def permutation_matrix(n,k) :
    def sigma(i,n,k) :
        if i < k :
            return n-k+i 
        if i >= n-k :
            return i+k-n 
        return i 

    I = matrix.identity(n)
    res = [I.columns()[sigma(i,n,k)] for i in range(n)]
    return matrix(res).transpose()


def reversion_matrix(n) :
    def sigma(i,n) :
        return n-1-i 

    I = matrix.identity(n)
    res = [I.columns()[sigma(i,n)] for i in range(n)]
    return matrix(res)


def reverse_diagonal(g, randomize=False) :
    """  
    Given a matrix g, find a diagonal matrix, or offset diagonal matrix such that disc(D) = disc(G) and return the corresponding change of variables.
    """
    n = g.dimensions()[0]
    FF = g.base_ring()
    C = quadric_normal_form(g, randomize=randomize)
    D = C.transpose()*g*C

    if D.diagonal()[-1] == 1 :
        P = reversion_matrix(n) 
    else :
        disc = D.diagonal()[-1]
        small_p = reversion_matrix(n-1)
        P = block_diagonal_matrix(small_p,matrix(FF,[disc]))
        if P.determinant() == -disc :
            P[-1,-1] = - disc 
    P = matrix(FF,P)

    return C*quadric_normal_form(P).inverse()
    

def hyperbolic_diagonal(g, randomize= False) :
    """ 
    Given a symmetric matrix g, return a change of variables C such that g o C is in Witt-decomposition-form. 
    """

    n = g.dimensions()[0]
    F = g.base_ring()
    p = F.characteristic()
    hblock = matrix(F, [[0,1], [1,0]]) #elementary hyperbolic block

    P = block_diagonal_matrix([hblock for _ in range(n//2)]+[matrix(F,[1]) for _ in range(n-n//2*2)])

    C = quadric_normal_form(g, randomize=randomize)
    D = C.transpose()*g*C
    disc = D.diagonal()[-1] 

    if disc != 1 :
        P[-1,-1] = disc ###-1 is a square mod 2*r - 1 so the last entry will control the discriminant (unless we are in n even case but we can always choose to avoid it). 

    return C*quadric_normal_form(P).inverse()


def reid_form(g, randomize=False) :
    """
    Given a symmetric matrix g, return a change of variables C such that g o C is in Reid shape.:  [ a | 0 | 0 ]
                                                                                                   [ 0 | 0 | I ] 
                                                                                                   [ 0 | I | 0 ]
    """

    n = g.dimensions()[0]
    K = g.base_ring()
    p = K.characteristic()
    r = n//2

    L = matrix(K,r+1,r) #Reid notation
    I = matrix(K, r+1,r)
    
    for i in range(r) :
        I[i+1, i] = 1 
    target = block_matrix(K,[[matrix(K,r+1,r+1),I], [I.transpose(), matrix(K,r,r)]])
    target[0,0] = g.determinant()*(-1)^r    
    C = quadric_normal_form(g, randomize=randomize)

    return C*quadric_normal_form(target).inverse()



### 2 quadrics


#Le code qui suit travaille dans une extension de Fq de degré n ou 2n (selon l'importance que l'on donne a la normalisation)
import numpy

def simultaneous_diagonalisation(g1,g2, verbose = False) :
    """ 
    Simultaneous block diagonalization of quadratic forms g1,g2 using the associated pencil.
    """

    try :
        M = g1.inverse()*g2
    except :
        raise Exception("The pencil is singular.")

    P = M.characteristic_polynomial()
    B = []
    for l,_ in P.factor() :
        B = B + l(M).right_kernel().basis() #primary decomposition of M. 

    #Normalisation
    for i in range(len(B)) :
        N = sum([j**2 for j in B[i]])
        if  sqrt(N) in g1.base_ring() :
            B[i] = sqrt(N)*B[i]

    B2 = matrix(B)
    if verbose :
        print(B2*g1*B2.transpose(), '\n')
        print(B2*g2*B2.transpose())
    return B2


def simultaneous_diagonalisation_closure(g1,g2, verbose = False) :

    F = g1.base_ring()
    
    R2 = PolynomialRing(F, 'x') #2n ou n selon l'importance de la normalisation.
    x = R2.gens()[0]
    g1 = matrix(R2,g1)
    g2 = matrix(R2,g2)
    L = (g1+x*g2).determinant().roots()
    if verbose:
        print(L)
    B = []
    for r,_ in L :
        E = matrix(F,g1 + r*g2).kernel()
        e = E.basis()[0]
        try : 
            roo = sqrt(e*g1*e)**(-1)
        except :
            roo = 1
        B.append(roo*e) #sqrt(e*g1*e)**(-1)* pour normaliser
    B = matrix(B)
    b = (matrix(F,B*g1)).right_kernel().intersection((matrix(F,B*g2)).right_kernel()).basis()
    B2 = matrix(B.rows()+b)
    if verbose :
        print(B2*g1*B2.transpose(), '\n')
        print(B2*g2*B2.transpose())
    return B2

def simultaneous_diagonal_to_witt(D, d2=None, verbose = False) :
    """ 
    Given g a (block) diagonal matrix with (n-1)/2 size 1 blocks, find C,X = (x1...xn) = (a,b.t,c.t) such that
    CgC.t  = a  b  c  
             b  0  L
             c  L  0   
    
    CC.t =  1  0 . 0
            0  0   I
            0  I   0     
    where the two blocks L, I have size (n-1)/2
    """

    n = D.dimensions()[0]
    r=(n-1)//2
    lambdas = D.diagonal()[:r]
    vars = ['b'+str(i) for i in range(r)]
    #vars2 = ['c'+str(i) for i in range(r)]
    K = D.base_ring()
    
    if d2 is None :
        d2 = matrix(K,matrix.identity(n))    

    R3 = PolynomialRing(K, ['y']+vars, 1+r)
    y = R3.gens()[0]
    x = R3.gens()[1:]
    #Polynomes utiles
    f = (y*d2-D).determinant()
    g = product([d2[i,i]*y - lambdas[i] for i in range(r)])
    
    h = f//g 
    
    Q = h//g # = y - a
    a = -Q.coefficients()[-1] #*Q.coefficients()[0]
    
    if verbose:
        print('First write the Euclidean division of the characteristic polynomial by the chosen singular values:')
        print("f(X) = (X-a)g(X)")
        print("X-a = ", Q)
        print('yielding a = ', a)
        print('Then find the remainder of this division:')
    
    M = sum([ -2*x[i]*g//(y-lambdas[i]) for i in range(r)])
    B = h%g
    if verbose :
        print("Find values of bi s.t.", M, ' = ', B)
    system = []
    if verbose:
        print('ie the linear system:')
    for i in range(1,r) :
        if verbose: 
            print(M.coefficient(y**i), ' = ', B.coefficient(y**i))
        system.append(M.coefficient(y**i))
    
    non_constant = sum([system[i]*y**(i+1) for i in range(r-1)])
    constant = M - non_constant
    if verbose:
        print("and constant term: ",constant, ' = ', B.coefficients()[-1])
    system = [constant]+system
    
    mat = [ [ 0 for _ in range(r)] for _ in range(r)]
    for i in range(r) :
        for j in range(r) :
            mat[i][j] = system[i].coefficient(x[j])
    mat = matrix(K,mat)
    vB=vector(K, B.coefficients()[::-1])

    X= mat.solve_right(vB)
    
    M2 = sum([ -2*X[i]*g//(y-lambdas[i]) for i in range(r)])
    
    if verbose:
        print('ie  \n', mat,'X = ', vB)
        print('where X = ', X)
    L = matrix(K,r+1,r) #Reid notation
    I = matrix(K, r+1,r)
    
    for i in range(r) :
        L[i+1, i] = lambdas[i]
        
        I[i+1, i] = 1 
    targetB = block_matrix(K,[[matrix(K,r+1,r+1),L], [L.transpose(), matrix(K,r,r)]])
    targetA = block_matrix(K,[[matrix(K,r+1,r+1),I], [I.transpose(), matrix(K,r,r)]])
    

    targetB[0,0] = a 
    
    targetA[0,0] = 1
    for i in range(r) :
        targetB[0,r+1+i] = 1 #ci
        targetB[r+1+i,0] = 1 #ci

        targetB[0, 1+i] = X[i]
        targetB[1+i,0] = X[i]

    In =matrix(K,matrix.identity(n))
    
    #if verbose:    
    if verbose :
        print("We conclude the Reid-target is:")
        print(targetB)
        print("Which we verify :")
        print("det(A*B   - yI ) = ", matrix(R3, targetA.inverse()*targetB - y*In).determinant())
        print("det(A'*B' - yI) = ", matrix(R3, d2.inverse()*D - y*In ).determinant())
    #Now compute the change of variables from the target to the simultaneous diagonal. 

    C = simultaneous_diagonalisation_closure(targetA, targetB)
    diagA = (C*targetA*C.transpose()).diagonal()
    diagB = (C*targetB*C.transpose()).diagonal()
    permutation = list(numpy.argsort(diagB))
    D = C[permutation]

    return D.inverse()



"""

print("Detailed 1-QF algorithm on a small example.")
n = 11
q = 31
P = random_matrix(GF(q), n-1, n-1)
P = P + P.T
B = quadric_normal_form(P, verbose=True)



print("Detailed 2-QF (Reid) algorithm on a small example.")

q= 17
d1 = diagonal_matrix(GF(q**2),[1 for _ in range(7)])
d2 = diagonal_matrix(GF(q**2), ([GF(q**2)(i+1) for i in range(7)]))
print(d1)
print()
print(d2)

C = simultaneous_diagonal_to_witt(d1.inverse()*d2, verbose=True)
#print(C)
print(' ')
print(C*d1*C.transpose())
print(' ')
print(C*d2*C.transpose())
"""