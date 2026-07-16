load('UOV.sage')
def hpKeyGen(q,o,v,m,t ) :
    """ 
    m equations of a UOVhp(qovt) key.
    """
    n = o + v
    F = []
    
    #Hat plus equations
    for _ in range(t) : 
        f = matrix([[ GF(q).random_element() for _ in range(n)]for _ in range(n)] )
        F.append(f + f.transpose())
    #UOV equations
    for _ in range(m-t) :
        f = matrix([[ GF(q).random_element() for _ in range(n)]for _ in range(n)] )
        for i in range(o) :
            for j in range(o) :
                f[i,j] = 0
        F.append(f+f.transpose())

    A = matrix(complete_basis([], GF(q)^n))

    #Public key
    G = [A.transpose()*f*A for f in F]
    if t == m :
        return (A,[], F, G), G
    Sp = matrix([[GF(q).random_element() for _ in range(t) ]for _ in range(m)])
    
    G2 = [ G[i] + sum([Sp[i,j]*G[j] for j in range(t)]) for i in range(m)]
    
    return (A,Sp,F, G), G2

def FOXKeyGen(q,o,v,t ) :
    """
      
    """
    n=o+v
    (A,F), G = KeyGen(q,o,v) #Underlying UOV of the key-pair.
    for i in range(t) :
        F[i] = matrix(complete_basis([],GF(q)**n)) #We replace the first t equations by random quadratic equations.
        G[i] = A.transpose()*G[i]*A
    Sp = matrix(complete_basis([],GF(q)**(o-t)))[:t] #We generate the S-map.

    S = block_matrix([[matrix.identity(GF(q),t),Sp], [matrix(GF(q), o-t, t), matrix.identity(GF(q),o-t)]])
    G2 = [ sum([S[j,i]*G[j] for j in range(o)]) for i in range(o)]
    
    return (A,S,F, G), G2 #This a pair of the form Secret key, Public key.

