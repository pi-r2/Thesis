import os 
import csv 


def OVinit(q,k):
    F = GF(q)
    R = PolynomialRing(F,'x',2*k)
    R.inject_variables(verbose=False)
    F.inject_variables(verbose=False)
    
    return F,R

def OVsystem_to_matrix(S,FF): #in: k*k multivariate polynomial system in RR that is in fact linear.
                           #out: (mat: FF matrix k*k; B: FF vector k*1) s.t. S = A.x[1:k] - B  
    
    k = len(S.rows()) #S is a k*k system. 
    mat = []
    B = [0 for _ in range(k)]
    
    
    #str(S[e][0].monomials()[i])[1:] -> coefficient du i-eme monome dans la e-ieme equation du systeme
    for e in range(k):
        Se = S[e]
        eq= Se[0]
        line = [0 for _ in range(k)]
        for i in range(len(eq.monomials())):
            if str(eq.monomials()[i])[0] == 'x': #If it is not the case, the monomial is a constant.
                coef = int(str(eq.monomials()[i])[1:])
                line[coef]=eq.coefficients()[i]
            else: 
                B[e] = -eq.coefficients()[i] #We directly add the constant to the target vector B.
        mat.append(line)
    mat = matrix(FF,k,k,mat)
    B = vector(FF,k,B)
    return mat, B



def write_example(Gstar, q,k, dire= "") : #Given public key Gstar, store it as a csv file for further use
    with open(dire+'pub'+str(q)+'_'+str(k)+'.csv', 'w') as f:
        c = csv.writer(f)
        c.writerows(Gstar)
        

def read_example(q,k, dire = "") : #Given a public key as a csv file, turn it into a usable input for sage implem.
    with open(dire+'pub'+str(q)+'_'+str(k)+'.csv', 'r') as f:
        FF, RR = OVinit(q,k)
        c = csv.reader(f)
        Gs = []
        for Ge in c :
            vecs = []
            for Gev in Ge :
                vecs.append(vector(FF,list(map(FF,(Gev[1:-1]).split(',')))))
            Gs.append(matrix(FF,vecs))
        
        return Gs
    
def write_example2(A, q,k,dire="") : #Given private key S, store it as a csv file for further use
    with open(dire+'sec'+str(q)+'_'+str(k)+'.csv', 'w') as f:
        c = csv.writer(f)
        c.writerows(A)
        

def read_example2(q,k, dire = "") : #Given a private key as a csv file, turn it into a usable input for sage implem.
    with open(dire+'sec'+str(q)+'_'+str(k)+'.csv', 'r') as f:
        FF, RR = OVinit(q,k)
        c = csv.reader(f)
        Gs = []
        for Ge in c :
            vecs = []
            for Gev in Ge :
                vecs.append(vector(FF,list(map(FF,(Gev[1:-1]).split(',')))))
            Gs.append(matrix(FF,vecs))
        A = Gs
        return A

def short_to_long_key(G,A,q,k) :
    F = []
    for Ge in G :
        F.append(((A.transpose()).inverse())*Ge*(A.inverse()))
    return (A,F)


def vector_to_tex(v) :
    RR = v.base_ring()
    args = list(RR.variable_names())
    var = args[0][0] #ex: x
    k = len(list(v))
    res = ""
    for vi in list(v) :
        current = str(vi)
        copy = ""
        for i in range(len(current)) :
            if current[i] == var :
                copy+= var + '_'
            elif current[i] != "*" :
                copy+= current[i]
            
        res+= copy + " \\ "
        
    return repr(res)

def minor(M, rows, cols) :
    m = M[rows, cols]
    return m.determinant()


def random_affine_matrix(k, RR) : #Generates a random affine matrix to be compared with a matrix generated in the KS OV attack.
    FF = base_ring(RR)
    vars = vector(RR, RR.variable_names()[:k])
    Mat = matrix(RR, (k+1)*(k+2),2*k)
    for i in range((k+1)*(k+2)) :
        for j in range(2*k) :
            Mat[i,j] = [random_matrix(FF, 1,k)*vars][0][0] + FF.random_element()
    return Mat
            
################# OV ##################

#Definition


def OVKeyGen(q,k): #Compromise: large private key and fast signature or smaller key and slower signature ?
                # case 1 : store both A,F, case 2 : store only 1
                # Beullens : case 2
            
    FF,RR = OVinit(q,k) #Double letter for field/ring to avoid confusion with F,G which are matrices.
    
    #Define A
    A = complete_basis([], FF**(2*k))
    A = matrix(FF, A)
    
    #Define F, G
    F = []
    G = []
    for e in range(k):
        B0 = zero_matrix(FF,k,k)
        B1 = random_matrix(FF,k,k)
        B2 = random_matrix(FF,k,k)
        B3 = random_matrix(FF,k,k)
        Fe = (block_matrix([[B0,B1],[B2,B3]]))
        Ge = A.transpose()*Fe*A
        F.append(Fe)
        G.append(Ge)
    return ((A,F), G) # (Private key, Public key): we can eventually get rid of F in PrK

def OVSign(PrK, M, q, k, depth = 0, verbose = False): 
    FF,RR = OVinit(q,k) #Double letter to avoid confusion with F,G which are matrices. 
    
    max_depth = 10 #Fail after 10 retries (arbitrary value). Probability : (p_failure)^10 
    if depth > max_depth:
        raise Exception("The signature procedure has failed.")
    
    #Generate random vinegar variables.
    A,F = PrK
    A_1 = A.inverse()
    X = RR.variable_names()
    Y_2 = random_matrix(FF,1,k)
    Y = matrix(RR, 1,2*k, list((X)[0:k]) + list(Y_2[0]))

    #Use linear algebra to solve for oil variables.
    system = []
    for e in range(k):
        system.append(Y*F[e]*Y.transpose()) 
    system = matrix(RR,system)
    S, B = OVsystem_to_matrix(system,FF)

    target = B+M 
    try: 
        Y_1 = S.solve_right(target)
    except:
        return Sign(PrK, M, q, k, depth+1, verbose)
    Y_hat = vector(FF, list(Y_1)+list(Y_2[0])) #Recombination
    
    #Use Secret Key to return an 'X' solution.
    if verbose :
        print("Number of retries : ", depth)
    return (A.inverse()) * Y_hat

def OVVerify(M, X, G, q, k, verbose = False): 
    FF,RR = OVinit(q,k) #Double letter to avoid confusion with F,G which are matrices.
    X=matrix(RR,1,2*k,X)
    ver = True
    for e in range(k):
        if verbose :
            print(("G"+str(e)+"(X)= ", X*G[e]*X.transpose()," M"+str(e)+"= ", M[e]))
        ver = ( X*G[e]*X.transpose()==M[e])
        if not(ver):
            return False
    return True
    
##Demo

def OVdemo(q,k) :
    FF,RR = OVinit(q,k)
    
    args = x0.args()
    args = matrix(RR,1,2*k,args)
    
    print("Key generation :")
    PrK, G = KeyGen(q,k)
    A,F = PrK
    print("The secret key generated is the matrix A :\n", A)
    print("And the secret polynomials F_1,...,F_k :\n")
    for Fe in F: 
        print(Fe)
        print((args*Fe*args.transpose())[0])
    print("The public key is composed of the polynomials G_1, ..., G_k :\n")
    for Ge in G :
        print(Ge)
        print((args*Ge*args.transpose())[0])
    M = random_matrix(FF,1,k)
    M = vector(FF,M[0])
    print("The signer wants to sign message M:\n", M)
    X = Sign((A,F), M,q,k, verbose = True)
    
    print("They use their secret key to generate a random signature - it may require a few tries - and obtain a vector X:\n", X)
    
    print("The receiving end of the pair Message M, Signature X, checks that it verifies G(X) = M:")

    print(Verify(M,X,G,q,k, verbose = True))



def ToMSolve(F, finput="/tmp/in.ms"): #From msolve library interfaces
    """Convert a system of sage polynomials into a msolve input file.

    Inputs :
    F (list of polynomials): system of polynomial to solve
    finput (string): name of the msolve input file.

    """
    A = F[0].parent()
    assert all(A1 == A for A1 in map(parent,F)),\
            "The polynomials in the system must belong to the same polynomial ring."
    variables, char = A.variable_names(), A.characteristic()
    s = (", ".join(variables) + " \n"
            + str(char) + "\n")

    B = A.change_ring(order = 'degrevlex') 
    F2 = [ str(B(f)).replace(" ", "") for f in F ]
    if "0" in F2:
        F2.remove("0")
    s += ",\n".join(F2) + "\n"

    fd = open(finput, 'w')
    fd.write(s)
    fd.close()
    
    
def msolve(eqs, threads = 8, verbose =False) :
    """ 
    Solve eqs using msolve.
    Input: a list of equations 
    Output: a single solution of the system, or an empty list if no solution has been found.
    """
    
    R = eqs[0].parent()
    if verbose:
        v = ' -v2 '
    else :
        v = ""
    for i in range(q) :
        eqs2 = eqs + [R.gens()[0] - i]        
        ToMSolve(eqs2, '/tmp/in.ms')
        os.system("/home/pierre/msolve/msolve  "+v+" -g2 -t"+str(threads)+" -f /tmp/in.ms -o /tmp/in.o > /tmp/in.log")
        gb = FromMsolve("/tmp/in.o", R)
        if len(gb) > 1:
            I = Ideal(gb)
            V = I.variety()
            if len(V) == 0 :
                return []
            sols = [vector( [V[i][x] for x in R.gens()]) for i in range(len(V))]
            return sols

    return []


def FromMsolve(output,R):
    with open(output, 'r') as o :
        sols = []
        for l2 in o.readlines()[2:] :
            l = ''
            for c in l2 :
                if c not in ['[', ']', '\n', ',' , ':'] :
                    l+=c    
            if l[0] == '#' :
                continue
            sols.append(R(l))
    return sols


def FromMsolve2(output,R):
    with open(output, 'r') as o :
        sols = []
        for l2 in o.readlines()[2:] :
            if l2[0] == '#' :
                continue
            l2.strip("[],:\n")
            monomials = l2[:-1].split("+")
            polynomial = sum([R(m) for m in monomials])
            sols.append(polynomial)
    return sols
    

def FromMsolveLT(output,R):
    with open(output, 'r') as o :
        sols = []
        for l2 in o.readlines()[2:] :
            if l2[0] == '#' :
                continue
            monomials = l2[:-1].split("+")
            m = monomials[0].strip("[")
            m = m.strip(",")
            m = m.strip(":")
            m = m.strip("]")
            sols.append(R(m))
    return sols

def FromMsolve_deg1_bis(output,RR):
    
    with open(output, 'r') as o :
        
        lines = o.readlines()[4:]
        sols = []

        lines = [l.replace('[','') for l in lines]
        lines = [l.replace(']','') for l in lines]
        lines = [l.replace('\n','') for l in lines]
        lines = [l.replace(',','') for l in lines]
        lines = [l.replace('1*','') for l in lines]
        lines = [l.replace(':','') for l in lines]
        for l in lines :
            
            vari = RR(l).monomials()[0]
            if len(RR(l).monomials()) > 1 :
                val = -RR(l).coefficients()[-1]
            else :
                val = 0
            sols.append((vari,val))
        
    return sols

def FormatOutputMSolve(foutput):
    """Convert a msolve output file into a rational parametrization 

    Inputs :
    foutput (string): name of the msolve output file

    Output :
        A rational parametrization of the zero-dimensional ideal describing
    the solutions. Note : p[i] and c[i] stand for the (i+1)-th coordinate.

    """
    f = open(foutput,'r')
    s = f.read()
    s = s.replace("\n","").replace(":","")
    R = sage_eval(s)
    A.<t> = QQ[]
    # dimension
    dim = R[0]
    if dim > 0:
        return None, None, A(-1), None, None, None, None

    # parametrization
    nvars       = R[1][1]
    qdim        = R[1][2]
    varstr      = R[1][3]
    linearform  = R[1][4]
    elim        = R[1][5][1][0]
    den         = R[1][5][1][1]
    polys       = R[1][5][1][2]
    # solutions
    intervals   = R[2][1]

    #  nvars, degquot, deg = L[1], L[2], L[5][0]
    #  varstr      =   L[3]
    #  linearform  =   L[4]

    if len(elim) > 0:
        pelim = A(elim[1])
    else:
        return None, None, A(-2), None, None, None, None

    pden, p, c = A(1), [], []
    if qdim > 0:
        pden = A(den[1])
        for l in polys:
            p.append(A(l[0][1]))
            c.append( l[1] )

    S   =   []
    if len(intervals) > 0:
        for sol in intervals:
            s = []
            for i in range(nvars):
                s.append((sol[i][0]+sol[i][1])/2)
            S.append(s)
    return [varstr, linearform, pelim, pden, p, c, S]

def FromMsolve_deg1(output,RR):
    with open(output, 'r') as o :
        
        lines = o.readlines()[4:]
        
        sols = []

        lines = [l.replace('[','') for l in lines]
        lines = [l.replace(']','') for l in lines]
        lines = [l.replace('\n','') for l in lines]
        lines = [l.replace(',','') for l in lines]
        lines = [l.replace('1*','') for l in lines]
        lines = [l.replace(':','') for l in lines]
        if lines == "['1']" or lines[0] == '' :
            return []
        
        for l in lines :
            if str(RR(l).monomials()[0])[1:] == '' :
                return []
            vari = int(str(RR(l).monomials()[0])[1:])
            if len(RR(l).monomials()) > 1 :
                val = -RR(l).coefficients()[-1]
            else :
                val = 0
            sols.append((vari,val))
        
    return sols


def quadratic_map(G,X) :
    """Return G(X)"""
    return [X*g*X for g in G]
    



###############################
# This code is from Hosein Hadipourh at https://github.com/hadipourh/mqchallenge
###############################

import sys
def MQC_to_file(inputfile_name,outputfile_name) :
    with open(inputfile_name, 'r') as inputfile:
        file_contents = inputfile.readlines()
    field_line = file_contents[0].split(" : ")[1]
    field_line = field_line.replace(" ", "")
    if "/" in field_line:
        field_line = field_line.split("/")
        R = sage_eval(field_line[0],locals={'x':x})
        F = R.base()
        modulus_poly = R(symbolic_expression(field_line[1]))
        base_field = F.extension(modulus_poly, 'a', repr='int')
        str_to_field_element = lambda t: base_field(list(map(int, list(bin(int(t, 16))[:1:-1]))))
    else:
        base_field = sage_eval(file_contents[0].split(" : ")[1])
        str_to_field_element = lambda t: base_field(t)
    number_of_variables = int(file_contents[1].split(" : ")[1])
    number_of_equations = int(file_contents[2].split(" : ")[1])
    monomial_order = file_contents[4].split(" : ")[1]
    polynomial_ring = PolynomialRing(base_field, number_of_variables, names='x', order='degrevlex')
    exponents = IntegerVectors(2, number_of_variables, max_part=2).list()
    quadratic_monomials = []
    for e in exponents:
        quadratic_monomials.append(polynomial_ring.monomial(*e))
    linear_monomials = []
    for var in polynomial_ring.gens():
        linear_monomials.append(var)
    monomials = quadratic_monomials + linear_monomials + [1]
    monomials.sort(reverse=True)
    monomials = matrix(monomials).transpose()
    # coefficient_matrix = matrix(base_field, number_of_equations, number_of_variables)
    coefficient_matrix = []
    for i in range(7, 7 + number_of_equations):
        row = file_contents[i].replace(" ;", "")
        row = row.split(" ")
        coefficient_matrix.append(list(map(str_to_field_element, row)))
    coefficient_matrix = matrix(coefficient_matrix)
    polynomials = coefficient_matrix*monomials
    if base_field == GF(2):
        flt = lambda x: x if (not x.is_square() or x.is_constant()) else x.variable()
        simplifier = lambda f : sum(list(map(flt, f.monomials())))
        simplified_equations = []
        for row in polynomials.rows():
            simplified_equations.append(simplifier(row[0]))
        equations = simplified_equations
        equations_str = list(map(str, equations))
    else:
        equations = []
        for row in polynomials.rows():
            equations.append(row[0])
        equations_str = list(map(str, equations))
    with open(outputfile_name, 'w') as file:
        file.write("Base field: %s\n" % str(base_field))
        file.write("Modulus: %s\n" % str(base_field.modulus()))
        for eq in equations_str:
            file.write(eq)
            file.write('\n')
    return equations

###Starting here, this is mine (but likely redundant with sage)
def homogeneous_part(eqs) :
    """ 
    Given a system of quadratic equations eqs, return the homogeneous part of degree two and the affine part separately.
    """
    m = len(eqs)
    hom = [0 for _ in range(m)]
    aff = [0 for _ in range(m)]
    monomials = eqs[0].monomials()
    for i in range(m) :
        e = eqs[i]
        for j in range(len(e.monomials())) :
            monomial = e.monomials()[j]
            coef = e.coefficients()[j]
            if monomial.degree() > 1 :
                hom[i]+= coef*monomial
            else :
                aff[i] += coef*monomial
    return hom, aff

def homogeneous_to_matrix(eqs) :
    """  
    Given m quadratic equations eqs, return m symmetric matrices representing the corresponding quadratic forms.
    """
    FF = eqs[0].base_ring()
    RR = eqs[0].parent()
    RR.inject_variables(verbose=False)
    n = len(RR.variable_names())
    m = len(eqs)
    G = []
    for e in eqs :
        mat = matrix(FF, n,n)
        for i in range(n) :
            for j in range(i,n) :
                xi = RR(RR.variable_names()[i])
                xj = RR(RR.variable_names()[j])
                mat[i,j] = e.coefficient(xi*xj)
        if FF.characteristic() != 2 :
            G.append(FF(2)**(-1)*(mat + mat.transpose()))
        else :
            G.append(mat)
    #Sanity check :
    flag = True 
    X = vector(RR, RR.variable_names())
    for i in range(m) :
        e2 = X*G[i]*X 
        flag = flag & (e2 - eqs[i] == 0)
        if not flag :
            raise Exception("The matrices do not correspond to the quadratic forms!")
    return G 


def sage_to_mqc(P, foutput = '/tmp/challenge.xl', XL = True) :
    """  
    Given a system of multivariate quadratic equations, store it in a file format 
    matching the MQC website. If the option XL is set to true, remove the header of that file,
    so that it is directly readable by Niederhagen's XL implementation.
    """



    RR = P[0].parent()
    q = P[0].base_ring().characteristic()
    RR.inject_variables(verbose=False)
    X = vector(RR,list(RR.variable_names())+[1])
    L = (sum(list(X))**2).monomials()
    with open(foutput,'w') as f:
        if not(XL) :
            f.write('Galois Field : GF('+str(q)+')\n')
            f.write('Number of variables (n) : '+str(len(X)-1)+'\n')
            f.write('Number of polynomials (m) : '+str(len(P))+'\n')
            f.write('Seed : 0\n')
            f.write('Order : graded reverse lex order\n')
            f.write('\n')
            f.write('*********************\n')
        for eq in P :
            line = "" 
            for m in L :
                coef = eq.coefficient(m)
                if coef.degree() != 0 :
                    try : 
                        coef = coef.homogeneous_components()[0]
                    except :
                        coef = 0
                line = line + str(coef) + " "  
            line = line + ";\n"
            f.write(line)
        
####

def delta_dm(n,r,m) :
    
    """Special case of TH2.1 where vector(d) = (d,...,d)"""

    return (r+1)*(n-r) - m*binomial(2+r, r)

def delta_moins(n,m,r) :
    return min(delta_dm(n,r,m), n-2*r-m )

def borne_debarre_manivel(n,m) :
    """ 
    Implementation de delta de Debarre Manivel Th2.1 

    Return smallest r such that there are no r-dimensional proj subspaces in the projective variety spanned by m generic equations of degree two in P(K^n)
    """
    for r in range(2,n) :
        if delta_moins(n,m,r) < 0:
            return r
    return n


def FromMSolveRational(file, R) :
    """
    Take as input an msolve output in rational parametrization mode and returns a list lexGB that contains the parametrization describing a lexicographical Gröbner basis with respect to a lexicographic ordering chosen by msolve.
    """
    with open(file,'r') as f :
        l= f.readlines()
        first = l[0]
        first = first.replace("[", '')
        first = first.replace(",", "")
        first = first.replace("\n", "")

        char = first.split(" ")[1]

        vars = l[3]
        vars = vars.replace("[", '')
        vars = vars.replace("]", "")
        vars = vars.replace(",", "")
        vars = vars.replace("'", "")
        vars = list(map(R,vars.split(" ")))
        print(vars) #May be different from the expected ordering !
        xelim = vars[-1]
        R2 = PolynomialRing(GF(char),'t')
        univariate = R2(0)
        X = R2.gens()[0]
        #sdeg = l[6].replace('[', '')
        #sdeg = sdeg.replace(',', '')
        #deg = int(sdeg)
        params = []
        scoefs = l[7]
        scoefs = scoefs.replace('[', '')
        scoefs = scoefs.replace(']', '')
        scoefs = scoefs.replace(',', '')
        coefs = list(map(int, scoefs.split(' ')))
        #deg = len(coefs) - 1
        for i in range(len(coefs)) :
            univariate += X**i * coefs[i]
        parametrizer = univariate
        params.append(parametrizer(xelim))
        for i in range(len(vars)-1) :
            univariate = R2(0)
            #print(l[8+2*i])
            #print(l[11+2*i+1])
            scoefs = str(l[11+2*i+1])
            scoefs = scoefs.replace('[', '')
            scoefs = scoefs.replace(']', '')
            scoefs = scoefs.replace(',', '')
            coefs = list(map(int, scoefs.split(' ')))
            #deg = len(coefs) - 1
            for i in range(len(coefs)) :
                univariate += X**i * coefs[i]
            params.append(univariate)
        lexGB = []
        for i in range(len(vars)-1) :
            lexGB.append(vars[i] + params[i+1](xelim))
        lexGB.append(params[0])
        return lexGB, vars



    
def sols_rational(file, R):
    try :
        lexGB, vars = FromMSolveRational(file, R)
    except :
        print("Failed to read file.")
        return []
    sols = []
    factors = lexGB[-1].factor()
    xelim = lexGB[-1].variables()[0]
    if len(factors) == 1 :
        return []
    R2 = PolynomialRing(R.base_ring(), 't')
    fill = [R2.gens()[0] for _ in range(len(R.gens()))]
    roots = lexGB[-1](fill).roots()
    print("roots:",roots)
    #X = list(vector(R.gens()))
    for r in roots :
        X = list(vector(R.gens()))
        eqs = [xelim-r[0]]
        for i in range(len(R.gens())):
            if X[i] == xelim :
                X[i] = r[0]
            #else :
            #    X[i] = 0
        sol = []
        for i in lexGB[:-1] :
            #print(i(X))
            if len(i(X).coefficients()) == 1 :
                sol.append(0)
            else :
                sol.append(-i(X).coefficients()[-1])
            #print(sol)
            #eqs.append(i(X))
        #V = Ideal(eqs).variety()[0]
        #y = list(vector(X)([V[i] for i in R.gens()]))
        sol.append(r[0])
        sols.append(sol)

    #Transformer la liste des solutions (ordonnee par msolve) en dictionnaire pour matcher la def
    #de variete de sage

    solutions =  [dict() for _ in sols]
    for i in range(len(sols)):
        for j in range(len(vars)) :
            solutions[i][vars[j]] = sols[i][j]

    return solutions

        
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

