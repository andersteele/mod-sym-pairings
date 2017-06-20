from sage.modular.pollack_stevens.space import ps_modsym_from_elliptic_curve, ps_modsym_from_simple_modsym_space, Symk
from sage.modular.arithgroup.arithgroup_element import ArithmeticSubgroupElement

class TwoCocycle(SageObject):
    """
    2-Cocycle class for congruence subgroups of SL_2(Z) with level N
    
    f = a function SL_2(Z)\times SL_2(Z) -> M
    
    """
    def __init__(self, f, N):
        self._f = f
        self._N = N
    def __call__(self, A, B):
        if not isinstance(A, ArithmeticSubgroupElement):
            A = Gamma0(self._N)(A)
        if not isinstance(B, ArithmeticSubgroupElement):
            B = Gamma0(self._N)(B)
        return self._f(A,B)
    def find_boundary(self):
        def compute_u(A):
            F = SL2Z.farey_symbol()
            gens = F.generators()
            gensi = [~g for g in gens]
            s, r = gens # [0,-1,1,0] and [0,-1,1,-1]
            si, ri = gensi
            us = 1/2*self(s,s)
            ur = 1/3*self(r,r) + 1/3*self(r,r^2)
            W = F.word_problem(A)
            scount = W.count(1) - W.count(-1)
            rcount = W.count(2) - W.count(-2)
            total = W.count(1) * us + W.count(-1) * (self(s,si) - us) + W.count(2) * ur + W.count(-2) * (self(r,ri) - ur)
            B = A
            for i in W[:-1]:
                g = gens[i-1] if i > 0 else gens[-i-1]
                gi = gensi[i-1] if i > 0 else gensi[-i-1]
                B = gi * B
                total -= self(g, B)
            return total
        return OneCochain(compute_u,self._N)
    def derivative(self):
        return ThreeCochain(lambda A, B, C: -self(A, B) + self(A, B*C) - self(A*B, C) + self(B, C),self._N)
    def __add__(self, other):
        return TwoCocycle(lambda A, B: self(A,B) + other(A,B),self._N)
    def __sub__(self, other):
        return TwoCocycle(lambda A, B: self(A,B) - other(A,B),self._N)
    def check_cocycle(self,trials=5,size=100):
        dself = self.derivative()
        for trial in range(trials):
            L = []
            for mat in range(3):
                c = ZZ.random_element(1,size) * (1-2*ZZ.random_element(2)) * self._N
                d = (ZZ.random_element(1,size) * (1-2*ZZ.random_element(2))).val_unit(self._N)[1]
                g, a, b = d.xgcd(c)
                c = c // g
                d = d // g
                b=-b
                L.append(matrix(ZZ,2,2,[a,b,c,d]))
            if dself(*L) != 0:
                raise ValueError("Not a cocylce!")
        print "Cocycle checks out okay in %s trials"%(trials)

class ThreeCochain(SageObject):
    def __init__(self, f, N):
        self._f = f
        self._N = N
    def __call__(self, A, B, C):
        if not isinstance(A, ArithmeticSubgroupElement):
            A = Gamma0(self._N)(A)
        if not isinstance(B, ArithmeticSubgroupElement):
            B = Gamma0(self._N)(B)
        if not isinstance(C, ArithmeticSubgroupElement):
            C = Gamma0(self._N)(B)
        return self._f(A,B,C)

class OneCochain(SageObject):
    def __init__(self, f, N):
        self._f = f
        self._N = N
    def __call__(self, A):
        if not isinstance(A, ArithmeticSubgroupElement):
            A = Gamma0(self._N)(A)
        return self._f(A)
    def derivative(self):
        return TwoCocycle(lambda A, B: self(A) + self(B) - self(A*B), self._N)

    
def parabolic(Phi):
    """
    Returns the (parabolic) 1-cocyle obtained by projection to group cohomology
    
    Argument:
    Phi -- A modular symbol
    """
    #TO DO: add this method if useful
    return None
    
def cup_product(Phi,Psi, pairing):
    """
    Computes the cup product (as a 2-cocycle) of two modular symbols of level N.
    
    Returns a TwoCocycle object
    
    Arguments:
    
    Phi, Psi -- Modular symbols for Gamma0(N) with coefficients in a module M
    pairing --  an inner product on the module M with values in a trivial Gamma0(N)-module
    """
    #this computes the corestriction to SL_2(Z) of the cup product of Phi, Psi. This is given by
    # cor \Phi\cup \Psi (\alpha,\beta)=sum_{g in SL_2 / Gamma} Phi(g r,g\alpha r)\otimes Psi(g\alpha r, g\alpha\beta r)
    # where g runs over coset representatives of Gamma in SL_2(Z)

    N = Psi.parent().source().level()
    W = matrix(ZZ,2,2,[0,-1,N,0])
    assert Phi.parent().source().level() == N #check that the modular symbols share the same level
    coset_reps = list(Gamma0(N).coset_reps()) #We stick to Gamma0(N) for now
    f = lambda A, B: sum([pairing(Phi._map(matrix(ZZ,[g.matrix()*r,g.matrix()*A.matrix()*r]).transpose()),
                                 Psi._map(matrix(ZZ,[W*g.matrix()*A.matrix()*r,W*g.matrix()*A.matrix()*B.matrix()*r]).transpose())) 
                         for g in coset_reps])
    return TwoCocycle(f,1)

def inner(Phi,Psi, pairing):
    N=Phi.parent().source().level()
    A = matrix(ZZ,2,2,[1,1,0,1]) #generator of the parabolic
    parsum=cup_product(Phi,Psi,pairing).find_boundary()(A)
    return parsum

def symk_pairing(a, b, N = 1, twist = True):
    k = a.parent().weight()
    assert b.parent().weight() == k
    if twist:
        pair=sum(N^i*a.moment(i) * b.moment(i) * binomial(k,i) for i in xrange(k+1))
    else:
        pair=sum((-1)^i*a.moment(i) * b.moment(k-i) * binomial(k,i) for i in xrange(k+1)) 
    return pair

def overconvergent_pairing(a, b, N = 1):
    #pairing only defined if twisted
    k = a.parent().weight()
    p = a.parent()._p
    assert b.parent().weight() == k
    pair = sum([(-1)^k*(N*p)^i*binomial(k,i)*a.moment(i)*b.moment(i) for i in xrange(k+1)])
    return pair

def choose_series(n,K,prec_w):
    #returns a polynomial approximation to the power series binomial(log(1+wp)/log(1+p) n)
    #w = ((1+p) ** k - 1) / p
    # k choose i replaced by log_p(1+pw)/log_p(1+p) choose i
    p = K.prime()
    R.<w> = PolynomialRing(K)
    log_poly = sum([ ((-1)**(i-1) * (p*w) ** i)/i for i in [1..prec_w] ])/K(1+p).log()
    prod = 1/factorial(n)
    for i in range(n): 
        prod *= (log_poly - i)
    return prod

def family_pairing(a, b, N=1):
    #repalce binomial(k, i) with "binomial"(log(1+wp)/log(gamma), i)
    p = a.parent()._p
    K = a.base_ring().base_ring()
    prec = a.precision_absolute()[0]
    pair = sum([(N*p)^i*choose_series(i,K,prec)*a.moment(i)*b.moment(i) for i in xrange(prec+1)])
    return pair
