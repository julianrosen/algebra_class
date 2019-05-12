from collections import defaultdict
from copy import copy
from IPython.display import display, Math, Latex

def not_implemented(*s):
    raise NotImplementedError
    return None

def print_tuple(s):
    """
    str(s) in a reasonable way
    """
    if len(s) == 1:
        T = "("+str(s[0])+")"
    else:
        T = str(s)
    return T.replace(' ','')


NI = not_implemented

class Algebra(Ring):
    def __init__(self,name,base,unit,init=lambda *s:{},mul=NI,is_inv=NI,inv=NI,rep=lambda s:'['+str(s)+']',\
                 tex=lambda s:'['+latex(s)+']',coer=lambda s:False,order=lambda s:0,is_basis_element=lambda s:True,\
                data={},self_tex=None):
        """
        Builds an algebra over base whose underlying module is free.
        Module basis can be indexed by any hashable items (b is basis element)
        Element of algebra is dictionary {b: coefficient}
        name: Name of the algebra
        base: Base ring
        unit: Hashable item representing 1
        init(*s) returns D (initializer)
        mul(b1,b2) returns dictionary {b:coefficient}
        is_inv(D) returns True if D gives invertible element, False otherwise
        inv(D) returns inverse of D
        rep(b) returns string representation of b
        latex(b) returns latex representation of b
        coer(S) return True if S has non-obvious coercion into this algebra, False otherwise (base always coerces)
        order(b) describes ordering of basis elements for display
        is_basis_element(b) returns True if b is a valid basis element, False otherwise
        """
        Ring.__init__(self,base)
        self._populate_coercion_lists_()
        self.init = init
        self.unit = unit
        self.mul = mul
        self.is_inv = is_inv
        self.inv = inv
        self.rep = rep
        self.coer = coer
        self.order = order
        self.tex = tex
        self.is_basis_element = is_basis_element
        self.data = dict(data)
        self.name = name
        self.self_tex = name if self_tex is None else self_tex
    
    def _repr_(self):
        return self.name
    
    def _latex_(self):
        return self.self_tex 
        
    def _element_constructor_(self,*s):
        return AlgebraElement(self,*s)
    
    def _coerce_map_from_(self,S):
        # Can coerce from rings that coerce into base
        if self.base().coerce_map_from(S) or parent(S) == parent(self) or self.coer(S):
            return True
        return False

class AlgebraElement(RingElement):
    def __init__(self,parent,*s):
        RingElement.__init__(self,parent)
        base = parent.base()
        if len(s) == 1:
            s = s[0]
            if s in parent.base():
                ss = base(s)
                self.D = defaultdict(lambda:base(0))
                if ss != 0:
                    self.D[parent.unit] = base(s)
                return None
            elif isinstance(s,type(parent.unit)):
                self.D = defaultdict(lambda:base(0))
                self.D[s] = base(1)
                return None
            elif isinstance(s,AlgebraElement):
                self.D = copy(s.D)
            elif isinstance(s,defaultdict):
                self.D = copy(s)
            elif isinstance(s,dict):
                self.D = defaultdict(lambda:base(0),dict(s))
            else:
                self.D = parent.init(s)
        else:
            self.D = parent.init(s)
        return None
    
    def _repr_(self):
        S = ""
        D = self.D
        if len(D) == 0:
            return "0"
        K = D.keys()
        K.sort(key=self.parent().order)
        for x in K:
            T = str(D[x]) + '*'
            rep = self.parent().rep(x)
            if T[0] != '-':
                T = '+' + T
            T = ' ' + T[0] + ' ' + T[1:]
            if len(T) == 5 and T[3] == '1' and rep != '':
                T = T[:3]
            if S == '':
                if T[1] == '+':
                    T = T[3:]
                elif T[1] == '-':
                    T = '-' + T[3:]
            if rep == '':
                T = T[:-1]
            S += T + rep
        return S
    
    def _latex_(self):
        S = ""
        D = self.D
        if len(D) == 0:
            return "0"
        K = D.keys()
        K.sort(key=self.parent().order)
        for x in K:
            T = str(latex(D[x]))
            rep = self.parent().tex(x)
            if T[0] != '-':
                T = '+' + T
            if len(T) == 2 and T[1] == '1' and rep != '':
                T = T[0]
            if S == '' and T[0] == '+':
                T = T[1:]
            if T == "+1":
                raise Exception
            S = S + T + rep
        return S
    
    def _add_(self,other):
        T = self.parent()(0)
        T.D = copy(self.D)
        for x in other.D:
            T.D[x] += other.D[x]
        T.red()
        return T
    
    def _sub_(self,other):
        T = self.parent()(0)
        T.D = copy(self.D)
        for x in other.D:
            T.D[x] -= other.D[x]
        T.red()
        return T
    
    def _mul_(self,other):
        T = self.parent()(0)
        for x in self.D:
            for y in other.D:
                D = self.parent().mul(x,y)
                for z in D:
                    T.D[z] += self.D[x] * other.D[y] * D[z]
        T.red()
        return T
    
    def is_inv(self):
        return self.parent().is_inv(self.D)
    
    def _inv_(self):
        if not self.is_inv():
            raise ValueError("Element not invertible")
        T = self.parent()(0)
        T.D = self.parent().inv(self.D)
        return T
    
    def _div_(self,other):
        return self * other._inv_()
    
    def _pow_(self,n):
        if n == 0:
            return self.parent()(1)
        elif n > 0:
            return self * self._pow_(n-1)
        else:
            return self._pow(-n)._inv_()
    
    def red(self):
        for x in self.D:
            if self.D[x] == self.parent().base()(0):
                self.D.pop(x)
        return self
    
    def disp(self):
        display(Math(latex(self)))
        return None