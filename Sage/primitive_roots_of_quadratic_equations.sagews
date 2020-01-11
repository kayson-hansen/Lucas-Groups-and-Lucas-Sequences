def first_root_checker(p):
    vals = []
    for x in range(2, p):
        if Mod(x,p).multiplicative_order() == p-1:
            vals.append((x + Integer(x).inverse_mod(p)) % p)
    return list(set(vals))

#implements a binary operation between Lucas Groups
def bin_op(x1, x2, y1, y2, p, D):
    return ((x1*y1+D*x2*y2) % p, (x1*y2+x2*y1) % p)

#generates all the primitives
def primitive_generator(p, D):
    primitives = []
    for a1 in range(1, p):
        for a2 in range(1, p):
            a = (a1, a2)
            a0 = a
            order = 0
            for i in range(2, p^2):
                a = bin_op(a[0], a[1], a0[0], a0[1], p, D)
                if a == (1,0):
                    order = i
                    break
            if order == p^2-1:
                primitives.append(a0)
    return primitives

def second_root_checker(a, p):
    a1 = a[0]
    a2 = a[1]
    return (a1*Integer(a2).inverse_mod(p)-2) % p

def intersect(a, b):
    """ return the intersection of two lists """
    return list(set(a) & set(b))

for p in range(3, 100):
    if p in Primes():
        print "p: %d" %p, "\n"
        x = first_root_checker(p)
        print 1, len(x)
        vals = [1]
        for P in range(1, p):
            D = (P^2-4)%p
            if legendre_symbol(D, p) == -1:
                generators = primitive_generator(p, D)
                vals = []
                for i in generators:
                    ratio = second_root_checker(i, p)
                    if ratio not in vals:
                        vals.append(ratio)
                vals.sort()
                print P, vals
        print intersect(x, vals)
        print "\n\n"









