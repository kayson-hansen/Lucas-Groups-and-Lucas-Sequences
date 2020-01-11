        for i in generators:
            if i == (P,1):
                generator = i
                break
            else:
                first_gen = i
                new_gen = first_gen
                for j in range(2, new_order/lucas_sequence(P,p,D)+1):
                    new_gen = bin_op(new_gen, first_gen, D, p)
                if new_gen == (P,1):
                    generator = first_gen
                    break
        try:
            test = generator
        except UnboundLocalError:
            generator = choice(generators)


 if (x,y) == (P,1):
                    generator = (x,y)
                else:
                    first_gen = (x,y)
                    new_gen = first_gen
                    for i in range(2, len(elements(D,p))/lucas_sequence(P,p,D)+1):
                        new_gen = bin_op(new_gen, first_gen, D, p)
                    if new_gen == (P,1):
                        generator = first_gen


for i in generators:
            if i == (P,1):
                generator = i
                break
            else:
                first_gen = i
                new_gen = first_gen
                for i in range(2, len(elements(D,p))/lucas_sequence(P,p,D)+1):
                    new_gen = bin_op(new_gen, first_gen, D, p)
                if new_gen == (P,1):
                    generator = first_gen
                    break


#for jacobi_symbol = 1
def gen_powers(p, P):
    if not is_prime_power(p):
        f = factor(P)
        generators = OrderedDict()
        for divisor in f:
            generators[divisor] = []
            prime_power = divisor[0]**divisor[1]
            orders = []
            for a in range(2, p):
                if order(a,p) == euler_phi(p):
                    generators[divisor].append(gen_order(p, a, P)[0])
                    orders.append(gen_order(p, a, P)[1])
        generator_tuples = list(product(*generators.values()))
        new_gens = []
        for i in generator_tuples:
            solution = crt(i[0], i[1], f[0][0]**f[0][1], f[1][0]**f[1][0])
            modulus = f[0][0]**f[0][1] * f[1][0]**f[1][0]
            for j in range(1, len(f)-1):
                solution = crt(solution, i[j+1], modulus, f[j+1][0]**f[j+1][0])
                modulus *= f[j+1][0]
            new_gens.append(solution)
        return [new_gens, orders]
    orders = []
    generators = []
    for a in range(2, p):
        if order(a,p) == euler_phi(p):
            data = gen_order(p, a, P)
            generators.append(data[0])
            orders.append(data[1])
    return [generators, orders]


#for jacobi_symbol = -1
def gen_homo(p, P, D):
    generators = []
    orders = []
    for generator in primitive_test(p, D):
        a = generator[0]
        b = generator[1]
        norm = Mod(a**4+D**2*b**4-2*D*a**2*b**2, p).sqrt()
        new_gen = ((a**2+D*b**2)*(Integer(norm).inverse_mod(p)) % p, (2*a*b)*(Integer(norm).inverse_mod(p)) % p)
        new_gen = (2*new_gen[0] % p, 2*new_gen[1] % p)
        if new_gen not in generators:
            if gen_test(new_gen, D, p) == True:
                generators.append(new_gen)
            #this part handles when p - \epsilon(p) = 2 mod 4, because the sqrt could be negative, causing the order to halve
            elif gen_test(new_gen, D, p) == "Almost":
                generators.append((-new_gen[0] % p, -new_gen[1] % p))
    for generator in generators:
        new_element = generator
        order_P = 0
        if generator == (P,1):
            order_P = 1
            orders.append(order_P)
            continue
        for i in range(2, p+2):
            new_element = bin_op(generator, new_element, D, p)
            if new_element == (P,1):
                order_P = i
                break
        orders.append(order_P)
    return [generators, orders]


#lucas group primality testing
#for composite p, if the Lucas Sequence is not contained in any cyclic subgroup, choose a random generator
def luc_group_test(P, D, p):
    if p not in Primes() and not is_prime_power(p):
        f = factor(p)
        new_order = 1
        for i in f:
            new_order = lcm(new_order, len(elements(D,i[0]**i[1])))
        solutions = elements(D, p)
        generators = []
        for i in solutions:
            if gen_test(i, D, p) == True:
                generators.append(i)
        #testing if a random generator still works
        generator = choice(generators)
    elif p in Primes() and jacobi_symbol(D, p) == 1:
        generators = []
        for a in range(2, p):
            if order(a,p) == euler_phi(p):
                (x,y) = ((a+Integer(a).inverse_mod(p)) % p, (a-Integer(a).inverse_mod(p))*(Integer(Mod(D, p).sqrt()).inverse_mod(p)) % p)
                generators.append((x,y))
        #testing if a random generator still works
        generator = choice(generators)
    elif p in Primes() and jacobi_symbol(D, p) == -1:
        generators = []
        for generator in primitive_test(p, D):
            a = generator[0]
            b = generator[1]
            norm = Mod(a**4+D**2*b**4-2*D*a**2*b**2, p).sqrt()
            new_gen = ((a**2+D*b**2)*(Integer(norm).inverse_mod(p)) % p, (2*a*b)*(Integer(norm).inverse_mod(p)) % p)
            new_gen = (2*new_gen[0] % p, 2*new_gen[1] % p)
            if new_gen not in generators:
                if gen_test(new_gen, D, p) == True:
                    generators.append(new_gen)
                #this part handles when p - \epsilon(p) = 2 mod 4, because the sqrt could be negative, causing the order to halve
                elif gen_test(new_gen, D, p) == "Almost":
                    generators.append((-new_gen[0] % p, -new_gen[1] % p))
        #testing if a random generator still works
        generator = choice(generators)
    else:
        return 0
    try:
        element = generator
    except UnboundLocalError:
        return True
    f = list(factor(p-jacobi_symbol(D, p)))
    s = 0
    for j in f:
        if j[0] == 2:
            s = j[1]
            break
    q = (p-jacobi_symbol(D, p))/2**s
    lucas_group = [generator]
    for i in range(2, p-jacobi_symbol(D, p)+1):
        element = bin_op(generator, element, D, p)
        lucas_group.append(element)
    if lucas_group[q-1][1] == 0:
        return True
    else:
        for r in range(0, s):
            if lucas_group[q*2**r-1][0] == 0:
                return True
    return False


def lucas_sequence_polys(p):
    if is_prime(p):
        F = GF(p)
        R.<P> = PolynomialRing(F)
        polys = [(2,0), (P,1)]
        for i in range(0, p+2):
            polys.append((P*polys[-1][0]-polys[-2][0], P*polys[-1][1]-polys[-2][1]))
        factored_polys = [(2,0), (P,1)]
        for index, polynomial in enumerate(polys):
            if index > 1 and index < p + 2:
                #if (polynomial[0]-2).is_irreducible() or polynomial[1].is_irreducible():
                #    print polynomial, index
                factored_polys.append(((polynomial[0]-2).factor(), polynomial[1].factor()))
        return factored_polys
    else:
         pass









