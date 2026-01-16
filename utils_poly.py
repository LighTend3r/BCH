from random import choice

def prime_factorization(n):
    fac = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            fac.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        fac.append(n)
    return fac


def poly_mod(a, mod):
    d_a = a.bit_length() - 1
    d_m = mod.bit_length() - 1
    while a and d_a >= d_m:
        a ^= mod << (d_a - d_m)
        d_a = a.bit_length() - 1
    return a


def poly_mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
    return result


def poly_gcd(a, b):
    while b:
        a, b = b, poly_mod(a, b)
    return a


def poly_pow_mod(x, e, mod):
    res = 1
    while e:
        if e & 1:
            res = poly_mod(poly_mul(res, x), mod)
        x = poly_mod(poly_mul(x, x), mod)
        e >>= 1
    return res


def is_reducible(fx):
    degree = fx.bit_length() - 1
    x = 2
    y = x
    for _ in range(degree // 2 + 1):
        y = poly_mod(poly_mul(y, y), fx)
        y_minus_x = y ^ x
        if poly_gcd(y_minus_x, fx) != 1:
            return False

    for _ in range(degree // 2 + 1, degree):
        y = poly_mod(poly_mul(y, y), fx)
    return y == x


def primitive_binary_polynomials(degree):
    n = 2**degree - 1
    prime_factors = set(prime_factorization(n))
    x = 2

    for fx in range(2**degree + 1, 2 ** (degree + 1), 2):
        # check irreducible
        if not is_reducible(fx):
            continue

        # check primitive
        for q in prime_factors:
            if poly_pow_mod(x, n // q, fx) == 1:
                break
        else:
            yield fx


def get_random_primitive_binary_polynomials(degree):
    all_primitive_binary_polynomials = [ px for px in primitive_binary_polynomials(degree) ]

    return choice(all_primitive_binary_polynomials)





from math import gcd




def gf_mul(a: int, b: int, prim: int, m: int) -> int:
    """Multiplication dans GF(2^m) (bitset), modulo prim (bitmask de p(x))."""
    res = 0
    while b:
        if b & 1:
            res ^= a
        b >>= 1
        a <<= 1
        if a >> m:          # dépassement du degré m-1
            a ^= prim       # réduction modulo p(x)
    return res & ((1 << m) - 1)

def gf_pow(a: int, e: int, prim: int, m: int) -> int:
    """a^e dans GF(2^m)."""
    res = 1
    while e:
        if e & 1:
            res = gf_mul(res, a, prim, m)
        a = gf_mul(a, a, prim, m)
        e >>= 1
    return res

def coset(i: int, n0: int) -> list[int]:
    """Coset cyclotomique de i modulo n0."""
    out, seen = [], set()
    x = i % n0
    while x not in seen:
        seen.add(x)
        out.append(x)
        x = (2 * x) % n0
    return out

def poly_add_field(p: list[int], q: list[int]):
    if len(q) > len(p):
        q,p=p,q

    r = p[:]

    for i in range(len(q)):
        r[i] = p[i] ^ q[i]

    return r



def poly_mul_field(p: list[int], q: list[int], prim: int, m: int) -> list[int]:
    """Produit de polynômes dont les coefficients sont dans GF(2^m). (coeffs low->high)"""
    r = [0] * (len(p) + len(q) - 1)
    for i, ai in enumerate(p):
        if ai == 0:
            continue
        for j, bj in enumerate(q):
            if bj == 0:
                continue
            r[i + j] ^= gf_mul(ai, bj, prim, m)  # + = XOR
    return r

def minimal_poly_from_coset(C: list[int], prim: int, m: int) -> list[int]:
    """
    Construit M_C(x)=∏_{j∈C}(x+α^j).
    Retourne une liste de coeffs dans GF(2) (low->high).
    """
    n0 = (1 << m) - 1
    alpha = 0b10  # élément 'x'
    poly = [1]    # polynôme 1 dans GF(2^m)[x]

    for j in C:
        a = gf_pow(alpha, j % n0, prim, m)     # α^j dans GF(2^m)
        poly = poly_mul_field(poly, [a, 1], prim, m)  # (a + x)

    # Les coeffs doivent retomber dans {0,1}
    out = []
    for c in poly:
        if c == 0:
            out.append(0)
        elif c == 1:
            out.append(1)
        else:
            raise ValueError(
                f"Coefficient {c} ∉ GF(2). "
                "Vérifie prim (irréductible/primitif) et la définition de α."
            )
    return out  # coeffs GF(2)

def poly_mul_gf2(p: list[int], q: list[int]) -> list[int]:
    """Produit dans GF(2)[x], coeffs low->high."""
    r = [0] * (len(p) + len(q) - 1)
    for i, ai in enumerate(p):
        if ai:
            for j, bj in enumerate(q):
                if bj:
                    r[i + j] ^= 1
    return r

def poly_divmod_gf2(a: list[int], b: list[int]) -> tuple[list[int], list[int]]:
    """Division euclidienne dans GF(2)[x]. Retourne (quotient, reste)."""
    a = a[:]
    # normalise
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    while len(b) > 1 and b[-1] == 0:
        b.pop()

    da, db = len(a) - 1, len(b) - 1
    if db < 0 or (len(b) == 1 and b[0] == 0):
        raise ZeroDivisionError
    if da < db:
        return [0], a

    q = [0] * (da - db + 1)
    r = a
    for k in range(da - db, -1, -1):
        if r[db + k]:
            q[k] = 1
            for j in range(db + 1):
                r[j + k] ^= b[j]
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return q, r

def poly_gcd_gf2(a: list[int], b: list[int]) -> list[int]:
    """PGCD dans GF(2)[x]."""
    # normalise
    def norm(p):
        p = p[:]
        while len(p) > 1 and p[-1] == 0:
            p.pop()
        return p
    a, b = norm(a), norm(b)
    while not (len(b) == 1 and b[0] == 0):
        _, r = poly_divmod_gf2(a, b)
        a, b = b, r
    return a

def poly_lcm_gf2(a: list[int], b: list[int]) -> list[int]:
    """PPCM dans GF(2)[x]."""
    g = poly_gcd_gf2(a, b)
    # a*b/g : on divise (a*b) par g
    ab = poly_mul_gf2(a, b)
    q, r = poly_divmod_gf2(ab, g)
    assert r == [0]
    return q

def bch_generator_poly(m: int, t: int, prim: int) -> list[int]:
    """Renvoie g(x) (coeffs GF(2) low->high) pour BCH narrow-sense longueur n0=2^m-1."""
    n0 = (1 << m) - 1
    seen_cosets = set()
    g = [1]  # polynôme 1

    for i in range(1, 2 * t + 1):
        C = tuple(coset(i, n0))
        # canonise le coset : on prend la rotation commençant par son min (juste pour dédupliquer)
        mn = min(C)
        k = C.index(mn)
        Ccanon = C[k:] + C[:k]
        if Ccanon in seen_cosets:
            continue
        seen_cosets.add(Ccanon)

        Mi = minimal_poly_from_coset(list(Ccanon), prim, m)
        g = poly_lcm_gf2(g, Mi)

    return g

def poly_to_string_gf2(p: list[int]) -> str:
    terms = []
    for k, c in enumerate(p):
        if c == 0:
            continue
        if k == 0:
            terms.append("1")
        elif k == 1:
            terms.append("x")
        else:
            terms.append(f"x^{k}")
    return " + ".join(reversed(terms)) if terms else "0"

def gf_make_tables(prim: int, m: int):
    """
    Construit exp/log pour GF(2^m) avec alpha = 0b10 (x).
    exp[i] = alpha^i
    log[a] = i tel que a = alpha^i (log[0] inutilisé)
    """
    n0 = (1 << m) - 1
    exp = [0] * (2 * n0)      # on double pour éviter le modulo dans les produits
    log = [0] * (1 << m)

    alpha = 0b10
    x = 1
    for i in range(n0):
        exp[i] = x
        log[x] = i
        x = gf_mul(x, alpha, prim, m)

    # duplication
    for i in range(n0, 2 * n0):
        exp[i] = exp[i - n0]

    return exp, log

def gf_inv(a: int, exp: list[int], log: list[int], m: int) -> int:
    """Inverse multiplicatif dans GF(2^m) via tables."""
    if a == 0:
        raise ZeroDivisionError("inverse(0) n'existe pas")
    n0 = (1 << m) - 1
    return exp[(n0 - log[a]) % n0]


def bytes_to_bits_poly_lsb(data: bytes) -> list[int]:
    bits = []
    for b in data:
        for i in range(8):  # LSB -> MSB
            bits.append((b >> i) & 1)
    return bits

def bits_to_bytes_poly_lsb(bits: list[int]) -> bytes:
    if len(bits) % 8 != 0:
        raise ValueError("La longueur des bits doit être multiple de 8")

    out = bytearray()
    for i in range(0, len(bits), 8):
        b = 0
        for j in range(8):  # bit j = 2^j
            b |= (bits[i + j] & 1) << j
        out.append(b)
    return bytes(out)

if __name__ == "__main__":
    m = 14
    print(f"All primitive polynomials of degree {m}:")

    i = 0
    for px in primitive_binary_polynomials(m):
        i += 1
        print(f"{px} = {bin(px)}")

    print(f"Total primitive polynomials of degree {m}: {i}")

if __name__ == "__main__":
    m = 4
    t = 2
    prim = 0b10011  # x^4 + x + 1
    g = bch_generator_poly(m, t, prim)
    print(g)                       # coeffs low->high
    print(poly_to_string_gf2(g))   # forme lisible
