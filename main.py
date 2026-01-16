from math import log2, ceil, sqrt
from utils_poly import get_random_primitive_binary_polynomials, bch_generator_poly, bytes_to_bits_poly_lsb, poly_divmod_gf2, poly_add_field, bits_to_bytes_poly_lsb, primitive_binary_polynomials, gf_mul, gf_make_tables, gf_inv

def param_from_kt(k: int, t): # à améliorer
    m = ceil(log2(k))
    n = pow(2,m) - 1

    while t > int((n-k)/m):
        m+=1
        n = pow(2,m) - 1

    return m, n, k, t

def param_from_kn(k, n):
    m: int = ceil(log2(n))
    t = int((n-k)/m)

    return m, n, k, t



class BCH:
    def __init__(self, m=None, n = None, k=None, t=None, prim_poly=None, calc_prim = True):
        self.m = m
        self.n = n
        self.k = k
        self.t = t
        self.prim_poly = prim_poly

        if self.m and not self.n:
            self.n = pow(2,m) - 1
        if self.n and not m:
            self.m = ceil(sqrt(n + 1))
            assert self.n <= pow(2,self.m) - 1



        if self.m is None and self.n is None and self.k is not None and self.t is not None: # si on a que k et t
            self.m,self.n,_,_=param_from_kt(self.k,self.t)
        elif self.k is not None and self.n is not None and self.t is None:
            self.m, _, _, self.t = param_from_kn(self.k,self.n)

        ## Vérification
        if not self.m or not self.n or not self.k or not self.t:
            raise Exception("Au moin 2 valeur doit être fournis entre m, k ou t")

        # print(f"[DEBUG] BCH(m={self.m}, n={self.n}, n_max={pow(2,self.m) - 1}, k={self.k}, t={self.t})")

        assert self.n <= pow(2,self.m) - 1
        assert self.t <= self.n//2, f"t is too large, take t <= {int((self.n-self.k)/self.m)}"
        assert self.t <= int((self.n-self.k)/self.m)

        if not self.prim_poly and calc_prim:
            self.find_prim()
            self.find_generator()

        # self.find_smallest_n()

    def __str__(self):
        return f"BCH(m={self.m}, n={self.n}, n_max={pow(2,self.m) - 1}, k={self.k}, t={self.t})"


    def find_smallest_n(self):
        while self.k < self.n - self.m * self.t:
            self.n -= 1
            # print(f"[DEBUG] Trying n={self.n}")
            if self.n < pow(2,self.m - 1):
                raise Exception("Impossible de trouver m plus petit")

    def find_prim(self):
        self.prim_poly = get_random_primitive_binary_polynomials(self.m) # TODO : do it my self
        print(self.prim_poly)

    def find_generator(self):  # TODO : do it my self
        g = bch_generator_poly(m=self.m, t=self.t,  prim=self.prim_poly)
        self.g = g
        self.deg_g = len(g) - 1
        self.n = self.deg_g + self.k



    def redondance_from_bytes(self, message: bytes):
        assert self.k/8 == self.k//8
        assert len(message)*8 == self.k, f"Le message n'est pas égal à k={self.k/8} octet"

        message = bytes_to_bits_poly_lsb(message)

        r = self.n - self.k

        work = [0]*r + message                          # = x^r * m(x) en low->high
        _, rem = poly_divmod_gf2(work, self.g)

        # pad ECC à r bits (low->high)
        if len(rem) < r:
            rem += [0] * (r - len(rem))

        return rem

    def check_from_bytes(self, message: bytes, ecc: list[int]) -> bool:
        """
        Retourne True si le mot est valide (aucune erreur détectée),
        False sinon.
        """
        assert self.k % 8 == 0
        assert len(message) * 8 == self.k

        msg_bits = bytes_to_bits_poly_lsb(message)
        r = self.n - self.k

        assert len(ecc) == r

        codeword = ecc + msg_bits      # c(x) = ecc + x^r m(x)

        _, rem = poly_divmod_gf2(codeword, self.g)

        # reste nul ?
        return all(b == 0 for b in rem)

    def guess_prim(self, message: bytes, ecc: list[int]):
        if self.prim_poly:
            raise Exception("Le polynôme primitif est déjà défini")
        for prim in primitive_binary_polynomials(self.m):
            g = bch_generator_poly(m=self.m, t=self.t,  prim=prim)

            _, rem = poly_divmod_gf2(ecc + bytes_to_bits_poly_lsb(message), g)

            if all(b == 0 for b in rem):
                print(f"[INFO] Found primitive polynomial: {bin(prim)}")
                return prim, g

        return None, None

    def _ensure_tables(self):
        if not hasattr(self, "exp") or not hasattr(self, "log"):
            self.exp, self.log = gf_make_tables(self.prim_poly, self.m)

    def _syndromes_from_bits(self, recv_bits: list[int]) -> list[int]:
        """
        Calcule S1..S_{2t} pour r(x) (bits low->high, positions 0..n-1),
        dans GF(2^m). Retourne liste length 2t, index 0->S1.
        """
        self._ensure_tables()
        n0 = (1 << self.m) - 1
        alpha = 0b10

        S = [0] * (2 * self.t)
        one_positions = [j for j, b in enumerate(recv_bits) if b & 1]

        for i in range(1, 2 * self.t + 1):
            acc = 0
            for j in one_positions:
                # terme = alpha^{i*j} (mod n0)
                e = (i * j) % n0
                acc ^= self.exp[e]
            S[i - 1] = acc

        return S

    def _bm_error_locator(self, S: list[int]) -> list[int]:
        """
        Berlekamp–Massey sur syndromes S1..S2t.
        Retourne sigma(x) = [1, s1, s2, ...] en coeffs GF(2^m), low->high.
        """
        self._ensure_tables()
        n0 = (1 << self.m) - 1

        # sigma = C, B dans l'algo BM
        C = [1] + [0] * (2 * self.t)
        B = [1] + [0] * (2 * self.t)
        L = 0
        m_shift = 1
        b = 1

        for n in range(0, 2 * self.t):
            # discrepancy d = S[n] + sum_{i=1..L} C[i]*S[n-i]
            d = S[n]
            for i in range(1, L + 1):
                if C[i] != 0 and S[n - i] != 0:
                    # d ^= C[i] * S[n-i]
                    a = C[i]
                    s = S[n - i]
                    d ^= gf_mul(a, s, self.prim_poly, self.m)

            if d == 0:
                m_shift += 1
                continue

            T = C[:]  # copie
            # coef = d / b = d * inv(b)
            invb = gf_inv(b, self.exp, self.log, self.m)
            coef = gf_mul(d, invb, self.prim_poly, self.m)

            # C = C + coef * x^{m_shift} * B
            for i in range(0, 2 * self.t + 1 - m_shift):
                if B[i] != 0:
                    C[i + m_shift] ^= gf_mul(coef, B[i], self.prim_poly, self.m)

            if 2 * L <= n:
                L = n + 1 - L
                B = T
                b = d
                m_shift = 1
            else:
                m_shift += 1

        # tronque à degré L
        return C[: L + 1]

    def _chien_search(self, sigma: list[int]) -> list[int]:
        """
        Trouve les positions d'erreurs via Chien search.
        Retourne la liste des positions j telles que sigma(alpha^{-j}) = 0.
        Positions j correspondent aux bits (low->high).
        """
        self._ensure_tables()
        n0 = (1 << self.m) - 1

        errs = []
        deg = len(sigma) - 1

        for j in range(n0):
            # évalue sigma(x) en x = alpha^{-j}
            # alpha^{-j} = alpha^{n0 - j}
            x = self.exp[(n0 - (j % n0)) % n0]

            acc = sigma[0]
            xpow = 1
            for i in range(1, deg + 1):
                xpow = gf_mul(xpow, x, self.prim_poly, self.m)  # x^i
                if sigma[i] != 0:
                    acc ^= gf_mul(sigma[i], xpow, self.prim_poly, self.m)

            if acc == 0:
                errs.append(j)

        return errs

    def correct_from_bytes(self, data: bytes, ecc: bytes) -> tuple[bytes, bytes, int]:
        """
        Corrige data+ecc si <= t erreurs.
        Entrées/Sorties bytes sont en convention "poly_lsb" (bit0=LSB).
        Retourne (data_corr, ecc_corr, nb_erreurs_corrigees).
        """
        assert self.k % 8 == 0
        assert len(data) * 8 == self.k

        r_bits_len = self.n - self.k
        assert len(ecc) * 8 == r_bits_len, f"ECC doit faire {r_bits_len//8} bytes"

        # bits low->high
        data_bits = bytes_to_bits_poly_lsb(data)
        ecc_bits = bytes_to_bits_poly_lsb(ecc)

        recv = ecc_bits + data_bits  # codeword low->high (ECC bas degrés, data hauts degrés)
        if len(recv) != self.n:
            raise ValueError("Longueur bits incohérente")

        # 1) syndromes
        S = self._syndromes_from_bits(recv)
        if all(x == 0 for x in S):
            # rien à corriger
            return data, ecc, 0

        # 2) sigma(x)
        sigma = self._bm_error_locator(S)
        L = len(sigma) - 1
        if L == 0:
            # syndromes non nuls mais sigma=1 -> incohérent
            raise RuntimeError("Décodage échoué (sigma degré 0 mais syndromes non nuls)")

        if L > self.t:
            raise RuntimeError(f"Trop d'erreurs pour corriger: deg(sigma)={L} > t={self.t}")

        # 3) positions erreurs (sur parent n0, mais on ne corrige que celles < n)
        err_pos_all = self._chien_search(sigma)

        # BCH binaire: le nombre d'erreurs = deg(sigma) si tout va bien
        # (on filtre celles qui sont hors de notre code raccourci n)
        err_pos = [j for j in err_pos_all if j < self.n]

        if len(err_pos) != L:
            # souvent signe d'erreurs > t ou d'un mismatch de conventions (bit order / prim_poly)
            raise RuntimeError(
                f"Décodage incohérent: trouvé {len(err_pos)} positions, attendu {L}. "
                "Vérifie swap_bits/invert/endian + prim_poly."
            )

        # 4) correction (flip des bits)
        for j in err_pos:
            recv[j] ^= 1

        # recoupe
        ecc_corr_bits = recv[:r_bits_len]
        data_corr_bits = recv[r_bits_len:]

        # repack
        ecc_corr = bits_to_bytes_poly_lsb(ecc_corr_bits)
        data_corr = bits_to_bytes_poly_lsb(data_corr_bits)

        return data_corr, ecc_corr, len(err_pos)




if __name__ == "__main__":
    bch = BCH(k=8224,n=8448)
    print(bch)

    bch = BCH(k=8224,t=16)
    print(bch)
    print(8224/8)
    message = b"a"*(8224//8)
    redondance : list[int] = bch.redondance_from_bytes(message)

    assert bch.check_from_bytes(message, redondance)

    bch_without_prim = BCH(k=8224,t=16, calc_prim=False)
    prim, g = bch_without_prim.guess_prim(message, redondance)
    assert prim == bch.prim_poly

if __name__ == "__main__":
    bch = BCH(k=8224, t=16)  # si tu connais prim_poly (comme bchlib)
    data = b"a" * (8224 // 8)

    # ECC calculé par TON encodeur
    ecc_bits = bch.redondance_from_bytes(data)
    ecc = bits_to_bytes_poly_lsb(ecc_bits)

    # Injecte 1 erreur
    data_bad = bytearray(data)
    data_bad[0] ^= 0x01  # flip 1 bit

    data_bad[11] ^= 0x01  # flip 1 bit
    data_bad[15] ^= 0x01  # flip 1 bit
    data_bad[16] ^= 0x01  # flip 1 bit

    data_corr, ecc_corr, nfix = bch.correct_from_bytes(bytes(data_bad), ecc)
    print("corrigé:", nfix, data_corr == data)
