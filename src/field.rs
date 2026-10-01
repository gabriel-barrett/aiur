//! Canonical arithmetic for a runtime-selected prime of at most 64 bits.

#[derive(Clone, Copy, Debug)]
pub struct PrimeField {
    modulus: u64,
}

impl PrimeField {
    pub fn new(modulus: u64) -> Result<Self, String> {
        if !is_prime(modulus) {
            return Err(format!("field modulus {modulus} is not prime"));
        }
        Ok(Self { modulus })
    }

    pub fn modulus(self) -> u64 {
        self.modulus
    }
    pub fn contains(self, value: u64) -> bool {
        value < self.modulus
    }
    pub fn add(self, a: u64, b: u64) -> u64 {
        ((u128::from(a) + u128::from(b)) % u128::from(self.modulus)) as u64
    }
    pub fn sub(self, a: u64, b: u64) -> u64 {
        if a >= b {
            a - b
        } else {
            self.modulus - (b - a)
        }
    }
    pub fn neg(self, a: u64) -> u64 {
        if a == 0 { 0 } else { self.modulus - a }
    }
    pub fn mul(self, a: u64, b: u64) -> u64 {
        ((u128::from(a) * u128::from(b)) % u128::from(self.modulus)) as u64
    }
    pub fn inverse(self, a: u64) -> Option<u64> {
        (a != 0).then(|| self.pow(a, self.modulus - 2))
    }
    fn pow(self, mut base: u64, mut power: u64) -> u64 {
        let mut result = 1;
        while power != 0 {
            if power & 1 != 0 {
                result = self.mul(result, base);
            }
            base = self.mul(base, base);
            power >>= 1;
        }
        result
    }
}

fn is_prime(n: u64) -> bool {
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n == p {
            return true;
        }
        if n < 2 || n.is_multiple_of(p) {
            return false;
        }
    }
    // These Miller–Rabin bases cover the entire u64 range.
    let field = PrimeField { modulus: n };
    let shifts = (n - 1).trailing_zeros();
    let odd = (n - 1) >> shifts;
    for base in [2, 325, 9_375, 28_178, 450_775, 9_780_504, 1_795_265_022] {
        let base = base % n;
        if base == 0 {
            continue;
        }
        let mut x = field.pow(base, odd);
        if x == 1 || x == n - 1 {
            continue;
        }
        let mut passed = false;
        for _ in 1..shifts {
            x = field.mul(x, x);
            if x == n - 1 {
                passed = true;
                break;
            }
        }
        if !passed {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn arithmetic_at_word_boundary() {
        let p = 18_446_744_069_414_584_321;
        let f = PrimeField::new(p).unwrap();
        assert_eq!(f.add(p - 1, p - 1), p - 2);
        assert_eq!(f.mul(p - 1, p - 1), 1);
        assert_eq!(f.sub(0, p - 1), 1);
        assert_eq!(f.inverse(0), None);
        for a in [1, 2, 7, p - 2, p - 1] {
            assert_eq!(f.mul(a, f.inverse(a).unwrap()), 1);
        }
    }
    #[test]
    fn rejects_composites_including_pseudoprimes() {
        for n in [0, 1, 4, 561, 3_215_031_751, 341_550_071_728_321, u64::MAX] {
            assert!(PrimeField::new(n).is_err(), "{n}");
        }
        for n in [2, 3, 7, 97, 65_537, 18_446_744_073_709_551_557] {
            assert!(PrimeField::new(n).is_ok(), "{n}");
        }
    }
}
