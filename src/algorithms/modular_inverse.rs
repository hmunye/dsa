use super::extended_gcd::extended_gcd;

/// Returns the modular inverse of `a` under modulus `m`, or [`None`] if it
/// does not exist.
///
/// The modular inverse of `a` is the number `x` such that:
///
/// ```text
///     a * x ≡ 1 (mod m)
/// ```
///
/// Used in cryptography (e.g., RSA), digital signatures, and hashing functions.
pub fn modular_inverse(a: usize, m: usize) -> Option<usize> {
    // Uses the `Extended Euclidean Algorithm` to find the modular inverse, if
    // it exists. The modular inverse of `a` under modulus `m` is the value `x`
    // such that:
    //
    //     a * x ≡ 1 (mod m)
    //
    let (gcd, x, _) = extended_gcd(a, m);

    // If the GCD of `a` and `m` != 1, it means `a` and `m` are not `coprime`
    // (relatively prime to each other), so no modular inverse exists.
    if gcd != 1 {
        return None;
    }

    // If gcd(a, m) is 1, it means `a` and `m` are coprime, so a modular inverse
    // exists. The value `x` is the coefficient of `a` in the equation
    // `a * x + m * y = gcd(a, m)`, which gives us the modular inverse of `a`
    // modulo `m` (a * x ≡ 1 mod m). We also need to normalize `x` within the
    // range `0..m` by taking `x % m`, to ensure the result remains within
    // bounds. Ensure a negative coefficient is converted to a positive value.
    Some(((x % m as isize) + m as isize) as usize % m)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inverse_exists() {
        let result = modular_inverse(3, 7);
        assert_eq!(result, Some(5));

        let result = modular_inverse(11, 26);
        assert_eq!(result, Some(19));

        let result = modular_inverse(10, 17);
        assert_eq!(result, Some(12));

        let result = modular_inverse(1, 1);
        assert_eq!(result, Some(0));
    }

    #[test]
    fn test_inverse_not_exists() {
        let result = modular_inverse(6, 9);
        assert_eq!(result, None);

        let result = modular_inverse(8, 12);
        assert_eq!(result, None);

        let result = modular_inverse(0, 5);
        assert_eq!(result, None);
    }
}
