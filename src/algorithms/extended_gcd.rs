/// Returns the largest positive integer that divides `a` and `b` without
/// leaving a remainder, as well as the coefficients of [Bézout's Identity],
/// using the [Euclidean Algorithm].
///
/// The coefficients of Bézout's identity are integers `x` and `y` such that:
///
/// ```text
///      ax + by = gcd(a,b)
/// ```
///
/// One important application of Extended Euclidean Algorithm is in finding
/// `modular inverses`.
///
/// [Bézout's Identity]: https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity
/// [Euclidean Algorithm]: https://en.wikipedia.org/wiki/Euclidean_algorithm
pub fn extended_gcd(mut a: usize, mut b: usize) -> (usize, isize, isize) {
    // If `b` is 0, the GCD is `a`. This is because every number divides 0, but
    // only the divisors of `a` divide `a`. So, the only common divisors between
    // `a` and 0 are the divisors of `a` itself.
    //
    // The coefficients of `1` and `0` satisfy the equation:
    //
    //      ax + by = gcd(a,b)
    //
    //              |
    //              V
    //
    //       a(1) + b(0) = a
    //          a + 0 = a
    //            a = a
    if b == 0 {
        return (a, 1, 0);
    }

    let (mut x0, mut y0): (isize, isize) = (1, 0); // Coefficients for `a`.
    let (mut x1, mut y1): (isize, isize) = (0, 1); // Coefficients for `b`.

    while b > 0 {
        // The Euclidean algorithm is based on the principle that the GCD of two
        // numbers does not change if the larger number is replaced by its
        // difference with the smaller number.
        //
        // Later improved upon to also include:
        //
        //      `GCD(a, b) = GCD(b, a % b)`
        //
        // These steps replace `a` with `b`, and `b` with `a % b`. By applying
        // this iteratively, we progressively reduce the problem, with each
        // iteration bringing us closer to the base case of `b == 0`. When this
        // is reached, the current value of `a` will be the GCD.
        let q = (a / b) as isize;
        let r = a % b;

        let tmp = (x1, y1);

        // Update coefficients.
        x1 = x0 - q * x1;
        y1 = y0 - q * y1;

        // Store previous coefficients of `b`.
        (x0, y0) = tmp;

        a = b;
        b = r;
    }

    (a, x0, y0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn gcd_extended_assert(
        a: usize,
        b: usize,
        expected_gcd: usize,
        expected_x: isize,
        expected_y: isize,
    ) {
        let (gcd, x, y) = extended_gcd(a, b);

        assert_eq!(gcd, expected_gcd, "gcd failed for {} and {}", a, b);
        assert_eq!(x, expected_x, "coefficient x failed for {} and {}", a, b);
        assert_eq!(y, expected_y, "coefficient y failed for {} and {}", a, b);
    }

    #[test]
    fn test_extended() {
        gcd_extended_assert(30, 12, 6, 1, -2);
        gcd_extended_assert(48, 18, 6, -1, 3);
        gcd_extended_assert(56, 15, 1, -4, 15);
        gcd_extended_assert(101, 10, 1, 1, -10);
        gcd_extended_assert(1, 1, 1, 0, 1);
        gcd_extended_assert(0, 10, 10, 0, 1);
        gcd_extended_assert(987654321, 123456789, 9, 1, -8);
    }
}
