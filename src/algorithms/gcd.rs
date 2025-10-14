/// Returns the largest positive integer that divides `x` and `y` without
/// leaving a remainder, using the [Euclidean Algorithm].
///
/// [Euclidean Algorithm]: https://en.wikipedia.org/wiki/Euclidean_algorithm
pub fn gcd(mut x: usize, mut y: usize) -> usize {
    // If `y` is 0, the GCD is `x`. This is because every number divides 0, but
    // only the divisors of `x` divide `x`. So, the only common divisors between
    // `x` and 0 are the divisors of `x` itself.
    if y == 0 {
        return x;
    }

    while y > 0 {
        // The Euclidean algorithm is based on the principle that the GCD of two
        // numbers does not change if the larger number is replaced by its
        // difference with the smaller number.
        //
        // Later improved upon to also include:
        //
        //      `GCD(x, y) = GCD(y, x % y)`
        //
        // These steps replace `x` with `y`, and `y` with `x % y`. By applying
        // this iteratively, we progressively reduce the problem, with each
        // iteration bringing us closer to the base case of `y == 0`. When this
        // is reached, the current value of `x` will be the GCD.
        let tmp = x;
        x = y;
        y = tmp % y;
    }

    x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        assert_eq!(gcd(48, 18), 6);
        assert_eq!(gcd(54, 24), 6);
        assert_eq!(gcd(101, 10), 1);
    }

    #[test]
    fn test_zero() {
        assert_eq!(gcd(0, 5), 5);
        assert_eq!(gcd(10, 0), 10);
        assert_eq!(gcd(0, 0), 0);
    }

    #[test]
    fn test_duplicate() {
        assert_eq!(gcd(7, 7), 7);
        assert_eq!(gcd(100, 100), 100);
    }

    #[test]
    fn test_one() {
        assert_eq!(gcd(1, 99), 1);
        assert_eq!(gcd(1, 1), 1);
    }

    #[test]
    fn test_large() {
        assert_eq!(gcd(123456, 789012), 12);
    }
}
