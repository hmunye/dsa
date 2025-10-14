/// Returns `x` raised to the power of `exp` using [Binary Exponentiation].
///
/// [Binary Exponentiation]: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
pub fn binary_power(mut x: usize, mut exp: usize) -> usize {
    // One can naively compute `x^exp` with:
    //
    //      x * x * x * x .... * x (`exp` times)
    //
    // Using binary exponentiation offers a more efficient method based on
    // `successive squaring`.

    // Any number `x` raised to the power of `0` evaluates to `1`.
    if exp == 0 {
        return 1;
    }

    // Initialize the accumulator to `1`.
    let mut y = 1;

    while exp > 1 {
        if exp % 2 != 0 {
            y *= x;
            exp -= 1; // Decrease `exp` by 1 to make it even.
        }

        x *= x;

        // Halving `exp` reduces the problem size exponentially.
        exp /= 2;
    }

    x * y
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_small() {
        assert_eq!(binary_power(2, 1), 2);
        assert_eq!(binary_power(3, 2), 9);
        assert_eq!(binary_power(5, 3), 125);
    }

    #[test]
    fn test_even_exponent() {
        assert_eq!(binary_power(2, 4), 16);
        assert_eq!(binary_power(3, 6), 729);
        assert_eq!(binary_power(10, 8), 100000000);
    }

    #[test]
    fn test_odd_exponent() {
        assert_eq!(binary_power(2, 5), 32);
        assert_eq!(binary_power(7, 3), 343);
        assert_eq!(binary_power(9, 7), 4782969);
    }

    #[test]
    fn test_large_exponent() {
        assert_eq!(binary_power(2, 50), 1125899906842624);
        assert_eq!(binary_power(3, 10), 59049);
    }

    #[test]
    fn test_large_base() {
        assert_eq!(binary_power(1000, 2), 1000000);
        assert_eq!(binary_power(100, 4), 100000000);
    }

    #[test]
    fn test_zero() {
        assert_eq!(binary_power(0, 5), 0);

        assert_eq!(binary_power(5, 0), 1);
        assert_eq!(binary_power(10, 0), 1);
        assert_eq!(binary_power(100, 0), 1);
    }
}
