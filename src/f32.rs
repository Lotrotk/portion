/// The floating point type.
type Flt = f32;

/// A value in range [0..1].
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct Portion(Flt);

/// The relative portion of one (numerator) within another (denominator).
/// Two segments are considered here : [0..denominator] and ]denominator..1].
/// If the numerator lies within first segment the resulting value is simply numerator/denumerator.
/// Otherwise the relative portion within the second segment is returned.
pub enum Within {
    /// Represents the portion within the interval [0..denominator].
    First(Portion),
    /// Represents the portion within the interval ]denominator..1].
    Second(Portion),
}

impl Portion {
    /// The minimum value.
    ///
    /// ```
    /// use portion::f32::Portion;
    /// let p = Portion::zero();
    /// assert_eq!(Portion::value(p), 0.0);
    /// ```
    pub const fn zero() -> Self {
        Portion(0.0)
    }

    /// ```
    /// use portion::f32::Portion;
    /// let p = Portion::half();
    /// assert_eq!(Portion::value(p), 0.5);
    /// ```
    pub const fn half() -> Self {
        Portion(0.5)
    }

    /// The unit and maximum value.
    ///
    /// ```
    /// use portion::f32::Portion;
    /// let p = Portion::one();
    /// assert_eq!(Portion::value(p), 1.0);
    /// ```
    pub const fn one() -> Self {
        Portion(1.0)
    }

    /// Creates a portion at run time.
    ///
    /// ```
    /// use portion::f32::Portion;
    /// let p = Portion::new(-0.5);
    /// assert!(p.is_err());
    /// let p = Portion::new(0.0);
    /// assert!(p.is_ok());
    /// let p = Portion::new(0.5);
    /// assert!(p.is_ok());
    /// let p = Portion::new(1.0);
    /// assert!(p.is_ok());
    /// let p = Portion::new(1.5);
    /// assert!(p.is_err());
    /// for value in &[std::f32::NAN, std::f32::INFINITY, std::f32::NEG_INFINITY,] {
    ///    let p = Portion::new(*value);
    ///    assert!(p.is_err());
    /// }
    /// ```
    pub fn new(value: Flt) -> Result<Self, ()> {
        if 0.0 <= value && value <= 1. {
            Ok(Portion(value))
        } else {
            Err(())
        }
    }

    /// Returns a floating point value in range [0..1].
    ///
    /// This is intentionally not a method. Avoid it.
    ///
    /// ```
    /// use portion::f32::Portion;
    /// let p = Portion::new(0.25).unwrap();
    /// assert_eq!(Portion::value(p), 0.25);
    /// ```
    pub const fn value(p: Portion) -> Flt {
        p.0
    }

    /// Returns the difference to 1.
    ///
    /// ```
    /// use portion::f32::Portion;
    /// let x = Portion::new(0.25).unwrap();
    /// let y = x.complement();
    /// assert_eq!(Portion::value(y), 0.75);
    /// ```
    pub fn complement(self) -> Portion {
        Portion(1.0 - self.0)
    }

    /// The relative portion of one (numerator) within another (denominator).
    ///
    /// ```
    /// use portion::f32::{Portion, Within};
    /// let x = Portion::new(0.125).unwrap();
    /// let y = Portion::half();
    /// let z = x.within(y);
    /// if let Within::First(first) = z {
    ///    assert_eq!(Portion::value(first), 0.25);
    /// } else {
    ///    panic!("This should really lie in the first segment");
    /// }
    ///
    /// let x = Portion::new(0.875).unwrap();
    /// let y = Portion::half();
    /// let z = x.within(y);
    /// if let Within::Second(second) = z {
    ///    assert_eq!(Portion::value(second), 0.75);
    /// } else {
    ///    panic!("This should really lie in the second segment");
    /// }
    ///
    /// ```
    pub fn within(self, denominator: Self) -> Within {
        if self.0 <= denominator.0 {
            Within::First(Portion(self.0 / denominator.0))
        } else {
            Within::Second(Portion((self.0 - denominator.0) / (1.0 - denominator.0)))
        }
    }
}

impl std::ops::Mul for Portion {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Portion(self.0.mul(rhs.0))
    }
}

impl std::ops::Mul<SPortion> for Portion {
    type Output = SPortion;
    fn mul(self, rhs: SPortion) -> Self::Output {
        SPortion(self.0.mul(rhs.0))
    }
}

impl std::ops::Add for Portion {
    type Output = Result<Self, ()>;
    fn add(self, rhs: Self) -> Self::Output {
        Portion::new(self.0.add(rhs.0))
    }
}

impl std::ops::Add<SPortion> for Portion {
    type Output = Result<SPortion, ()>;
    fn add(self, rhs: SPortion) -> Self::Output {
        SPortion::new(self.0.add(rhs.0))
    }
}

impl std::ops::Sub for Portion {
    type Output = SPortion;
    fn sub(self, rhs: Self) -> Self::Output {
        SPortion(self.0.sub(rhs.0))
    }
}

impl std::ops::Sub<SPortion> for Portion {
    type Output = Result<SPortion, ()>;
    fn sub(self, rhs: SPortion) -> Self::Output {
        SPortion::new(self.0.sub(rhs.0))
    }
}

impl std::ops::Neg for Portion {
    type Output = SPortion;
    fn neg(self) -> Self::Output {
        SPortion(self.0.neg())
    }
}

impl Eq for Portion {}

impl Ord for Portion {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.0 < other.0 {
            std::cmp::Ordering::Less
        } else if self.0 == other.0 {
            std::cmp::Ordering::Equal
        } else {
            std::cmp::Ordering::Greater
        }
    }
}

#[cfg(test)]
mod tests_portion {
    use super::*;

    #[test]
    fn test_within() {
        let x = Portion::new(0.75).unwrap();
        let y = Portion::zero();
        match x.within(y) {
            Within::Second(_) => {}
            _ => panic!("This should really lie in the second segment"),
        };

        let x = Portion::new(0.75).unwrap();
        let y = Portion::one();
        match x.within(y) {
            Within::First(_) => {}
            _ => panic!("This should really lie in the first segment"),
        };
    }

    #[test]
    fn test_mul_self() {
        let x = Portion::half();
        let y = x * x;
        assert_eq!(Portion::value(y), 0.25);
    }

    #[test]
    fn test_mul_negative() {
        let x = Portion::half();
        let y = -SPortion::half();
        let z = x * y;
        assert_eq!(SPortion::value(z), -0.25);
    }

    #[test]
    fn test_add_self() {
        let x = Portion::new(0.25).unwrap();
        let y = (x + x).unwrap();
        assert_eq!(Portion::value(y), 0.5);
        let x = Portion::new(0.75).unwrap();
        let y = x + x;
        assert!(y.is_err());
    }

    #[test]
    fn test_add_negative() {
        let x = Portion::new(0.25).unwrap();
        let y = SPortion::new(0.5).unwrap();
        let z = (x + y).unwrap();
        assert_eq!(SPortion::value(z), 0.75);
        let y = SPortion::new(-0.5).unwrap();
        let z = (x + y).unwrap();
        assert_eq!(SPortion::value(z), -0.25);
        let y = SPortion::new(0.9).unwrap();
        let z = x + y;
        assert!(z.is_err());
    }

    #[test]
    fn test_sub_self() {
        let x = Portion::new(0.25).unwrap();
        let y = Portion::new(0.5).unwrap();
        let z = x - y;
        assert_eq!(SPortion::value(z), -0.25);
    }

    #[test]
    fn test_sub_negative() {
        let x = Portion::new(0.25).unwrap();
        let y = SPortion::new(0.5).unwrap();
        let z = (x - y).unwrap();
        assert_eq!(SPortion::value(z), -0.25);
        let y = SPortion::new(-0.5).unwrap();
        let z = (x - y).unwrap();
        assert_eq!(SPortion::value(z), 0.75);
        let y = SPortion::new(-0.9).unwrap();
        let z = x - y;
        assert!(z.is_err());
    }

    #[test]
    fn test_neg() {
        let x: SPortion = -Portion::new(0.25).unwrap();
        assert_eq!(SPortion::value(x), -0.25);
    }

    #[test]
    fn test_ord() {
        let x = Portion::new(0.25).unwrap();
        let y = Portion::half();
        assert!(x < y);
        assert!(y > x);
        assert_eq!(x, x);
    }
}

/// A signed portion: a value in range [-1..1].
/// This type represents the difference between two unsigned portions.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct SPortion(Flt);

impl SPortion {
    /// The minimum value.
    ///
    /// ```
    /// use portion::f32::SPortion;
    /// let sp = SPortion::minus_one();
    /// assert_eq!(SPortion::value(sp), -1.0);
    /// ```
    pub const fn minus_one() -> Self {
        SPortion(-1.0)
    }

    /// The zero value.
    ///
    /// ```
    /// use portion::f32::SPortion;
    /// let sp = SPortion::zero();
    /// assert_eq!(SPortion::value(sp), 0.0);
    /// ```
    pub const fn zero() -> Self {
        SPortion(0.0)
    }

    /// ```
    /// use portion::f32::SPortion;
    /// let sp = SPortion::half();
    /// assert_eq!(SPortion::value(sp), 0.5);
    /// ```
    pub const fn half() -> Self {
        SPortion(0.5)
    }

    /// The unit and maximum value.
    ///
    /// ```
    /// use portion::f32::SPortion;
    /// let sp = SPortion::one();
    /// assert_eq!(SPortion::value(sp), 1.0);
    /// ```
    pub const fn one() -> Self {
        SPortion(1.0)
    }

    /// Creates a portion at run time.
    ///
    /// ```
    /// use portion::f32::SPortion;
    /// let sp = SPortion::new(-1.5);
    /// assert!(sp.is_err());
    /// let sp = SPortion::new(-1.0);
    /// assert!(sp.is_ok());
    /// let sp = SPortion::new(0.0);
    /// assert!(sp.is_ok());
    /// let sp = SPortion::new(1.0);
    /// assert!(sp.is_ok());
    /// let sp = SPortion::new(1.5);
    /// assert!(sp.is_err());
    /// for value in &[std::f32::NAN, std::f32::INFINITY, std::f32::NEG_INFINITY,] {
    ///    let sp = SPortion::new(*value);
    ///    assert!(sp.is_err());
    /// }
    /// ```
    pub fn new(value: Flt) -> Result<Self, ()> {
        if -1.0 <= value && value <= 1. {
            Ok(SPortion(value))
        } else {
            Err(())
        }
    }

    /// Returns a floating point value in range [-1..1].
    ///
    /// This is intentionally not a method. Avoid it.
    ///
    /// ```
    /// use portion::f32::SPortion;
    /// let sp = SPortion::new(-0.25).unwrap();
    /// assert_eq!(SPortion::value(sp), -0.25);
    /// ```
    pub const fn value(sp: SPortion) -> Flt {
        sp.0
    }

    /// Converts to a positive portion, if the value is not negative.
    ///
    /// ```
    /// use portion::f32::{Portion, SPortion};
    /// let x = SPortion::half();
    /// let y = x.to_portion().unwrap();
    /// assert_eq!(Portion::value(y), 0.5);
    /// let x = SPortion::new(-0.5).unwrap();
    /// let y = x.to_portion();
    /// assert!(y.is_err());
    /// ```
    pub fn to_portion(self) -> Result<Portion, ()> {
        Portion::new(self.0)
    }

    /// Removes the value's sign.
    ///
    /// ```
    /// use portion::f32::{Portion, SPortion};
    /// let x = SPortion::half();
    /// let y = x.abs();
    /// assert_eq!(Portion::value(y), 0.5);
    /// let x = -SPortion::half();
    /// let y = x.abs();
    /// assert_eq!(Portion::value(y), 0.5);
    /// ```
    pub fn abs(self) -> Portion {
        Portion(Flt::abs(self.0))
    }
}

impl From<Portion> for SPortion {
    fn from(p: Portion) -> Self {
        SPortion(p.0)
    }
}

impl std::ops::Mul for SPortion {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        SPortion(self.0.mul(rhs.0))
    }
}

impl std::ops::Mul<Portion> for SPortion {
    type Output = Self;
    fn mul(self, rhs: Portion) -> Self::Output {
        SPortion(self.0.mul(rhs.0))
    }
}

impl std::ops::Add for SPortion {
    type Output = Result<Self, ()>;
    fn add(self, rhs: Self) -> Self::Output {
        SPortion::new(self.0.add(rhs.0))
    }
}

impl std::ops::Sub for SPortion {
    type Output = Result<Self, ()>;
    fn sub(self, rhs: Self) -> Self::Output {
        SPortion::new(self.0.sub(rhs.0))
    }
}

impl std::ops::Neg for SPortion {
    type Output = Self;
    fn neg(self) -> Self::Output {
        SPortion(self.0.neg())
    }
}

impl Eq for SPortion {}

impl Ord for SPortion {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.0 < other.0 {
            std::cmp::Ordering::Less
        } else if self.0 == other.0 {
            std::cmp::Ordering::Equal
        } else {
            std::cmp::Ordering::Greater
        }
    }
}

#[cfg(test)]
mod tests_dportion {
    use super::*;

    #[test]
    fn test_from_portion() {
        let x = Portion::half();
        let y: SPortion = x.into();
        assert_eq!(SPortion::value(y), 0.5);
    }

    #[test]
    fn test_mul() {
        let x = SPortion::half();
        let y = -x * x;
        assert_eq!(SPortion::value(y), -0.25);
    }

    #[test]
    fn test_mul_positive() {
        let x = -SPortion::half();
        let y = Portion::half();
        let z = x * y;
        assert_eq!(SPortion::value(z), -0.25);
    }

    #[test]
    fn test_add() {
        let x = SPortion::new(0.25).unwrap();
        let y = SPortion::new(-0.5).unwrap();
        let z = (x + y).unwrap();
        assert_eq!(SPortion::value(z), -0.25);
        let x = SPortion::new(0.75).unwrap();
        let y = x + x;
        assert!(y.is_err());
        let x = SPortion::new(-0.75).unwrap();
        let y = x + x;
        assert!(y.is_err());
    }

    #[test]
    fn test_sub() {
        let x = SPortion::new(0.25).unwrap();
        let y = SPortion::new(0.5).unwrap();
        let z = (x - y).unwrap();
        assert_eq!(SPortion::value(z), -0.25);
        let x = SPortion::new(0.75).unwrap();
        let y = SPortion::new(-0.75).unwrap();
        let z = x - y;
        assert!(z.is_err());
        let x = SPortion::new(-0.75).unwrap();
        let y = SPortion::new(0.75).unwrap();
        let z = x - y;
        assert!(z.is_err());
    }

    #[test]
    fn test_neg() {
        let x = -SPortion::new(0.25).unwrap();
        assert_eq!(SPortion::value(x), -0.25);
    }

    #[test]
    fn test_ord() {
        let x = -SPortion::half();
        let y = SPortion::half();
        assert!(x < y);
        assert!(y > x);
        assert_eq!(x, x);
    }
}
