//! Temporal quantification.

use std::convert;
use std::fmt;
use std::num;
use std::ops;
use std::str;
use std::time;

/// A Duration type to represent a span of time.
///
/// A string representing the duration is of the form "72h3m0.5s".
/// As a special case, durations less than one second format use a
/// smaller unit (milli-, micro-, or nanoseconds) to ensure that the
/// leading digit is non-zero. The zero duration formats as 0s.
///
/// ```
/// use std::time;
/// use pflag::Value;
/// use pflag::time::Duration;
///
/// let mut d = Duration::default();
/// d.set("1h1m10.987654321s".to_string());
///
/// assert_eq!(d, Duration::from(time::Duration::new(3670, 987654321)));
/// assert_eq!(format!("{}", d), "1h1m10.987654321s");
/// ```
#[derive(Debug, Default, Copy, Clone, PartialEq, PartialOrd)]
pub struct Duration(time::Duration);

impl Duration {
    pub fn new(secs: u64, nanos: u32) -> Self {
        Self(time::Duration::new(secs, nanos))
    }
}

impl str::FromStr for Duration {
    type Err = num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars().peekable();
        let mut secs = 0;
        let mut nanos = 0;

        loop {
            let (s, c) = scan_digits(&mut chars);
            let num: u64 = s.parse()?;
            match c {
                'h' => {
                    secs += num * 3600;
                }
                'm' => {
                    let c = chars.peek().unwrap();
                    if *c == 's' {
                        chars.next();
                        nanos += num * 1e6 as u64;
                        break;
                    }
                    secs += num * 60;
                }
                'µ' => {
                    nanos += num * 1e3 as u64;
                    break;
                }
                'n' => {
                    nanos += num;
                    break;
                }
                's' => {
                    secs += num;
                    break;
                }
                '.' => {
                    let (mut s, c) = scan_digits(&mut chars);
                    let mut pad = 9;
                    if c == 's' {
                        secs += num;
                    } else if c == 'm' {
                        nanos += num * 1e6 as u64;
                        pad = 6;
                    } else {
                        nanos += num * 1e3 as u64;
                        pad = 3;
                    }
                    (0..pad - s.len()).for_each(|_| s.push('0'));
                    let s = s.trim_start_matches('0');
                    let frac: u64 = s.parse()?;
                    nanos += frac;
                    break;
                }
                _ => break,
            }
        }

        Ok(Self(time::Duration::new(secs, nanos as u32)))
    }
}

fn scan_digits<I: Iterator<Item = char>>(iter: &mut I) -> (String, char) {
    let mut s = String::new();
    loop {
        let c = iter.next().unwrap();
        if c.is_alphabetic() || c == '.' {
            return (s, c);
        }

        s.push(c);
    }
}

impl fmt::Display for Duration {
    // largest time fmt is 5119296h10m10.000000000s
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == time::Duration::default() {
            return write!(f, "0s");
        }
        let mut buf = [0 as u8; 32];
        let mut w = buf.len();
        if self.0 < time::Duration::SECOND {
            let mut prec = 0;
            w -= 1;
            buf[w] = 's' as u8;
            w -= 1;
            if self.0 < time::Duration::MICROSECOND {
                buf[w] = 'n' as u8;
            } else if self.0 < time::Duration::MILLISECOND {
                prec = 3;
                w -= 1;
                // U+00B5 'µ' micro sign == 0xC2 0xB5
                buf[w] = 0xC2;
                buf[w + 1] = 0xB5;
            } else {
                prec = 6;
                buf[w] = 'm' as u8;
            }
            let (w2, u) = fmt_frac(&mut buf[..w], self.0.as_nanos() as u64, prec);
            w = fmt_int(&mut buf[..w2], u);
        } else {
            w -= 1;
            buf[w] = 's' as u8;

            let (w2, mut u) = fmt_frac(&mut buf[..w], self.0.as_nanos() as u64, 9);

            w = fmt_int(&mut buf[..w2], u % 60);
            u /= 60;

            if u > 0 {
                w -= 1;
                buf[w] = 'm' as u8;
                w = fmt_int(&mut buf[..w], u % 60);
                u /= 60;

                if u > 0 {
                    w -= 1;
                    buf[w] = 'h' as u8;
                    w = fmt_int(&mut buf[..w], u)
                }
            }
        }

        f.write_str(str::from_utf8(&buf[w..]).unwrap())
    }
}

fn fmt_frac(buf: &mut [u8], mut v: u64, prec: u8) -> (usize, u64) {
    // Omit trailing zeros up to and including decimal point.
    let mut w = buf.len();
    let mut print = false;
    for _ in 0..prec {
        let digit = v % 10;
        print = print || digit != 0;
        if print {
            w -= 1;
            buf[w] = digit as u8 + '0' as u8;
        }
        v /= 10;
    }
    if print {
        w -= 1;
        buf[w] = '.' as u8;
    }
    (w, v)
}

fn fmt_int(buf: &mut [u8], mut v: u64) -> usize {
    let mut w = buf.len();
    if v == 0 {
        w -= 1;
        buf[w] = '0' as u8;
    } else {
        while v > 0 {
            w -= 1;
            buf[w] = (v % 10) as u8 + '0' as u8;
            v /= 10;
        }
    }
    w
}

impl From<time::Duration> for Duration {
    fn from(d: time::Duration) -> Self {
        Self(d)
    }
}

impl Into<time::Duration> for Duration {
    fn into(self) -> time::Duration {
        self.0
    }
}

impl ops::Deref for Duration {
    type Target = time::Duration;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl convert::AsRef<time::Duration> for Duration {
    fn as_ref(&self) -> &time::Duration {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Value;

    #[test]
    fn format() {
        let cases = vec![
            ("3ns", time::Duration::new(0, 3)),
            ("3.000001ms", time::Duration::new(0, 3000001)),
            ("3s", time::Duration::new(3, 0)),
            ("1m0s", time::Duration::new(60, 0)),
            ("1h0m0s", time::Duration::new(3600, 0)),
            ("1h0m0.0001s", time::Duration::new(3600, 100000)),
        ];

        cases
            .into_iter()
            .map(|(f, d)| (f, Duration::from(d)))
            .for_each(|(f, d)| {
                assert_eq!(f, format!("{}", d));
                let mut d2 = Duration::default();
                let res = d2.set(f.to_string());
                assert!(res.is_ok());
                assert_eq!(d, d2);
            })
    }
}
