use std::fmt;
use std::str;
use std::string;

/// Value is a trait representing the value stored in a flag.
pub trait Value {
    /// set sets the underlying value.
    fn set(&mut self, val: string::String) -> Result<(), string::String>;

    /// value retrieves the current value as a String.
    fn value(&self) -> string::String;

    /// typ returns the type name as a string.
    fn typ(&self) -> &str {
        let type_name = std::any::type_name_of_val(self);
        &type_name[(type_name
            .rfind(':')
            .map(|v| v as isize)
            .unwrap_or_else(|| -1)
            + 1) as usize..]
    }
}

impl<T: string::ToString + str::FromStr<Err: fmt::Debug>> Value for T {
    // typ is reimplemeted in order to leverage any::type_name, which
    // is currently whereas any::type_name_of_val is not.
    fn typ(&self) -> &str {
        let type_name = std::any::type_name::<T>();
        &type_name[(type_name
            .rfind(':')
            .map(|v| v as isize)
            .unwrap_or_else(|| -1)
            + 1) as usize..]
    }

    fn set(&mut self, val: string::String) -> Result<(), string::String> {
        let res = val.as_str().parse::<T>();
        match res {
            Ok(v) => {
                *self = v;
                Ok(())
            }
            Err(err) => Err(format!("unexpected error while parsing: {:?}", err)),
        }
    }

    fn value(&self) -> string::String {
        self.to_string()
    }
}

/// Slice is used for creating multi-valued flags.
#[derive(Debug, Default)]
pub struct Slice<T> {
    vals: Vec<T>,
    changed: bool,
}

impl<T> Slice<T> {
    /// Constructs a new, empty Slice<T>.
    /// Do not use this constructor for setting defaults. Instead, use the provided
    /// from method.
    pub fn new() -> Self {
        Slice {
            vals: Vec::new(),
            changed: true,
        }
    }

    /// Constructs a new, empty Slice<T> with the specified capacity.
    /// Do not use this constructor for setting defaults. Instead, use the provided
    /// from method.
    pub fn with_capacity(capacity: usize) -> Self {
        Slice {
            vals: Vec::with_capacity(capacity),
            changed: true,
        }
    }

    /// Returns the number of elements in the slice.
    pub fn len(&self) -> usize {
        self.vals.len()
    }
}

impl<T, V: Into<Vec<T>>> From<V> for Slice<T> {
    /// Constructs a Slice<T> from anything a Vec<T> can be constructed from.
    /// This method should be used anytime you desire default values to be set.
    fn from(v: V) -> Self {
        Self {
            vals: v.into(),
            changed: false,
        }
    }
}

impl<T: string::ToString + str::FromStr<Err: fmt::Debug>> Value for Slice<T> {
    fn typ(&self) -> &str {
        let type_name = std::any::type_name::<T>();
        &type_name[(type_name
            .rfind(':')
            .map(|v| v as isize)
            .unwrap_or_else(|| -1)
            + 1) as usize..]
    }

    fn set(&mut self, val: string::String) -> Result<(), string::String> {
        if !self.changed {
            self.vals = Vec::with_capacity(self.vals.capacity());
        }
        val.trim_matches('"').split(',').try_for_each(|v| {
            let res = v.parse::<T>();
            match res {
                Ok(v) => {
                    self.vals.push(v);
                    Ok(())
                }
                Err(err) => Err(format!("unexpected error while parsing: {:?}", err)),
            }
        })
    }

    fn value(&self) -> string::String {
        let mut val = self
            .vals
            .iter()
            .map(|v| -> string::String { v.to_string() })
            .fold(String::from(""), |mut acc, v| {
                acc.push_str(&v);
                acc.push(',');
                acc
            });
        val.pop();
        val
    }
}

impl<T: str::FromStr<Err: fmt::Debug>> str::FromStr for Slice<T> {
    type Err = T::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.trim_matches('"')
            .split(',')
            .try_fold(Slice::new(), |mut acc, v| {
                let res = v.parse::<T>()?;
                acc.vals.push(res);
                Ok(acc)
            })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn strip_prefix_from_type_name() {
        let val: Box<dyn Value> = Box::new("".to_string());
        let type_name = val.typ();
        assert_eq!(type_name, "String")
    }
}
