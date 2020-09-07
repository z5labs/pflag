use std::fmt;
use std::str;
use std::string;

/// Value is a trait representing the value stored in a flag.
///
/// (The default value is represented as a string.)
pub trait Value {
    // set
    fn set(&mut self, val: string::String) -> Result<(), string::String>;

    // value
    fn value(&self) -> string::String;

    // typ returns the type name as a string. By default,
    // all Values are assumed to be strings.
    //
    fn typ(&self) -> &str {
        "String"
    }
}

impl<T: string::ToString + str::FromStr<Err: fmt::Debug> + fmt::Debug> Value for T {
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
