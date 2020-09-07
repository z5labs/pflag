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
        return "string";
    }
}

#[derive(Debug)]
pub struct String(string::String);

impl String {
    pub fn new(val: string::String) -> Self {
        String(val)
    }
}

impl Value for String {
    fn set(&mut self, val: string::String) -> Result<(), string::String> {
        self.0 = val.trim_matches('"').to_string();
        Ok(())
    }

    fn value(&self) -> string::String {
        self.0.clone()
    }
}

// macro_rules! builtin_type_value {
//     ( $name:ident, $typ:ty ) => {
//         #[derive(Debug)]
//         pub struct $name($typ);
//
//         impl Value for $name {
//             fn typ(&self) -> &str {
//                 "&typ"
//             }
//
//             fn set(&mut self, val: string::String) -> Result<(), string::String> {
//                 self.0 = val.as_str().parse().unwrap();
//                 Ok(())
//             }
//
//             fn value(&self) -> string::String {
//                 self.0.to_string()
//             }
//         }
//     };
// }

impl<T: string::ToString + str::FromStr<Err: fmt::Debug> + fmt::Debug> Value for T {
    fn typ(&self) -> &str {
        std::any::type_name::<T>()
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

// builtin_type_value!(Bool, bool);
//
// builtin_type_value!(Uint8, u8);
// builtin_type_value!(Uint16, u16);
// builtin_type_value!(Uint32, u32);
// builtin_type_value!(Uint64, u64);
//
// builtin_type_value!(Int8, i8);
// builtin_type_value!(Int16, i16);
// builtin_type_value!(Int32, i32);
// builtin_type_value!(Int64, i64);
//
// builtin_type_value!(IpAddr, std::net::IpAddr);
