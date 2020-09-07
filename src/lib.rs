//! pflag is a port of spf13s' amazing Go package by the same name.

#![feature(associated_type_bounds)]

mod value;

use std::cell::{Ref, RefCell};
use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;
pub use value::Value;

/// A Flag represents the state of a flag.
pub struct Flag<'a> {
    /// name as it appears on command line
    pub name: &'a str,

    /// one-letter abbreviated flag
    pub shorthand: &'a str,

    /// help message
    pub usage: &'a str,

    /// value as set
    pub value: Box<dyn value::Value>,

    /// default value (as text); for usage message
    pub def_value: &'a str,

    /// If the user set the value (or if left to default)
    pub changed: bool,

    /// default value (as text); if the flag is on the command line without any options
    pub no_opt_def_value: &'a str,

    /// If this flag is deprecated, this string is the new or now thing to use
    pub deprecated: &'a str,

    /// used by cobra.Command to allow flags to be hidden from help/usage text
    pub hidden: bool,

    /// If the shorthand of this flag is deprecated, this string is the new or now thing to use
    pub shorthand_deprecated: &'a str,
}

impl<'a> Flag<'a> {
    pub fn set(&mut self, val: String) -> Result<(), String> {
        self.value.set(val)
    }

    fn default_is_zero_value(&self) -> bool {
        self.def_value == ""
    }
}

/// A FlagSet represents a set of defined flags.
pub struct FlagSet<'a> {
    name: &'a str,
    parsed: bool,
    args: Vec<String>,
    actual: Vec<Rc<RefCell<Flag<'a>>>>,
    formal: BTreeMap<&'a str, Rc<RefCell<Flag<'a>>>>,
    shorthand: BTreeMap<char, Rc<RefCell<Flag<'a>>>>,
}

macro_rules! builtin_flag_val {
    ($name:ident, $typ:ty) => {
        builtin_flag_val!{@gen $name, $typ, concat!(
            stringify!($name),
            " defines a ",
            stringify!($typ),
            " flag with specified name, default value, and usage string."
        )}
    };

    (@gen $name:ident, $typ:ty, $doc:expr) => {
        #[doc = $doc]
        pub fn $name(&mut self, name: &'a str, value: $typ, usage: &'a str) {
            self.add_flag(Flag {
                name,
                shorthand: "",
                usage,
                value: Box::new(value),
                def_value: "",
                changed: false,
                no_opt_def_value: "",
                deprecated: "",
                hidden: false,
                shorthand_deprecated: "",
            });
        }
    };
}

impl<'a> FlagSet<'a> {
    /// new returns a new, empty flag set with the specified name.
    pub fn new(name: &'a str) -> Self {
        FlagSet {
            name,
            parsed: false,
            args: Vec::new(),
            actual: Vec::new(),
            formal: BTreeMap::new(),
            shorthand: BTreeMap::new(),
        }
    }

    /// add_flag will add the flag to the FlagSet.
    pub fn add_flag(&mut self, flag: Flag<'a>) {
        if let Some(_) = self.formal.get(flag.name) {
            panic!("{} flag redefined: {}", self.name, flag.name);
        }
        let name = flag.name;
        let shorthand = flag.shorthand;
        let rf = Rc::new(RefCell::new(flag));
        self.formal.insert(name, rf.clone());

        if shorthand == "" {
            return;
        }
        if shorthand.len() > 1 {
            panic!("{} shorthand is more than one ASCII character", shorthand);
        }

        let c = shorthand.chars().nth(0).unwrap();
        if let Some(used) = self.shorthand.get(&c) {
            panic!(
                "unable to redefine {} shorthand in {} flagset: it's already used for {} flag",
                c,
                self.name,
                used.borrow().name
            );
        }
        self.shorthand.insert(c, rf);
    }

    /// parsed reports whether self.parse has been called.
    pub fn parsed(&self) -> bool {
        self.parsed
    }

    /// args returns the non-flag arguments.
    pub fn args(&self) -> Vec<String> {
        self.args.clone()
    }

    /// visit visits the flags in lexicographical order or in primordial
    /// order if f.SortFlags is false, calling fn for each. It visits only
    /// those flags that have been set.
    pub fn visit<F: FnMut(&Flag)>(&self, mut f: F) {
        if self.actual.len() == 0 {
            return;
        }

        self.actual.iter().for_each(|flag| f(&*flag.borrow()));
    }

    /// visit_all visits the flags in lexicographical order or in primordial
    /// order if f.SortFlags is false, calling fn for each. It visits all
    /// flags, even those not set.
    pub fn visit_all<F: FnMut(&Flag)>(&self, mut f: F) {
        if self.formal.len() == 0 {
            return;
        }

        self.formal.values().for_each(|flag| f(&*flag.borrow()));
    }

    /// lookup returns the flag structure of the named flag, returning None if none exists.
    pub fn lookup(&self, name: &str) -> Option<Ref<'_, Flag>> {
        self.formal.get(name).map(|f| f.borrow())
    }

    /// set sets the value of the named flag.
    pub fn set(&mut self, name: &str, value: &str) -> Result<(), String> {
        let opt = self.formal.get(name);
        if let None = opt {
            return Err(format!("no such flag -{}", name));
        }

        let flag_rc = opt.unwrap();
        let mut flag = flag_rc.borrow_mut();

        let res = flag.value.set(value.to_string());
        if let Err(err) = res {
            let mut flag_name = format!("--{}", flag.name);
            if flag.shorthand != "" && flag.shorthand_deprecated != "" {
                flag_name = format!("-{}, --{}", flag.shorthand, flag.shorthand_deprecated);
            }
            return Err(format!(
                "invalid argument {} for {} flag: {}",
                value, flag_name, err
            ));
        }

        if !flag.changed {
            self.actual.push(flag_rc.clone());
            flag.changed = true;
        }

        Ok(())
    }

    /// parse parses flag definitions from the argument list,
    /// which should not include the command name. Must be called
    /// after all flags in the FlagSet are defined and before flags
    /// are accessed by the program. The return value will be ErrHelp
    /// if -help was set but not defined.
    pub fn parse(&mut self, args: impl IntoIterator<Item = String>) -> Result<(), String> {
        self.parsed = true;

        let mut av: Vec<String> = args.into_iter().collect();
        loop {
            if av.len() == 0 {
                return Ok(());
            }
            let s = av.remove(0);

            if s.len() == 0 || !s.starts_with('-') || s.len() == 1 {
                self.args.push(s);
                continue;
            }

            if s.starts_with("--") {
                if let Err(err) = self.parse_long_arg(s, &mut av) {
                    return Err(err);
                }
            } else {
                // TODO: Parse short arg
            }
        }
    }

    fn parse_long_arg(&mut self, arg: String, args: &mut Vec<String>) -> Result<(), String> {
        let name = &arg[2..];
        if name.len() == 0 || name.starts_with('-') || name.starts_with('=') {
            return Err(format!("bad flag syntax: {}", arg));
        }
        let split: Vec<&str> = name.splitn(2, '=').collect();
        let name = split[0];

        match self.formal.get(name) {
            None => {
                if name == "help" {
                    return Err("help".to_string());
                }

                Err(format!("unknown flag: --{}", name))
            }
            Some(flag) => {
                let no_opt_def_value = flag.borrow().no_opt_def_value;

                if split.len() == 2 {
                    let val = split[1];
                    return self.set(name, val);
                } else if no_opt_def_value != "" {
                    return self.set(name, no_opt_def_value);
                } else if args.len() > 0 {
                    let s = args.remove(0);
                    return self.set(name, s.as_str());
                }
                Err(format!("flag needs an argument: {}", arg))
            }
        }
    }

    #[doc = "bool defines a bool flag with specified name, default value, and usage string."]
    pub fn bool(&mut self, name: &'a str, value: bool, usage: &'a str) {
        self.add_flag(Flag {
            name,
            shorthand: "",
            usage,
            value: Box::new(value),
            def_value: "",
            changed: false,
            no_opt_def_value: "true",
            deprecated: "",
            hidden: false,
            shorthand_deprecated: "",
        })
    }

    builtin_flag_val!(char, char);
    builtin_flag_val!(string, String);
    builtin_flag_val!(uint8, u8);
    builtin_flag_val!(uint16, u16);
    builtin_flag_val!(uint32, u32);
    builtin_flag_val!(uint64, u64);
    builtin_flag_val!(uint128, u128);
    builtin_flag_val!(usize, usize);
    builtin_flag_val!(int8, i8);
    builtin_flag_val!(int16, i16);
    builtin_flag_val!(int32, i32);
    builtin_flag_val!(int64, i64);
    builtin_flag_val!(int128, i128);
    builtin_flag_val!(isize, isize);
    builtin_flag_val!(f32, f32);
    builtin_flag_val!(f64, f64);

    builtin_flag_val!(ip_addr, std::net::IpAddr);
    builtin_flag_val!(ip_v4_addr, std::net::Ipv4Addr);
    builtin_flag_val!(ip_v6_addr, std::net::Ipv6Addr);
    builtin_flag_val!(socket_addr, std::net::SocketAddr);
    builtin_flag_val!(socket_addr_v4, std::net::SocketAddrV4);
    builtin_flag_val!(socket_addr_v6, std::net::SocketAddrV6);

    /// value_of retrieves the value for the given flags name.
    pub fn value_of<T: std::str::FromStr<Err: fmt::Debug>>(&self, name: &str) -> T {
        let flag = self.formal.get(name).unwrap();
        flag.borrow().value.value().parse().unwrap()
    }
}

/// FlagSet implements fmt::Display to format the
/// usage for all the flags in the set.
impl<'a> fmt::Display for FlagSet<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        let mut lines: Vec<String> = Vec::new();

        let mut max_len = 0;
        self.visit_all(|flag| {
            if flag.hidden {
                return;
            }

            let mut line = format!("      --{}", flag.name);
            if flag.shorthand != "" && flag.shorthand_deprecated == "" {
                line = format!("  -{}, --{}", flag.shorthand, flag.name);
            }

            let (varname, usage) = unquote_usage(flag);
            if varname != "" {
                line.push_str(&(" ".to_owned() + &varname));
            }
            if flag.no_opt_def_value != "" {
                match flag.value.typ() {
                    "String" => {}
                    "bool" => {
                        if flag.no_opt_def_value != "true" {
                            line.push_str(&format!("[={}]", flag.no_opt_def_value))
                        }
                    }
                    _ => line.push_str(&format!("[={}]", flag.no_opt_def_value)),
                }
            }

            line.push_str("\x00");
            if line.len() > max_len {
                max_len = line.len();
            }

            line.push_str(usage.as_str());
            if !flag.default_is_zero_value() {
                match flag.value.typ() {
                    "String" => line.push_str(&format!(" (default \"{}\")", flag.def_value)),
                    _ => line.push_str(&format!(" (default {})", flag.def_value)),
                }
            }
            if flag.deprecated.len() > 0 {
                line.push_str(&format!(" (DEPRECATED: {})", flag.deprecated));
            }

            lines.push(line);
        });

        lines.iter().for_each(|line| {
            let sidx = line.find("\x00").map(|v| v as isize).unwrap_or_else(|| -1);
            let spacing = " ".repeat((max_len as isize - sidx) as usize);
            buf.push_str(&line[..sidx as usize]);
            buf.push(' ');
            buf.push_str(&spacing);
            buf.push(' ');
            buf.push_str(&line[(sidx as usize) + 1..].replace("\n", &"\n".repeat(max_len + 2)));
            buf.push('\n');
        });

        f.write_str(buf.as_str())
    }
}

fn unquote_usage(flag: &Flag<'_>) -> (String, String) {
    let usage = flag.usage;
    for i in 1..usage.len() + 1 {
        if &usage[i - 1..i] == "`" {
            for j in i + 1..usage.len() + 1 {
                if &usage[j - 1..j] == "`" {
                    let name = &usage[i + 1..j];
                    let end = &usage[j + 1..];
                    let mut usage = usage[..i].to_string();
                    usage.push_str(name);
                    usage.push_str(end);
                    return (name.to_string(), usage);
                }
            }
            break;
        }
    }

    let mut name = flag.value.typ();
    match name {
        "bool" => name = "",
        "float64" => name = "float",
        "int64" => name = "int",
        "uint64" => name = "uint",
        _ => {}
    };

    (name.to_string(), usage.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_long_with_eq() {
        let mut flags = FlagSet::new("test");
        flags.string("hello", "".to_string(), "test");

        if let Err(err) = flags.parse(vec!["--hello=world".to_string()]) {
            panic!(err);
        }

        assert_eq!(flags.value_of::<String>("hello"), "world".to_string());
    }

    #[test]
    fn parse_long_arg_with_space() {
        let mut flags = FlagSet::new("test");
        flags.string("hello", "".to_string(), "test");

        if let Err(err) = flags.parse(vec!["--hello".to_string(), "world".to_string()]) {
            panic!(err);
        }

        assert_eq!(flags.value_of::<String>("hello"), "world".to_string());
    }

    #[test]
    fn parse_long_arg_optional() {
        let mut flags = FlagSet::new("test");
        flags.bool("hello", false, "test");

        if let Err(err) = flags.parse(vec!["--hello".to_string()]) {
            panic!(err);
        }

        assert_eq!(flags.value_of::<bool>("hello"), true);
    }

    #[test]
    fn parse_long_arg_default() {
        let mut flags = FlagSet::new("test");
        flags.bool("hello", true, "test");

        if let Err(err) = flags.parse(vec![]) {
            panic!(err);
        }

        assert_eq!(flags.value_of::<bool>("hello"), true);
    }

    #[test]
    fn parse_ignore_positional_args() {
        let mut flags = FlagSet::new("test");

        if let Err(err) = flags.parse(vec!["hello".to_string(), "world".to_string()]) {
            panic!(err);
        }

        assert_eq!(flags.args().len(), 2);
    }
}
