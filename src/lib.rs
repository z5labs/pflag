//! pflag is a port of spf13s' amazing Go package by the same name.
//!
//! pflag is compatible with the GNU extensions to the POSIX recommendations for command-line
//! options. See [http://www.gnu.org/software/libc/manual/html_node/Argument-Syntax.html](http://www.gnu.org/software/libc/manual/html_node/Argument-Syntax.html).
//!
//! ```
//! use pflag::{FlagSet, Slice};
//! use std::net::{IpAddr, Ipv4Addr};
//!
//! let mut flags = FlagSet::new("name");
//!
//! // Use higher level methods over add_flag directly.
//! flags.int8("num", 0, "a flag for a number");
//! flags.string_p("str", 's', String::from("default value"), "a flag for a String and has a shorthand");
//! flags.ip_addr_slice(
//!     "addrs",
//!     Slice::from([IpAddr::V4(Ipv4Addr::new(0,0,0,0)), IpAddr::V4(Ipv4Addr::new(127,0,0,1))]),
//!     "a multi-valued flag",
//! );
//!
//! let args = "--num=1 -s world --addrs 192.168.1.1,192.168.0.1 --addrs=127.0.0.1 subcommand";
//! if let Err(err) = flags.parse(args.split(' ')) {
//!     panic!(err);
//! }
//!
//! // Retrieving value is very easy with the value_of method.
//! assert_eq!(*flags.value_of::<i8>("num").unwrap(), 1);
//! assert_eq!(*flags.value_of::<String>("str").unwrap(), "world");
//! assert_eq!(flags.value_of::<Slice<IpAddr>>("addrs").unwrap().len(), 3);
//!
//! // Any non-flag args i.e. positional args can be retrieved by...
//! let args = flags.args();
//! assert_eq!(args.len(), 1);
//! assert_eq!(args[0], "subcommand");
//! ```

#![feature(const_type_id)]
#![feature(type_name_of_val)]
#![feature(test)]
#![feature(duration_constants)]

extern crate test;

pub mod time;
mod value;

pub use value::Slice;
pub use value::Value;
pub use value::ValueError;

use std::any::TypeId;
use std::collections::BTreeMap;
use std::error;
use std::fmt;
use std::iter::Peekable;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};
use std::str;

use concat_idents::concat_idents;
use paste::paste;

/// A Flag represents the state of a flag.
pub struct Flag {
    /// name as it appears on command line
    pub name: String,

    /// one-letter abbreviated flag
    pub shorthand: char,

    /// help message
    pub usage: String,

    /// value as set
    pub value: Box<dyn value::Value>,

    /// default value (as text); for usage message
    pub def_value: String,

    /// If the user set the value (or if left to default)
    pub changed: bool,

    /// default value (as text); if the flag is on the command line without any options
    pub no_opt_def_value: String,

    /// If this flag is deprecated, this string is the new or now thing to use
    pub deprecated: String,

    /// used by cobra.Command to allow flags to be hidden from help/usage text
    pub hidden: bool,

    /// If the shorthand of this flag is deprecated, this string is the new or now thing to use
    pub shorthand_deprecated: String,
}

macro_rules! const_type_id {
    ($name:ident, $typ:ty) => {
        const $name: TypeId = TypeId::of::<$typ>();
    };
}

const_type_id!(BOOL_ID, bool);
const_type_id!(STRING_ID, String);
const_type_id!(DURATION_ID, time::Duration);
const_type_id!(U8_ID, u8);
const_type_id!(U16_ID, u16);
const_type_id!(U32_ID, u32);
const_type_id!(U64_ID, u64);
const_type_id!(I8_ID, i8);
const_type_id!(I16_ID, i16);
const_type_id!(I32_ID, i32);
const_type_id!(I64_ID, i64);
const_type_id!(F32_ID, f32);
const_type_id!(F64_ID, f64);
const_type_id!(IP_ADDR_ID, IpAddr);
const_type_id!(IP_V4_ADDR_ID, Ipv4Addr);
const_type_id!(IP_V6_ADDR_ID, Ipv6Addr);

impl Flag {
    pub fn set(&mut self, val: String) -> Result<(), ValueError> {
        self.value.set(val)
    }

    fn default_is_zero_value(&self) -> bool {
        let def_value = self.def_value.clone();
        let id = self.value.value().type_id();
        match id {
            BOOL_ID => def_value == "false",
            DURATION_ID => def_value == "0" || def_value == "0s",
            U8_ID | U16_ID | U32_ID | U64_ID | I8_ID | I16_ID | I32_ID | I64_ID | F32_ID
            | F64_ID => def_value == "0",
            STRING_ID => def_value == "",
            IP_ADDR_ID | IP_V4_ADDR_ID | IP_V6_ADDR_ID => {
                def_value == "0.0.0.0" || def_value == "0:0:0:0:0:0:0:0"
            }
            _ => def_value == "" || def_value == "[]" || def_value == "0" || def_value == "false",
        }
    }
}

/// A FlagSet represents a set of defined flags.
pub struct FlagSet {
    name: String,
    parsed: bool,
    args: Vec<String>,
    flags: Vec<Flag>,
    formal: BTreeMap<String, usize>,
    shorthand: BTreeMap<char, usize>,
}

macro_rules! builtin_flag_val {
    ($name:ident, $typ:ty) => {
        paste!{
        concat_idents!(fn_short = $name, _, p {
            #[doc = $name " defines a " $typ " flag with specified name, default value, and usage string."]
            pub fn $name<S: Into<String>, U: Into<String>>(&mut self, name: S, value: $typ, usage: U) {
                self.var(name, value, usage)
            }

            #[doc = $name "_p is like " $name ", but accepts a shorthand letter that can be used after a single dash."]
            pub fn fn_short<S: Into<String>, U: Into<String>>(&mut self, name: S, shorthand: char, value: $typ, usage: U) {
                self.var_p(name, shorthand, value, usage)
            }
        });

        concat_idents!(fn_name = $name, _, slice  {
            #[doc = $name "_slice defines a `Slice<" $typ ">` flag with specified name, default value, and usage string."]
            pub fn fn_name<S: Into<String>, U: Into<String>>(&mut self, name: S, value: value::Slice<$typ>, usage: U) {
                self.var(name, value, usage)
            }
        });

        concat_idents!(fn_name = $name, _, p, _, slice  {
            #[doc = $name "_p_slice is like " $name "_slice, but accepts a shorthand letter that can be used after a single dash."]
            pub fn fn_name<S: Into<String>, U: Into<String>>(&mut self, name: S, shorthand: char, value: value::Slice<$typ>, usage: U) {
                self.var_p(name, shorthand, value, usage)
            }
        });
        }
    };
}

fn scan_arg<I: Iterator<Item = char>>(iter: &mut I) -> String {
    iter.skip_while(|c| *c == ' ')
        .take_while(|c| *c != ' ')
        .collect()
}

impl FlagSet {
    /// new returns a new, empty flag set with the specified name.
    pub fn new<S: Into<String>>(name: S) -> Self {
        FlagSet {
            name: name.into(),
            parsed: false,
            args: Vec::new(),
            flags: Vec::new(),
            formal: BTreeMap::new(),
            shorthand: BTreeMap::new(),
        }
    }

    /// add_flag will add the flag to the FlagSet.
    pub fn add_flag(&mut self, flag: Flag) {
        if let Some(_) = self.formal.get(&flag.name) {
            panic!("{} flag redefined: {}", self.name, flag.name);
        }
        let name = flag.name.clone();
        let shorthand = flag.shorthand.clone();

        let flags_len = self.flags.len();
        self.flags.push(flag);
        self.formal.insert(name, flags_len);

        if shorthand == char::default() {
            return;
        }

        let c = shorthand;
        if let Some(used) = self.shorthand.get(&c) {
            panic!(
                "unable to redefine {} shorthand in {} flagset: it's already used for {} flag",
                c, self.name, self.flags[*used].name
            );
        }
        self.shorthand.insert(c, flags_len);
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
        if self.flags.len() == 0 {
            return;
        }

        self.flags
            .iter()
            .filter(|f| f.changed)
            .for_each(|flag| f(flag));
    }

    /// visit_all visits the flags in lexicographical order or in primordial
    /// order if f.SortFlags is false, calling fn for each. It visits all
    /// flags, even those not set.
    pub fn visit_all<F: FnMut(&Flag)>(&self, mut f: F) {
        if self.flags.len() == 0 {
            return;
        }

        self.flags.iter().for_each(|flag| f(flag));
    }

    /// lookup returns the flag structure of the named flag, returning None if none exists.
    pub fn lookup<S: Into<String>>(&self, name: S) -> Option<&Flag> {
        let i = self.formal.get(&name.into());
        if i.is_none() {
            return None;
        }
        let i = i.unwrap();
        self.flags.get(*i)
    }

    /// set sets the value of the named flag.
    pub fn set<S: Into<String>, T: Into<String>>(
        &mut self,
        name: S,
        value: T,
    ) -> Result<(), String> {
        let name = name.into();
        let opt = self.formal.get(&name);
        if opt.is_none() {
            return Err(format!("no such flag -{}", name));
        }
        let value = value.into();

        let mut flag = self.flags.get_mut(*opt.unwrap()).unwrap();

        let res = flag.value.set(value.clone());
        if let Err(err) = res {
            let mut flag_name = format!("--{}", flag.name);
            if flag.shorthand != char::default() && flag.shorthand_deprecated != "" {
                flag_name = format!("-{}, --{}", flag.shorthand, flag.shorthand_deprecated);
            }
            return Err(format!(
                "invalid argument {} for {} flag: {}",
                value, flag_name, err
            ));
        }

        if !flag.changed {
            flag.changed = true;
        }

        Ok(())
    }

    /// parse parses flag definitions from the argument list,
    /// which should not include the command name. Must be called
    /// after all flags in the FlagSet are defined and before flags
    /// are accessed by the program. The return value will be ErrHelp
    /// if -help was set but not defined.
    ///
    /// ```
    /// let mut flags = pflag::FlagSet::new("example");
    /// flags.string("hello", String::new(), "example flag");
    ///
    /// let args = vec!["--hello=world"];
    /// if let Err(err) = flags.parse(args) {
    ///     panic!(err);
    /// }
    /// ```
    pub fn parse<'a>(&mut self, args: impl IntoIterator<Item = &'a str>) -> Result<(), String> {
        self.parsed = true;

        let mut av = args
            .into_iter()
            .flat_map(|arg| arg.trim_matches(' ').chars().chain(" ".chars()))
            .peekable();

        loop {
            let arg = av.peek();
            if arg.is_none() {
                av.next();
                return Ok(());
            }
            let s = arg.unwrap();

            match s {
                '-' => {
                    av.next();
                    let arg = av.peek();
                    if arg.is_none() || *arg.unwrap() == ' ' {
                        av.next();
                        self.args.push("-".to_string());
                        return Ok(());
                    }
                    let s = arg.unwrap();
                    if *s != '-' {
                        self.parse_shorthand(&mut av)?;
                        continue;
                    }
                    av.next();

                    let arg = av.peek();
                    let s = arg.unwrap();
                    if *s == ' ' {
                        // "--" terminates flags
                        av.next();
                        let mut i = 0;
                        let args: Vec<String> = av.fold(Vec::new(), |mut acc, c| {
                            if c == ' ' {
                                i += 1;
                                return acc;
                            }

                            if acc.len() == i {
                                acc.push(String::new());
                            }
                            acc[i].push(c);
                            acc
                        });

                        self.args.extend(args);
                        return Ok(());
                    }
                    self.parse_long(&mut av)?;
                }
                _ => {
                    let val = scan_arg(&mut av);
                    self.args.push(val);
                }
            }
        }
    }

    fn parse_long<I: Iterator<Item = char>>(
        &mut self,
        args: &mut Peekable<I>,
    ) -> Result<(), String> {
        let arg = args.peek();
        if arg.is_none() {
            return Err(String::from("bad flag syntax: --"));
        }
        let c = arg.unwrap();
        if *c == '-' || *c == '=' {
            return Err(format!("bad flag syntax: --{}", scan_arg(args)));
        }
        let s = scan_arg(args);
        let split: Vec<&str> = s.splitn(2, '=').collect();
        let name = split[0];

        let i = self.formal.get(name);
        if i.is_none() {
            // TODO: ParseErrorsWhitelist.UnknownFlags
            return Err(format!("unknown flag: --{}", name));
        }
        let i = i.unwrap();
        let flag = self.flags.get(*i).unwrap();
        let no_opt_def_value = flag.no_opt_def_value.clone();

        if split.len() == 2 {
            let val = split[1];
            return self.set(name, val);
        } else if no_opt_def_value != "" {
            return self.set(name, no_opt_def_value);
        }

        let arg = args.peek();
        if arg.is_none() {
            return Err(format!("flag needs an argument: --{}", name));
        }
        let val = scan_arg(args);
        self.set(name, val)
    }

    fn parse_shorthand<I: Iterator<Item = char>>(
        &mut self,
        args: &mut Peekable<I>,
    ) -> Result<(), String> {
        loop {
            let arg = args.next();
            if arg.is_none() {
                return Ok(());
            }
            let c = arg.unwrap();
            if c == ' ' {
                return Ok(());
            }

            let i = self.shorthand.get(&c);
            if i.is_none() {
                // TODO: ParseErrorsWhitelist.UnknownFlags
                return Err(format!(
                    "unknown shorthand flag: {} in -{}{}",
                    c,
                    c,
                    scan_arg(args)
                ));
            }
            let i = i.unwrap();
            let flag = self.flags.get(*i).unwrap();
            let name = flag.name.clone();
            let no_opt_def_value = flag.no_opt_def_value.clone();

            let arg = args.peek();
            if arg.is_none() {
                return Err(format!(
                    "flag needs an argument: {} in -{}{}",
                    c,
                    c,
                    scan_arg(args)
                ));
            }

            let c = arg.unwrap();
            if *c == '=' {
                args.next();
                return self.set(name, scan_arg(args));
            } else if no_opt_def_value != "" {
                self.set(name, no_opt_def_value)?;
            } else if *c != ' ' {
                return self.set(name, scan_arg(args));
            } else {
                args.next();
                return self.set(name, scan_arg(args));
            }
        }
    }

    #[doc = "bool defines a bool flag with specified name, default value, and usage string."]
    pub fn bool<S: Into<String>, U: Into<String>>(&mut self, name: S, value: bool, usage: U) {
        self.add_flag(Flag {
            name: name.into(),
            shorthand: char::default(),
            usage: usage.into(),
            value: Box::new(value),
            def_value: value.to_string(),
            changed: false,
            no_opt_def_value: String::from("true"),
            deprecated: String::new(),
            hidden: false,
            shorthand_deprecated: String::new(),
        })
    }

    #[doc = "bool_p is like bool, but accepts a shorthand letter that can be used after a single dash."]
    pub fn bool_p<S, U>(&mut self, name: S, shorthand: char, value: bool, usage: U)
    where
        S: Into<String>,
        U: Into<String>,
    {
        self.add_flag(Flag {
            name: name.into(),
            shorthand,
            usage: usage.into(),
            value: Box::new(value),
            def_value: value.to_string(),
            changed: false,
            no_opt_def_value: String::from("true"),
            deprecated: String::new(),
            hidden: false,
            shorthand_deprecated: String::new(),
        })
    }

    #[doc = "bool_slice defines a `Slice<bool>` flag with specified name, default value, and usage string."]
    pub fn bool_slice<S: Into<String>, U: Into<String>>(
        &mut self,
        name: S,
        value: value::Slice<bool>,
        usage: U,
    ) {
        self.var(name, value, usage)
    }

    #[doc = "bool_p_slice is like bool_slice, but accepts a shorthand letter that can used after a single dash."]
    pub fn bool_p_slice<S: Into<String>, U: Into<String>>(
        &mut self,
        name: S,
        shorthand: char,
        value: value::Slice<bool>,
        usage: U,
    ) {
        self.var_p(name, shorthand, value, usage)
    }

    #[doc = "Defines a `time::Duration` flag with specified name, default value, and usage string."]
    pub fn duration<S: Into<String>, U: Into<String>>(
        &mut self,
        name: S,
        value: time::Duration,
        usage: U,
    ) {
        self.var(name, value, usage)
    }

    #[doc = "duration_p is like duration, but accepts a shorthand letter that can be used after a single dash."]
    pub fn duration_p<S, U>(&mut self, name: S, shorthand: char, value: time::Duration, usage: U)
    where
        S: Into<String>,
        U: Into<String>,
    {
        self.var_p(name, shorthand, value, usage)
    }

    #[doc = "duration_slice defines a `Slice<time::Duration>` flag with specified name, default value, and usage string."]
    pub fn duration_slice<S: Into<String>, U: Into<String>>(
        &mut self,
        name: S,
        value: value::Slice<time::Duration>,
        usage: U,
    ) {
        self.var(name, value, usage)
    }

    #[doc = "duration_p_slice is like duration_slice, but accepts a shorthand letter that can used after a single dash."]
    pub fn duration_p_slice<S: Into<String>, U: Into<String>>(
        &mut self,
        name: S,
        shorthand: char,
        value: value::Slice<time::Duration>,
        usage: U,
    ) {
        self.var_p(name, shorthand, value, usage)
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
    builtin_flag_val!(ip_addr, IpAddr);
    builtin_flag_val!(ip_v4_addr, Ipv4Addr);
    builtin_flag_val!(ip_v6_addr, Ipv6Addr);
    builtin_flag_val!(socket_addr, SocketAddr);
    builtin_flag_val!(socket_addr_v4, SocketAddrV4);
    builtin_flag_val!(socket_addr_v6, SocketAddrV6);

    /// A helper method for creating flags with a custom `Value` implementation.
    ///
    /// ```
    /// # use std::fmt;
    ///
    /// #[derive(Debug)]
    /// pub struct Complex(f64, f64);
    ///
    /// impl pflag::Value for Complex {
    ///     fn set(&mut self, _: std::string::String) -> std::result::Result<(), pflag::ValueError> { todo!() }
    ///
    ///     fn value(&self) -> &dyn std::any::Any { self }
    /// }
    ///
    /// impl fmt::Display for Complex {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "{}+{}i", self.0, self.1)
    ///     }
    /// }
    ///
    /// let mut flags = pflag::FlagSet::new("custom");
    /// flags.var("complex_number", Complex(0.0, 0.0), "a complex number");
    /// ```
    pub fn var<N, V, U>(&mut self, name: N, value: V, usage: U)
    where
        N: Into<String>,
        V: Value + 'static,
        U: Into<String>,
    {
        let s = value.to_string();
        self.add_flag(Flag {
            name: name.into(),
            shorthand: char::default(),
            usage: usage.into(),
            value: Box::new(value),
            def_value: s,
            changed: false,
            no_opt_def_value: String::new(),
            deprecated: String::new(),
            hidden: false,
            shorthand_deprecated: String::new(),
        })
    }

    /// A helper method for creating flags with a custom `Value` implementation.
    pub fn var_p<N, V, U>(&mut self, name: N, shorthand: char, value: V, usage: U)
    where
        N: Into<String>,
        V: Value + 'static,
        U: Into<String>,
    {
        let s = value.to_string();
        self.add_flag(Flag {
            name: name.into(),
            shorthand,
            usage: usage.into(),
            value: Box::new(value),
            def_value: s,
            changed: false,
            no_opt_def_value: String::new(),
            deprecated: String::new(),
            hidden: false,
            shorthand_deprecated: String::new(),
        })
    }

    /// value_of retrieves a reference to the value for the given flag.
    ///
    /// ```
    /// let mut flags = pflag::FlagSet::new("example");
    /// flags.string("hello", "world".to_string(), "example");
    ///
    /// let val = flags.value_of::<String>("hello").unwrap();
    /// assert_eq!(*val, "world");
    /// ```
    pub fn value_of<T: 'static>(&self, name: &str) -> Result<&T, UnknownFlag> {
        let i = self
            .formal
            .get(name)
            .ok_or(format!("flag does not exist: {}", name))?;
        self.flags[*i]
            .value
            .value()
            .downcast_ref::<T>()
            .ok_or_else(|| {
                let type_name = std::any::type_name_of_val(self);
                let t_name = &type_name[(type_name
                    .rfind(':')
                    .map(|v| v as isize)
                    .unwrap_or_else(|| -1)
                    + 1) as usize..];
                let msg = format!("unable to downcast to type: {}", t_name);
                UnknownFlag::from(msg)
            })
    }
}

/// UnknownFlag represents the lookup or invalid
/// downcasting of an unknown flag.
#[derive(Debug)]
pub struct UnknownFlag(String);

impl error::Error for UnknownFlag {}

impl fmt::Display for UnknownFlag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unknown flag error: {}", self.0)
    }
}

impl<T: Into<String>> From<T> for UnknownFlag {
    fn from(s: T) -> Self {
        Self(s.into())
    }
}

/// FlagSet implements fmt::Display to format the
/// usage for all the flags in the set.
impl fmt::Display for FlagSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        let mut lines: Vec<String> = Vec::new();

        let mut max_len = 0;
        self.visit_all(|flag| {
            if flag.hidden {
                return;
            }

            let mut line = format!("      --{}", flag.name);
            if flag.shorthand != char::default() && flag.shorthand_deprecated == "" {
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

fn unquote_usage(flag: &Flag) -> (String, String) {
    let usage = flag.usage.clone();
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
    use test::Bencher;

    #[test]
    fn parse_long_with_eq() {
        let mut flags = FlagSet::new("test");
        flags.string("hello", "".to_string(), "test");

        if let Err(err) = flags.parse(vec!["--hello=world"]) {
            panic!(err);
        }

        assert_eq!(
            *flags.value_of::<String>("hello").unwrap(),
            "world".to_string()
        );
    }

    #[test]
    fn parse_long_arg_with_space() {
        let mut flags = FlagSet::new("test");
        flags.string("hello", "".to_string(), "test");

        if let Err(err) = flags.parse(vec!["--hello", "world"]) {
            panic!(err);
        }

        assert_eq!(
            *flags.value_of::<String>("hello").unwrap(),
            "world".to_string()
        );
    }

    #[test]
    fn parse_long_arg_optional() {
        let mut flags = FlagSet::new("test");
        flags.bool("hello", false, "test");

        if let Err(err) = flags.parse(vec!["--hello"]) {
            panic!(err);
        }

        assert_eq!(*flags.value_of::<bool>("hello").unwrap(), true);
    }

    #[test]
    fn parse_long_arg_default() {
        let mut flags = FlagSet::new("test");
        flags.bool("hello", true, "test");

        if let Err(err) = flags.parse(vec![]) {
            panic!(err);
        }

        assert_eq!(*flags.value_of::<bool>("hello").unwrap(), true);
    }

    #[test]
    fn parse_short_with_eq() {
        let mut flags = FlagSet::new("test");
        flags.bool_p("help", 'h', false, "test");

        if let Err(err) = flags.parse(vec!["-h=true"]) {
            panic!(err);
        }

        assert_eq!(*flags.value_of::<bool>("help").unwrap(), true);
    }

    #[test]
    fn parse_short_wo_val() {
        let mut flags = FlagSet::new("test");
        flags.bool_p("help", 'h', false, "test");

        if let Err(err) = flags.parse(vec!["-h"]) {
            panic!(err);
        }

        assert_eq!(*flags.value_of::<bool>("help").unwrap(), true);
    }

    #[test]
    fn parse_short_multiple() {
        let mut flags = FlagSet::new("test");
        flags.bool_p("help", 'h', false, "test");
        flags.bool_p("verbose", 'v', false, "test");

        if let Err(err) = flags.parse(vec!["-vh"]) {
            panic!(err);
        }

        assert_eq!(*flags.value_of::<bool>("help").unwrap(), true);
        assert_eq!(*flags.value_of::<bool>("verbose").unwrap(), true);
    }

    #[test]
    fn parse_short_multiple_with_eq() {
        let mut flags = FlagSet::new("test");
        flags.bool_p("help", 'h', false, "test");
        flags.bool_p("verbose", 'v', false, "test");

        if let Err(err) = flags.parse(vec!["-vh=false"]) {
            panic!(err);
        }

        assert_eq!(*flags.value_of::<bool>("help").unwrap(), false);
        assert_eq!(*flags.value_of::<bool>("verbose").unwrap(), true);
    }

    #[test]
    fn parse_short_wo_eq() {
        let mut flags = FlagSet::new("test");
        flags.uint32_p("port", 'p', 0, "test");

        if let Err(err) = flags.parse(vec!["-p8080"]) {
            panic!(err);
        }

        assert_eq!(*flags.value_of::<u32>("port").unwrap(), 8080);
    }

    #[test]
    fn parse_ignore_positional_args() {
        let mut flags = FlagSet::new("test");

        if let Err(err) = flags.parse(vec!["hello", "world"]) {
            panic!(err);
        }

        let args = flags.args();
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], "hello");
        assert_eq!(args[1], "world");
    }

    #[test]
    fn parse_single_dash_stdin() {
        let mut flags = FlagSet::new("test");

        if let Err(err) = flags.parse(vec!["-"]) {
            panic!(err);
        }

        let args = flags.args();
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], "-");
    }

    #[test]
    fn parse_terminate_flags() {
        let mut flags = FlagSet::new("test");

        if let Err(err) = flags.parse(vec!["--", "hello", "world"]) {
            panic!(err);
        }

        let args = flags.args();
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], "hello");
        assert_eq!(args[1], "world");
    }

    #[test]
    fn parse_multi_val_flag_with_comma() {
        let mut flags = FlagSet::new("test");
        flags.bool_slice("bools", Slice::new(), "test");

        if let Err(err) = flags.parse(vec!["--bools=true,false,true"]) {
            panic!(err);
        }

        let bools = flags.value_of::<Slice<bool>>("bools").unwrap();
        assert_eq!(bools.len(), 3);
    }

    #[test]
    fn parse_multi_val_flag_with_comma_and_quotes() {
        let mut flags = FlagSet::new("test");
        flags.bool_slice("bools", Slice::new(), "test");

        if let Err(err) = flags.parse(vec!["--bools=\"true,false,true\""]) {
            panic!(err);
        }

        let bools = flags.value_of::<Slice<bool>>("bools").unwrap();
        assert_eq!(bools.len(), 3);
    }

    #[test]
    fn parse_multi_val_flag_use() {
        let mut flags = FlagSet::new("test");
        flags.bool_slice("bools", Slice::new(), "test");

        if let Err(err) = flags.parse(vec!["--bools=true", "--bools=false", "--bools=true"]) {
            panic!(err);
        }

        let bools = flags.value_of::<value::Slice<bool>>("bools").unwrap();
        assert_eq!(bools.len(), 3);
    }

    #[test]
    fn parse_multi_val_flag_override_defaults() {
        let mut flags = FlagSet::new("test");
        flags.bool_slice("bools", Slice::from([true, false, true]), "test");

        if let Err(err) = flags.parse(vec!["--bools=true"]) {
            panic!(err);
        }

        let bools = flags.value_of::<Slice<bool>>("bools").unwrap();
        assert_eq!(bools.len(), 1);
    }

    #[test]
    fn parse_arg_after_shorthand() {
        let mut flags = FlagSet::new("test");
        flags.int8_p("int", 'i', 0, "test");

        if let Err(err) = flags.parse(vec!["-i=1", "test"]) {
            panic!(err);
        }

        let int = flags.value_of::<i8>("int").unwrap();
        assert_eq!(*int, 1);
        assert_eq!(flags.args().len(), 1);
    }

    #[test]
    fn parse_arg_after_shorthand_with_space() {
        let mut flags = FlagSet::new("test");
        flags.int8_p("int", 'i', 0, "test");

        if let Err(err) = flags.parse(vec!["-i", "1", "test"]) {
            panic!(err);
        }

        let int = flags.value_of::<i8>("int").unwrap();
        assert_eq!(*int, 1);
        assert_eq!(flags.args().len(), 1);
    }

    #[test]
    fn duration_value() {
        let mut flags = FlagSet::new("test");
        flags.duration("time", time::Duration::new(1, 0), "test");

        let val = flags.value_of::<time::Duration>("time").unwrap();
        assert_eq!(val.as_secs(), 1);
    }

    #[bench]
    fn bench_parse(b: &mut Bencher) {
        let mut flags = FlagSet::new("bench");
        flags.int8("num", 0, "test");
        flags.string_p("str", 's', "".to_string(), "test");
        flags.bool_slice("bool", Slice::new(), "test");
        flags.f64_p_slice("floats", 'f', Slice::new(), "test");

        // --num=2 -shello --bool true --bool false -f=1.0 -f 2.0,3.0,4.0 --floats=3.14
        let args = [
            "--num=2",
            "-shello",
            "--bool",
            "true",
            "--bool",
            "false",
            "-f=1.0",
            "-f",
            "2.0,3.0,4.0",
            "--floats=3.14",
        ];

        b.iter(|| {
            if let Err(err) = flags.parse(args.iter().map(|s| *s)) {
                panic!(err);
            }
        });
    }

    #[bench]
    fn bench_value_of(b: &mut Bencher) {
        let mut flags = FlagSet::new("bench");
        flags.int8("num", 0, "test");
        flags.string_p("str", 's', "".to_string(), "test");
        flags.bool_slice("bool", Slice::new(), "test");
        flags.f64_p_slice("floats", 'f', Slice::new(), "test");

        // --num=2 -shello --bool true --bool false -f=1.0 -f 2.0,3.0,4.0 --floats=3.14
        let args = [
            "--num=2",
            "-shello",
            "--bool",
            "true",
            "--bool",
            "false",
            "-f=1.0",
            "-f",
            "2.0,3.0,4.0",
            "--floats=3.14",
        ];

        if let Err(err) = flags.parse(args.iter().map(|s| *s)) {
            panic!(err);
        }

        b.iter(|| {
            if let Err(_) = flags.value_of::<i8>("num") {
                panic!("expected i8 for --num");
            }
            if let Err(_) = flags.value_of::<String>("str") {
                panic!("expected String for --str");
            }
            if let Err(_) = flags.value_of::<Slice<bool>>("bool") {
                panic!("expected bool for --bool");
            }
            if let Err(_) = flags.value_of::<Slice<f64>>("floats") {
                panic!("expected Slice<f64> for --floats");
            }
        });
    }
}
