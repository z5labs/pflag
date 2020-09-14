[![Documentation](https://docs.rs/pflag/badge.svg)](https://docs.rs/pflag)

# pflag

`pflag` is a port of the [spf13](https://github.com/spf13/pflag)'s popular fork of the
Go package by the same name.

## Usage

```rust
use pflag::{FlagSet, Slice};
use std::net::{IpAddr, Ipv4Addr};

let mut flags = FlagSet::new("name");

// Use higher level methods over add_flag directly.
flags.int8("num", 0, "a flag for a number");
flags.string_p("str", 's', String::from("default value"), "a flag for a String and has a shorthand");
flags.ip_addr_slice(
    "addrs",
    Slice::from([IpAddr::V4(Ipv4Addr::new(0,0,0,0)), IpAddr::V4(Ipv4Addr::new(127,0,0,1))]),
    "a multi-valued flag",
);

let args = "--num=1 -s world --addrs 192.168.1.1,192.168.0.1 --addrs=127.0.0.1 subcommand";
if let Err(err) = flags.parse(args.split(' ')) {
    panic!(err);
}

// Retrieving value is very easy with the value_of method.
assert_eq!(*flags.value_of::<i8>("num").unwrap(), 1);
assert_eq!(*flags.value_of::<String>("str").unwrap(), "world");
assert_eq!(flags.value_of::<Slice<IpAddr>>("addrs").unwrap().len(), 3);

// Any non-flag args i.e. positional args can be retrieved by...
let args = flags.args();
assert_eq!(args.len(), 1);
assert_eq!(args[0], "subcommand");
```
