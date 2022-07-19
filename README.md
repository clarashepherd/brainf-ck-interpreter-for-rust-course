A fully functioning interpreter for the
[Brainfuck](https://en.wikipedia.org/wiki/Brainfuck#:~:text=Brainfuck%20is%20an%20esoteric%20programming,Esoteric%2C%20imperative%2C%20structured)
language.

Includes a full suite of unit and integration tests.

Currently handles u8 and u16 data types, but could handle others with a few
`impl` blocks.

All arguments are available with the `-h` flag. They include the option for the
number of data cells in the VM, and the option to auto-extend the VM's tape.

All handles are errored without panicking.
