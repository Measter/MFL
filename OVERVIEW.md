# Types

## Integers

Integer types are:

|Signed|Unsigned|
|---|---|
|`s8`|`u8`|
|`s16`|`u16`|
|`s32`|`u32`|
|`s64`|`u64`|

MFL supports binary (`0b101`, `0B101`), octal (`0o101`), decimal, and hex (`0x101`, `0X101`) literals.

The language does have implicit integer widening. In integer of type `A` can widen into `B` if the following is true:

* `B`s width is greater than `A`s width
* (`B` is signed and `A` is unsigned) OR (`B` and `A` are the same signedness).

## Floats

The supported floating point types are `f32` and `f64`. Literals must have both integer and decimal parts (that is,
they must be of the form `1.1`), and may have an optional exponent suffux (`1.1e23`).

## Booleans

Boolean values have the type `bool`.

## Single Pointers

Single-Pointer notation is `T&`, where `T` is some type. Single-pointers can be null, and do not require the pointee to be
initialized.

## Multi Pointers

Multi-Pointer notation is `T*`, where `T` is some type. Multi-pointers are like Single-pointers, with the additional
support of pointer arithmetic.

## Arrays

Arrays are `T[N]`, where `T` is some type, and `N` is a positive integer.

## Strings

Strings are the following struct:

```
struct String {
    length u64,
    pointer u8*,
}
```

## Structs

Structs are defined with the following syntax

```
struct <name> {
    <name> <type>,
    ...
}
```

Note that trailing commas are not optional.

# Supported Operations

Note that the type notation for integers in this section are as follows:

* `i` means both signed and unsigned
* `N` means any width


## Arithmetic

### `+`(Add)

Stack: `[a b]` to `[c]`

Operation: `c` = `a` + `b`

Supported Types:

|a|b|c|
|---|---|---|
|`iN`|`iN`|`iN`|
|`uN`|`T*`|`T*`|
|`T*`|`uN`|`T*`|

### `-` (Subtract)

Stack: `[a b]` to `[c]`

Operation: `c` = `a` - `b`

Supported Types:

|a|b|c|
|---|---|---|
|`iN`|`iN`|`iN`|
|`T*`|`T*`|`u64`|
|`T*`|`uN`|`T*`|

### `*` (Multiplication), `/` (Division), `%` (Remainder)

Stack: `[a b]` to `[c]`

Operation: `c` = `a` * `b`    
Operation: `c` = `a` / `b`    
Operation: `c` = `a` % `b`

Supported Types:

|a|b|c|
|---|---|---|
|`iN`|`iN`|`iN`|

## Bitwise

### `or`, `and`, `xor`

Stack: `[a b]` to `[c]`

Operation (`or`): `c` = `a` | `b`   
Operation (`and`): `c` = `a` & `b`
Operation (`xor`): `c` = `a` ^ `b`

Supported Types:

|a|b|c|
|---|---|---|
|`iN`|`iN`|`iN`|
|`bool`|`bool`|`bool`|

### `not`

Stack: `[a]` to `[b]`

Operation: `b` = !`a`

Supported Types:

|a|b|
|---|---|
|`iN`|`iN`|
|`bool`|`bool`|

### `shl` (Shift Left), `shr` (Shift Right)

Stack: `[a b]` to `[c]`

Operation (`shl`): `c` = `a` << `b`
Operation (`shr`): `c` = `a` >> `b`

Supported Types:

|a|b|c|
|---|---|---|
|`iN`|`iN`|`iN`|


## Comparison

### `=`, `!=`

Stack: `[a b]` to `[c]`

Operation: `c` = `a` == `b`
Operation: `c` = `a` != `b`

Supported Types:

|a|b|c|
|---|---|---|
|`iN`|`iN`|`bool`|
|`bool`|`bool`|`bool`|
|`T&`|`T&`|`bool`|
|`T*`|`T*`|`bool`|


### `<`, `>`, `<=` `>=`

Stack: `[a b]` to `[c]`

Operation: `c` = `a` < `b`    
Operation: `c` = `a` > `b`    
Operation: `c` = `a` <= `b`    
Operation: `c` = `a` >= `b`

Supported Types:

|a|b|c|
|---|---|---|
|`iN`|`iN`|`bool`|
|`T*`|`T*`|`bool`|

## Memory

### `@` (Load)

Stack: `[a]` to `[b]`

Operation: `b` = *`a`

Supported Types:

|a|b|
|---|---|
|`T&`|`T`|
|`T*`|`T`|

### `!` (Store)

Stack: `[a b]` to `[]`

Operation: *`b` = `a`

Supported Types:

|a|b|
|---|---|
|`T`|`T&`|
|`T`|`T*`|

### `pack(N)`

Packs the top `N` values on the stack into an array. All values must have the same type.

Stack: `[v0, v1, .. vN]` to `[c]`

Supported Types:

|vN|c|
|---|---|
|`T`|`T[N]`|

### `pack(T)`

Packs the top values on the stack into an instance of `Struct`. The number of values taken is
the number of fields the struct has, in the same order.

Stack: `[v0, v1, .. vN]` to `[c]`

Supported Types:

|vN|c|
|---|---|
|`F`|`T`|

### `unpack`

Unpacks an array of length `N` into separate values on the stack.

Stack: `[a]` to `[v0, v1, .. vN]`

Supported Types:

|a|vN|
|---|---|
|`T[N]`|`T`|

### `ins`, `insd` (Insert into Array)

Stores a value into an array or slice-like struct (a struct with a `pointer` and `length` field) at the given runtime index.

Stack(`ins`): `[a b c]` to `[d]`

Stack(`insd`): `[a b c]` to `[]`

Operation:

* `b[c]` = `a`
* `d` = `b`

Supported Types:

|a|b|c|d|
|---|---|---|---|
|`T`|`T[N]`|`uN`|`T[N]`|
|`T`|`T[N]&`|`uN`|`T[N]&`|
|`T`|`T[N]*`|`uN`|`T[N]*`|
|`T`|`U`|`uN`|`U`|
|`T`|`U&`|`uN`|`U&`|
|`T`|`U*`|`uN`|`U*`|

### `xtr`, `xtrd` (Extract from Array)

Retrieves a value from an array or slice-like struct (a struct with a `pointer` and `length` field) at the given runtime index.

Stack(`xtr`): `[a b]` to `[c d]`

Stack(`xtrd`): `[a b]` to `[d]`

Operation:

* `d` = `a[b]`
* `c` = `a`

Supported Types:

|a|b|c|d|
|---|---|---|---|
|`T[N]`|`uN`|`T[N]`|`T`|
|`T[N]&`|`uN`|`T[N]&`|`T`|
|`T[N]*`|`uN`|`T[N]*`|`T`|
|`U`|`uN`|`U`|`T`|
|`U&`|`uN`|`U&`|`T`|
|`U*`|`uN`|`U*`|`T`|

### `ins(Field[.Field]*)`, `insd(Field[.Field]*)` (Insert into Struct)

Stores a value to field `Field` in a value of struct `T`

Stack(`ins`): `[a b]` to `[c]`

Stack(`insd`): `[a b]` to `[]`

Operation:

* `b.Field` = `a`
* `c` = `b`

Supported Types:

|a|b|c|
|---|---|---|
|`F`|`T`|`T`|
|`F`|`T&`|`T&`|
|`F`|`T*`|`T*`|

### `xtr(Field[.Field]*)`, `xtrd(Field[.Field]*)` (Extract from Struct)

Retrieves a value from a struct at the given field.

Stack(`xtr`): `[a]` to `[b c]`

Stack(`xtrd`): `[a]` to `[c]`

Operation:

* `c` = `a.Field`
* `b` = `a`

Supported Types:

|a|b|c|
|---|---|---|
|`T`|`T`|`F`|
|`T&`|`T&`|`F`|
|`T*`|`T*`|`F`|

### `.Field` (Field access)

Gets a pointer to the given field from a pointer to a struct.

Stack: `a` to `b`

Operation:

* `b` = `&a.Field`

Supported Types:
|a|b|
|`T*`|`F&`|
|`T&`|`F&`|

## Stack Manipulation

### `drop(N)`

Drops the top N values from the stack. If `N` is not provided, defaults to 1.

Stack: `[a0, .. aN]` to `[]`

### `dup(N)`

Duplicates the top N values from the stack. If `N` is not provided, defaults to 1.

Stack: `[a0, .. aN]` to `[a0, .. aN, a0, .. aN]`

### `over(N)`

Duplicates the Nth from the top of stack. If `N` is not provided, defaults to 1.

Stack: `[a, b]` to `[a, b, a]`

### `rev(N)`

Reverses the top N values on stack. If `N` is not provided, defaults to 2.

Stack: `[a, b, c]` to `[c, b, a]`

### `rot(N D S)`

Rotates the top `N` values in direction `D`, by `S` steps.

* `N` must be a positive integer.
* `D` must be either `<` on `>`.
* `S` must be a positive integer.

Stack: `[a, b, c]` to `[b, c, a]`

### `swap(N)`

Swaps the top `N` values with the `N` values below them. Defaults to 1.

Stack: `[a, b, c, d]` to `[c, d, a, b]`

### `stktrc(bool)`

Causes the compiler to print the current values and types on the stack. The boolean controls whether
labels for each value are emitted. Defaults to false.