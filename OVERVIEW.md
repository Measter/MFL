# Types

## Integers

Integer types are:

|Signed|Unsigned|
|---|---|
|`s8`|`u8`|
|`s16`|`u16`|
|`s32`|`u32`|
|`s64`|`u64`|

The language does have implicit integer widening. In integer of type `A` can widen into `B` if the following is true:

* `B`s width is greater than `A`s width
* (`B` is signed and `A` is unsigned) OR (`B` and `A` are the same signedness).

## Booleans

Boolean values have the type `bool`.

## Pointers

Pointers notation is `ptr(T)`, where `T` is some type.

## Arrays

Arrays are `T[N]`, where `T` is some type, and `N` is a positive integer.

## Strings

C-like strings are just a `ptr(u8)`, MFL-strings are the following struct:

```
struct String is
    field len u64
    field data ptr(u8)
end
```

## Structs

Structs are defined with the syntax

```
struct <name> is 
    field <name> <type>
    ...
end
```

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
|`uN`|`ptr(T)`|`ptr(T)`|
|`ptr(T)`|`uN`|`ptr(T)`|

### `-` (Subtract)

Stack: `[a b]` to `[c]`

Operation: `c` = `a` - `b`

Supported Types:

|a|b|c|
|---|---|---|
|`iN`|`iN`|`iN`|
|`ptr(T)`|`ptr(T)`|`u64`|
|`ptr(T)`|`uN`|`ptr(T)`|

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
|`ptr(T)`|`ptr(T)`|`bool`|


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
|`ptr(T)`|`ptr(T)`|`bool`|

## Memory

### `@` (Load)

Stack: `[a]` to `[b]`

Operation: `b` = *`a`

Supported Types:

|a|b|
|---|---|
|`ptr(T)`|`T`|

### `!` (Store)

Stack: `[a b]` to `[]`

Operation: *`b` = `a`

Supported Types:

|a|b|
|---|---|
|`T`|`ptr(T)`|

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

Stores a value into an array at the given runtime index.

Stack(`ins`): `[a b c]` to `[d]`

Stack(`insd`): `[a b c]` to `[]`

Operation:

* `b[c]` = `a`
* `d` = `b`

Supported Types:

|a|b|c|d|
|---|---|---|---|
|`T`|`T[N]`|`uN`|`T[N]`|
|`T`|`ptr(T[N])`|`uN`|`ptr(T[N])`|

### `xtr`, `xtrd` (Extract from Array)

Retrieves a value from an array at the given runtime index.

Stack(`xtr`): `[a b]` to `[c d]`

Stack(`xtrd`): `[a b]` to `[d]`

Operation:

* `d` = `a[b]`
* `c` = `a`

Supported Types:

|a|b|c|d|
|---|---|---|---|
|`T[N]`|`uN`|`T[N]`|`T`|
|`ptr(T[N])`|`uN`|`ptr(T[N])`|`T`|

### `ins(Field)`, `insd(Field)` (Insert into Struct)

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
|`F`|`ptr(T)`|`ptr(T)`|

### `xtr(Field)`, `xtrd(Field)` (Extract from Struct)

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
|`ptr(T)`|`ptr(T)`|`F`|

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