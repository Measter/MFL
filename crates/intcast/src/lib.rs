pub trait IntCast {
    type I8;
    type U8;
    type I16;
    type U16;
    type I32;
    type U32;
    type I64;
    type U64;
    type I128;
    type U128;
    type Isize;
    type Usize;

    fn to_i8(self) -> Self::I8;
    fn to_u8(self) -> Self::U8;

    fn to_i16(self) -> Self::I16;
    fn to_u16(self) -> Self::U16;

    fn to_i32(self) -> Self::I32;
    fn to_u32(self) -> Self::U32;

    fn to_i64(self) -> Self::I64;
    fn to_u64(self) -> Self::U64;

    fn to_i128(self) -> Self::I128;
    fn to_u128(self) -> Self::U128;

    fn to_isize(self) -> Self::Isize;
    fn to_usize(self) -> Self::Usize;
}

include!(concat!(env!("OUT_DIR"), "/impl.rs"));
