use std::mem;
use std::cmp::Ordering;

use bytes::{Bytes, BytesMut, Buf, BufMut};

#[derive(Debug, PartialEq)]
pub enum Error {
    IllegalArgumentError(String),
    RuntimeError(String),
}

#[derive(Clone, Copy, Debug, PartialEq, FromPrimitive, ToPrimitive)]
pub enum TypeId {
    Bool,
    Int,
    Long,
    Float,
    String,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
    type_id: TypeId,
    size_in_bytes: usize,
}

impl Type {
    pub fn new(type_id: TypeId, size_in_bytes: usize) -> Self {
        Self {
            type_id,
            size_in_bytes,
        }
    }

    pub fn bool_type() -> Self {
        Self::new(TypeId::Bool, mem::size_of::<bool>())
    }

    pub fn int_type() -> Self {
        Self::new(TypeId::Int, mem::size_of::<i32>())
    }

    pub fn long_type() -> Self {
        Self::new(TypeId::Long, mem::size_of::<i64>())
    }

    pub fn float_type() -> Self {
        Self::new(TypeId::Float, mem::size_of::<f32>())
    }

    pub fn string_type(n: usize) -> Result<Self, Error> {
        if n == 0 {
            let e = Error::IllegalArgumentError("Empty strings are not supported.".to_string());
            return Err(e);
        }
        Ok(Self::new(TypeId::String, n))
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut buf = BytesMut::new();
        buf.put_slice(bytes);

        let type_id_ordinal = buf.get_u32();
        let size_in_bytes = buf.get_u32() as usize;

        match num::FromPrimitive::from_u32(type_id_ordinal) {
            Some(type_id) => match type_id {
                TypeId::Bool => Ok(Self::bool_type()),
                TypeId::Int => Ok(Self::int_type()),
                TypeId::Long => Ok(Self::long_type()),
                TypeId::Float => Ok(Self::float_type()),
                TypeId::String => Self::string_type(size_in_bytes),
            },
            None => Err(Error::RuntimeError("unreachable.".to_string())),
        }
    }

    pub fn get_type_id(&self) -> TypeId {
        self.type_id
    }

    pub fn get_size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }

    pub fn to_bytes(&self) -> Bytes {
        let mut buf = BytesMut::with_capacity(mem::size_of::<u32>() * 2);
        buf.put_u32((self.type_id as usize) as u32);
        buf.put_u32(self.size_in_bytes as u32);
        buf.into()
    }
}

#[derive(Clone, Debug)]
pub enum DataBox {
    Bool(bool),
    Int(i32),
    Long(i64),
    Float(f32),
    String(String, usize),
}

impl DataBox {
    pub fn bool_databox(v: bool) -> Self {
        Self::Bool(v)
    }

    pub fn int_databox(v: i32) -> Self {
        Self::Int(v)
    }

    pub fn long_databox(v: i64) -> Self {
        Self::Long(v)
    }

    pub fn float_databox(v: f32) -> Self {
        Self::Float(v)
    }

    pub fn string_databox(v: String, n: usize) -> Result<Self, Error> {
        if n == 0 {
            return Err(Error::IllegalArgumentError(format!("Cannot construct a {}-byte string. Strings must be at least one byte.", n).to_string()));
        }
        Ok(Self::String(v, n))
    }

    pub fn get_type(&self) -> Result<Type, Error> {
        match self {
            Self::Bool(_) => Ok(Type::bool_type()),
            Self::Int(_) => Ok(Type::int_type()),
            Self::Long(_) => Ok(Type::long_type()),
            Self::Float(_) => Ok(Type::float_type()),
            Self::String(_, n) => Type::string_type(*n),
        }
    }

    pub fn get_type_id(&self) -> TypeId {
        match self {
            Self::Bool(_) => TypeId::Bool,
            Self::Int(_) => TypeId::Int,
            Self::Long(_) => TypeId::Long,
            Self::Float(_) => TypeId::Float,
            Self::String(_, _) => TypeId::String,
        }
    }

    pub fn get_bool(&self) -> Result<bool, Error> {
        match self {
            Self::Bool(v) => Ok(*v),
            _ => Err(Error::RuntimeError("not bool type".to_string())),
        }
    }

    pub fn get_int(&self) -> Result<i32, Error> {
        match self {
            Self::Int(v) => Ok(*v),
            _ => Err(Error::RuntimeError("not int type".to_string())),
        }
    }

    pub fn get_long(&self) -> Result<i64, Error> {
        match self {
            Self::Long(v) => Ok(*v),
            _ => Err(Error::RuntimeError("not Long type".to_string())),
        }
    }

    fn get_float(&self) -> Result<f32, Error> {
        match self {
            Self::Float(v) => Ok(*v),
            _ => Err(Error::RuntimeError("not float type".to_string())),
        }
    }

    fn get_string(&self) -> Result<String, Error> {
        match self {
            Self::String(v, _) => Ok(v.to_string()),
            _ => Err(Error::RuntimeError("not String type".to_string())),
        }
    }

    fn to_bytes(&self) -> Bytes {
        match self {
            Self::Bool(v) => {
                let mut buf = BytesMut::with_capacity(1);
                buf.put_u8(u8::from(*v));
                buf.into()
            },
            Self::Int(v) => {
                let mut buf = BytesMut::with_capacity(mem::size_of::<i32>());
                buf.put_slice(&v.to_be_bytes());
                buf.into()
            },
            Self::Long(v) => {
                let mut buf = BytesMut::with_capacity(mem::size_of::<i64>());
                buf.put_slice(&v.to_be_bytes());
                buf.into()
            },
            Self::Float(v) => {
                let mut buf = BytesMut::with_capacity(mem::size_of::<f32>());
                buf.put_slice(&v.to_be_bytes());
                buf.into()
            },
            Self::String(v, n) => {
                let mut buf = BytesMut::with_capacity(*n);
                buf.put_slice(&v.as_bytes());
                buf.into()
            },
        }
    }

    pub fn from_bytes(bytes: &[u8], t: Type) -> Result<DataBox, Error> {
        let mut buf = BytesMut::new();
        buf.put_slice(bytes);

        let type_id = t.get_type_id();

        match type_id {
            TypeId::Bool => {
                let v = buf.get_u8();
                Ok(Self::bool_databox(v == 1))
            },
            TypeId::Int => {
                let v = buf.get_i32();
                Ok(Self::int_databox(v))
            },
            TypeId::Long => {
                let v = buf.get_i64();
                Ok(Self::long_databox(v))
            },
            TypeId::Float => {
                let v = buf.get_f32();
                Ok(Self::float_databox(v))
            },
            TypeId::String => {
                let n = t.get_size_in_bytes();
                match String::from_utf8(buf.to_vec()) {
                    Ok(v) => Self::string_databox(v, n),
                    Err(err) => Err(Error::RuntimeError(err.to_string())),
                }
            },
            _ => Err(Error::RuntimeError(format!("Unhandled TypeId {:?}", type_id).to_string()))
        }
    }
}

impl PartialEq for DataBox {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::Bool(v1) => match other {
                Self::Bool(v2) => v1 == v2,
                _ => false,
            },
            Self::Int(v1) => match other {
                Self::Int(v2) => v1 == v2,
                Self::Long(v2) => *v1 as i64 == *v2,
                Self::Float(v2) => *v1 as f32 == *v2,
                _ => false,
            },
            Self::Long(v1) => match other {
                Self::Int(v2) => *v1 == *v2 as i64,
                Self::Long(v2) => v1 == v2,
                Self::Float(v2) => *v1 as f64 == *v2 as f64,
                _ => false,
            },
            Self::Float(v1) => match other {
                Self::Int(v2) => *v1 == *v2 as f32,
                Self::Long(v2) => *v1 as f64 == *v2 as f64,
                Self::Float(v2) => v1 == v2,
                _ => false,
            },
            Self::String(v1, _) => match other {
                Self::String(v2, _) => v1 == v2,
                _ => false,
            },
        }
    }
}

impl PartialOrd for DataBox {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            Self::Bool(v1) => match other {
                Self::Bool(v2) => Some(v1.cmp(v2)),
                _ => None,
            },
            Self::Int(v1) => match other {
                Self::Int(v2) => Some(v1.cmp(v2)),
                Self::Long(v2) => Some((*v1 as i64).cmp(v2)),
                Self::Float(v2) => (*v1 as f32).partial_cmp(v2),
                _ => None,
            },
            Self::Long(v1) => match other {
                Self::Int(v2) => Some((*v1).cmp(&(*v2 as i64))),
                Self::Long(v2) => Some(v1.cmp(v2)),
                Self::Float(v2) => (*v1 as f64).partial_cmp(&(*v2 as f64)),
                _ => None,
            },
            Self::Float(v1) => match other {
                Self::Int(v2) => (*v1).partial_cmp(&(*v2 as f32)),
                Self::Long(v2) => (*v1 as f64).partial_cmp(&(*v2 as f64)),
                Self::Float(v2) => v1.partial_cmp(v2),
                _ => None,
            },
            Self::String(v1, _) => match other {
                Self::String(v2, _) => v1.partial_cmp(v2),
                _ => None,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bool_type() {
        let bool_type = Type::bool_type();
        assert_eq!(bool_type.get_type_id(), TypeId::Bool);
        assert_eq!(bool_type.get_size_in_bytes(), 1);

        let buf = bool_type.to_bytes();
        assert_eq!(Type::from_bytes(&buf).unwrap(), bool_type);

        // Check equality.
        assert_eq!(bool_type, Type::bool_type());
        assert_ne!(bool_type, Type::int_type());
        assert_ne!(bool_type, Type::float_type());
        assert_ne!(bool_type, Type::string_type(1).unwrap());
        assert_ne!(bool_type, Type::string_type(2).unwrap());
    }

    #[test]
    fn test_int_type() {
        let int_type = Type::int_type();
        assert_eq!(int_type.get_type_id(), TypeId::Int);
        assert_eq!(int_type.get_size_in_bytes(), 4);

        let buf = int_type.to_bytes();
        assert_eq!(Type::from_bytes(&buf).unwrap(), int_type);

        // Check equality.
        assert_ne!(int_type, Type::bool_type());
        assert_eq!(int_type, Type::int_type());
        assert_ne!(int_type, Type::float_type());
        assert_ne!(int_type, Type::string_type(1).unwrap());
        assert_ne!(int_type, Type::string_type(2).unwrap());
    }

    #[test]
    fn test_float_type() {
        let float_type = Type::float_type();
        assert_eq!(float_type.get_type_id(), TypeId::Float);
        assert_eq!(float_type.get_size_in_bytes(), 4);

        let buf = float_type.to_bytes();
        assert_eq!(Type::from_bytes(&buf).unwrap(), float_type);

        // Check equality.
        assert_ne!(float_type, Type::bool_type());
        assert_ne!(float_type, Type::int_type());
        assert_eq!(float_type, Type::float_type());
        assert_ne!(float_type, Type::string_type(1).unwrap());
        assert_ne!(float_type, Type::string_type(2).unwrap());
    }

    #[test]
    fn test_zero_bytes_string_type() {
        assert!(Type::string_type(0).is_err());
    }

    #[test]
    fn test_one_bytes_string_type() {
        let string_type = Type::string_type(1).unwrap();
        assert_eq!(string_type.get_type_id(), TypeId::String);
        assert_eq!(string_type.get_size_in_bytes(), 1);

        let buf = string_type.to_bytes();
        assert_eq!(Type::from_bytes(&buf).unwrap(), string_type);

        // Check equality.
        assert_ne!(string_type, Type::bool_type());
        assert_ne!(string_type, Type::int_type());
        assert_ne!(string_type, Type::float_type());
        assert_eq!(string_type, Type::string_type(1).unwrap());
        assert_ne!(string_type, Type::string_type(2).unwrap());
    }

    #[test]
    fn test_two_bytes_string_type() {
        let string_type = Type::string_type(2).unwrap();
        assert_eq!(string_type.get_type_id(), TypeId::String);
        assert_eq!(string_type.get_size_in_bytes(), 2);

        let buf = string_type.to_bytes();
        assert_eq!(Type::from_bytes(&buf).unwrap(), string_type);

        // Check equality.
        assert_ne!(string_type, Type::bool_type());
        assert_ne!(string_type, Type::int_type());
        assert_ne!(string_type, Type::float_type());
        assert_ne!(string_type, Type::string_type(1).unwrap());
        assert_eq!(string_type, Type::string_type(2).unwrap());
    }

    /**
     * BoolDataBox tests
     */
    #[test]
    fn test_bool_databox_type() {
        assert_eq!(Type::bool_type(), DataBox::bool_databox(true).get_type().unwrap());
        assert_eq!(Type::bool_type(), DataBox::bool_databox(false).get_type().unwrap());
    }

    #[test]
    fn test_bool_databox_get_bool() {
        assert_eq!(true, DataBox::bool_databox(true).get_bool().unwrap());
        assert_eq!(false, DataBox::bool_databox(false).get_bool().unwrap());
    }

    #[test]
    fn test_bool_databox_get_int() {
        assert!(DataBox::bool_databox(true).get_int().is_err());
    }

    #[test]
    fn test_bool_databox_get_float() {
        assert!(DataBox::bool_databox(true).get_float().is_err());
    }

    #[test]
    fn test_bool_databox_get_long() {
        assert!(DataBox::bool_databox(true).get_long().is_err());
    }

    #[test]
    fn test_bool_databox_get_string() {
        assert!(DataBox::bool_databox(true).get_string().is_err());
    }

    #[test]
    fn test_bool_databox_to_and_from_bytes() {
        for v in [true, false] {
            let d1 = DataBox::bool_databox(v);
            let buf = d1.to_bytes();
            let d2 = DataBox::from_bytes(&buf, Type::bool_type()).unwrap();
            assert_eq!(Type::bool_type(), d2.get_type().unwrap());
            assert_eq!(v, d2.get_bool().unwrap());
        }
    }

    #[test]
    fn test_bool_databox_equals() {
        let tru = DataBox::bool_databox(true);
        let fls = DataBox::bool_databox(false);

        assert_eq!(tru, tru);
        assert_eq!(fls, fls);
        assert_ne!(tru, fls);
        assert_ne!(fls, tru);
    }

    #[test]
    fn test_bool_databox_compare() {
        let tru = DataBox::bool_databox(true);
        let fls = DataBox::bool_databox(false);

        assert!(fls == fls);
        assert!(fls < tru);
        assert!(tru == tru);
        assert!(tru > fls);
    }

    /**
     * IntDataBox tests
     */
    #[test]
    fn test_int_databox_type() {
        assert_eq!(Type::int_type(), DataBox::int_databox(0).get_type().unwrap());
    }

    #[test]
    fn test_int_databox_get_bool() {
        assert!(DataBox::int_databox(0).get_bool().is_err());
    }

    #[test]
    fn test_int_databox_get_int() {
        assert_eq!(0, DataBox::int_databox(0).get_int().unwrap());
    }

    #[test]
    fn test_int_databox_get_float() {
        assert!(DataBox::int_databox(0).get_float().is_err());
    }

    #[test]
    fn test_int_databox_get_long() {
        assert!(DataBox::int_databox(0).get_long().is_err());
    }

    #[test]
    fn test_int_databox_get_string() {
        assert!(DataBox::int_databox(0).get_string().is_err());
    }

    #[test]
    fn test_int_databox_to_and_from_bytes() {
        for v in -10..10 {
            let d1 = DataBox::int_databox(v);
            let buf = d1.to_bytes();
            let d2 = DataBox::from_bytes(&buf, Type::int_type()).unwrap();
            assert_eq!(Type::int_type(), d2.get_type().unwrap());
            assert_eq!(v, d2.get_int().unwrap());
        }
    }

    #[test]
    fn test_int_databox_equals() {
        let zero = DataBox::int_databox(0);
        let one = DataBox::int_databox(1);

        assert_eq!(zero, zero);
        assert_eq!(one, one);
        assert_ne!(zero, one);
        assert_ne!(one, zero);
    }

    #[test]
    fn test_int_databox_compare() {
        let zero = DataBox::int_databox(0);
        let one = DataBox::int_databox(1);

        assert!(zero == zero);
        assert!(zero < one);
        assert!(one == one);
        assert!(one > zero);
    }

    /**
     * LongDataBox tests
     */
    #[test]
    fn test_long_databox_type() {
        assert_eq!(Type::long_type(), DataBox::long_databox(0).get_type().unwrap());
    }

    #[test]
    fn test_long_databox_get_bool() {
        assert!(DataBox::long_databox(0).get_bool().is_err());
    }

    #[test]
    fn test_long_databox_get_int() {
        assert!(DataBox::long_databox(0).get_int().is_err());
    }

    #[test]
    fn test_long_databox_get_float() {
        assert!(DataBox::long_databox(0).get_float().is_err());
    }

    #[test]
    fn test_long_databox_get_long() {
        assert_eq!(0, DataBox::long_databox(0).get_long().unwrap());
    }

    #[test]
    fn test_long_databox_get_string() {
        assert!(DataBox::long_databox(0).get_string().is_err());
    }

    #[test]
    fn test_long_databox_to_and_from_bytes() {
        for v in -10..10 {
            let d1 = DataBox::long_databox(v);
            let buf = d1.to_bytes();
            let d2 = DataBox::from_bytes(&buf, Type::long_type()).unwrap();
            assert_eq!(Type::long_type(), d2.get_type().unwrap());
            assert_eq!(v, d2.get_long().unwrap());
        }
    }

    #[test]
    fn test_long_databox_equals() {
        let zero = DataBox::long_databox(0);
        let one = DataBox::long_databox(1);

        assert_eq!(zero, zero);
        assert_eq!(one, one);
        assert_ne!(zero, one);
        assert_ne!(one, zero);
    }

    #[test]
    fn test_long_databox_compare() {
        let zero = DataBox::long_databox(0);
        let one = DataBox::long_databox(1);

        assert!(zero == zero);
        assert!(zero < one);
        assert!(one == one);
        assert!(one > zero);
    }

    /**
     * FloatDataBox tests
     */
    #[test]
    fn test_float_databox_type() {
        assert_eq!(Type::float_type(), DataBox::Float(0 as f32).get_type().unwrap());
    }

    #[test]
    fn test_float_databox_get_bool() {
        assert!(DataBox::Float(0 as f32).get_bool().is_err());
    }

    #[test]
    fn test_float_databox_get_int() {
        assert!(DataBox::Float(0 as f32).get_int().is_err());
    }

    #[test]
    fn test_float_databox_get_float() {
        assert_eq!(0 as f32, DataBox::Float(0 as f32).get_float().unwrap());
    }

    #[test]
    fn test_float_databox_get_long() {
        assert!(DataBox::Float(0 as f32).get_long().is_err());
    }

    #[test]
    fn test_float_databox_get_string() {
        assert!(DataBox::Float(0 as f32).get_string().is_err());
    }

    #[test]
    fn test_float_databox_to_and_from_bytes() {
        for v in -10..10 {
            let d1 = DataBox::Float(v as f32);
            let buf = d1.to_bytes();
            let d2 = DataBox::from_bytes(&buf, Type::float_type()).unwrap();
            assert_eq!(Type::float_type(), d2.get_type().unwrap());
            assert_eq!(v as f32, d2.get_float().unwrap());
        }
    }

    #[test]
    fn test_float_databox_equals() {
        let zero = DataBox::Float(0 as f32);
        let one = DataBox::Float(1 as f32);

        assert_eq!(zero, zero);
        assert_eq!(one, one);
        assert_ne!(zero, one);
        assert_ne!(one, zero);
    }

    #[test]
    fn test_float_databox_compare() {
        let zero = DataBox::Float(0 as f32);
        let one = DataBox::Float(1 as f32);

        assert!(zero == zero);
        assert!(zero < one);
        assert!(one == one);
        assert!(one > zero);
    }

    /**
     * StringDataBox tests
     */
    #[test]
    fn test_string_databox_type() {
        assert_eq!(Type::string_type(3).unwrap(), DataBox::string_databox("foo".to_string(), 3).unwrap().get_type().unwrap());
    }

    #[test]
    fn test_string_databox_get_bool() {
        assert!(DataBox::string_databox("foo".to_string(), 3).unwrap().get_bool().is_err());
    }

    #[test]
    fn test_string_databox_get_int() {
        assert!(DataBox::string_databox("foo".to_string(), 3).unwrap().get_int().is_err());
    }

    #[test]
    fn test_string_databox_get_float() {
        assert!(DataBox::string_databox("foo".to_string(), 3).unwrap().get_float().is_err());
    }

    #[test]
    fn test_string_databox_get_long() {
        assert!(DataBox::string_databox("foo".to_string(), 3).unwrap().get_long().is_err());
    }

    #[test]
    fn test_string_databox_get_string() {
        assert_eq!("f".to_string(), DataBox::string_databox("f".to_string(), 1).unwrap().get_string().unwrap());
        assert_eq!("fo".to_string(), DataBox::string_databox("fo".to_string(), 2).unwrap().get_string().unwrap());
        assert_eq!("foo".to_string(), DataBox::string_databox("foo".to_string(), 3).unwrap().get_string().unwrap());
        assert_eq!("foo".to_string(), DataBox::string_databox("foo".to_string(), 4).unwrap().get_string().unwrap());
        assert_eq!("foo".to_string(), DataBox::string_databox("foo".to_string(), 5).unwrap().get_string().unwrap());
    }

    #[test]
    fn test_string_databox_to_and_from_bytes() {
        for v in ["foo", "bar", "baz"] {
            let d1 = DataBox::string_databox(v.to_string(), 3).unwrap();
            let buf = d1.to_bytes();
            let d2 = DataBox::from_bytes(&buf, Type::string_type(3).unwrap()).unwrap();
            assert_eq!(Type::string_type(3).unwrap(), d2.get_type().unwrap());
            assert_eq!(v, d2.get_string().unwrap());
        }
    }

    #[test]
    fn test_string_databox_equals() {
        let foo = DataBox::string_databox("foo".to_string(), 3).unwrap();
        let zoo = DataBox::string_databox("zoo".to_string(), 3).unwrap();

        assert_eq!(foo, foo);
        assert_eq!(zoo, zoo);
        assert_ne!(foo, zoo);
        assert_ne!(zoo, foo);
    }

    #[test]
    fn test_string_databox_compare() {
        let foo = DataBox::string_databox("foo".to_string(), 3).unwrap();
        let zoo = DataBox::string_databox("zoo".to_string(), 3).unwrap();

        assert!(foo == foo);
        assert!(foo < zoo);
        assert!(zoo == zoo);
        assert!(zoo > foo);
    }
}
