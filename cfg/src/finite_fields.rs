use std::hash::Hash;
use std::str::FromStr;
use num_bigint_dig::BigInt;

pub trait FiniteFieldDef: Clone + Eq + PartialEq + Hash {
    fn prime() -> BigInt;
}


#[derive(Hash, Clone, Eq, PartialEq)]
pub struct BN128Prime {}
impl FiniteFieldDef for BN128Prime {
    fn prime() -> BigInt {
        BigInt::from_str("21888242871839275222246405745257275088548364400416034343698204186575808495617").unwrap()
    }
}

#[derive(Hash, Clone, Eq, PartialEq)]
pub struct BLS12381Prime {}
impl FiniteFieldDef for BLS12381Prime {
    fn prime() -> BigInt {
        BigInt::from_str("52435875175126190479447740508185965837690552500527637822603658699938581184513").unwrap()
    }
}

#[derive(Hash, Clone, Eq, PartialEq)]
pub struct GoldilocksPrime {}
impl FiniteFieldDef for GoldilocksPrime {
    fn prime() -> BigInt {
        BigInt::from_str("18446744069414584321").unwrap()
    }
}

#[derive(Hash, Clone, Eq, PartialEq)]
pub struct GrumpkinPrime {}
impl FiniteFieldDef for GrumpkinPrime {
    fn prime() -> BigInt {
        BigInt::from_str("21888242871839275222246405745257275088696311157297823662689037894645226208583").unwrap()
    }
}

#[derive(Hash, Clone, Eq, PartialEq)]
pub struct PallasPrime {}
impl FiniteFieldDef for PallasPrime {
    fn prime() -> BigInt {
        BigInt::from_str("28948022309329048855892746252171976963363056481941560715954676764349967630337").unwrap()
    }
}

#[derive(Hash, Clone, Eq, PartialEq)]
pub struct VestaPrime {}
impl FiniteFieldDef for VestaPrime {
    fn prime() -> BigInt {
        BigInt::from_str("28948022309329048855892746252171976963363056481941647379679742748393362948097").unwrap()
    }
}

#[derive(Hash, Clone, Eq, PartialEq)]
pub struct SECQ256R1Prime {}
impl FiniteFieldDef for SECQ256R1Prime {
    fn prime() -> BigInt {
        BigInt::from_str("115792089210356248762697446949407573530086143415290314195533631308867097853951").unwrap()
    }
}
#[derive(Hash, Clone, Eq, PartialEq)]
pub struct SmallPrime {}
impl FiniteFieldDef for SmallPrime {
    fn prime() -> BigInt {
        BigInt::from_str("1009").unwrap()
    }
}