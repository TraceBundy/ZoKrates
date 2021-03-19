use proof_system::Scheme;
use zokrates_field::{Bn128Field, Field};

pub trait PlatonCppCompatibleField: Field {}
impl PlatonCppCompatibleField for Bn128Field {}

pub trait PlatonCppCompatibleScheme<T: PlatonCppCompatibleField>: Scheme<T> {
    fn export_platon_cpp_verifier(vk: Self::VerificationKey) -> String;
}
