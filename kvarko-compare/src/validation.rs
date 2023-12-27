use std::collections::HashMap;

use kvarko_model::error::AlgebraicError;
use kvarko_model::hash::IdHasher;
use kvarko_model::state::State;

use std::fmt::{Display, Formatter};
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
enum OpeningValidationError {
    LoadError(&'static str, AlgebraicError),
    Collision(&'static str, &'static str)
}

impl Display for OpeningValidationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            OpeningValidationError::LoadError(opening, error) =>
                write!(f, "Error loading opening `{opening}`: {error}"),
            OpeningValidationError::Collision(opening_1, opening_2) =>
                write!(f, "Collision between openings `{opening_1}` and {opening_2}")
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct OpeningValidationErrors(Vec<OpeningValidationError>);

impl Display for OpeningValidationErrors {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (index, error) in self.0.iter().enumerate() {
            if index > 0 {
                writeln!(f)?;
            }

            write!(f, "{error}")?;
        }

        Ok(())
    }
}

pub(crate) fn validate_openings(openings: &[&'static str]) -> Result<(), OpeningValidationErrors> {
    let mut states_hashes_to_openings = HashMap::new();
    let mut errors = Vec::new();

    for opening in openings {
        match State::<IdHasher>::from_algebraic_history(opening.split(' ')) {
            Ok(state) => {
                let position_hash = state.position_hash();

                if let Some(&old_opening) = states_hashes_to_openings.get(&position_hash) {
                    errors.push(OpeningValidationError::Collision(old_opening, opening));
                }
                else {
                    states_hashes_to_openings.insert(position_hash, opening);
                }
            },
            Err(error) => errors.push(OpeningValidationError::LoadError(opening, error))
        }
    }

    if errors.is_empty() {
        Ok(())
    }
    else {
        Err(OpeningValidationErrors(errors))
    }
}

#[cfg(test)]
mod tests {

    use crate::validation::{OpeningValidationError, OpeningValidationErrors, validate_openings};

    use kernal::prelude::*;

    use rstest::rstest;

    use kvarko_model::error::AlgebraicError;

    #[rstest]
    #[case::empty_openings(&[])]
    #[case::single_opening(&["e4 e5"])]
    #[case::multiple_non_colliding_openings(&["e4 e5", "e4 c5"])]
    fn no_error(#[case] openings: &[&'static str]) {
        let result = validate_openings(openings);

        assert_that!(result).is_ok();
    }

    #[rstest]
    #[case::single_load_error(&["e4 d4"], &[
        OpeningValidationError::LoadError("e4 d4", AlgebraicError::NoSuchMove)
    ])]
    #[case::multiple_load_errors(&["e4 Nc6?", "N4"], &[
        OpeningValidationError::LoadError("e4 Nc6?", AlgebraicError::InvalidSuffix('?')),
        OpeningValidationError::LoadError("N4", AlgebraicError::IncompleteDestination)
    ])]
    #[case::collision_of_same_opening(&["e4", "e4"], &[
        OpeningValidationError::Collision("e4", "e4")
    ])]
    #[case::collision_of_transposition(&["Nc3 e5 Nf3", "Nf3 e5 Nc3"], &[
        OpeningValidationError::Collision("Nc3 e5 Nf3", "Nf3 e5 Nc3")
    ])]
    #[case::multiple_collisions(&["e4 e5 Nf3 Nc6 Bc4", "e4 e5 Bc4 Nc6 Nf3", "Nf3 Nc6 e4 e5 Bc4"], &[
        OpeningValidationError::Collision("e4 e5 Nf3 Nc6 Bc4", "e4 e5 Bc4 Nc6 Nf3"),
        OpeningValidationError::Collision("e4 e5 Nf3 Nc6 Bc4", "Nf3 Nc6 e4 e5 Bc4")
    ])]
    #[case::mixed_errors(&["d4 d5 c4 Nf6 Nf3", "d4 d5 c4 Nf3", "c4 Nf6 d4 d5 Nf3"], &[
        OpeningValidationError::LoadError("d4 d5 c4 Nf3", AlgebraicError::NoSuchMove),
        OpeningValidationError::Collision("d4 d5 c4 Nf6 Nf3", "c4 Nf6 d4 d5 Nf3")
    ])]
    fn error(#[case] openings: &[&'static str],
            #[case] expected_errors: &[OpeningValidationError]) {
        let result = validate_openings(openings);

        assert_that!(result).contains_error(OpeningValidationErrors(expected_errors.to_vec()));
    }
}
