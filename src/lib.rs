#![feature(iterator_try_collect)]
#![feature(assert_matches)]
#![feature(get_mut_unchecked)]
#![feature(test)]

#[macro_use]
extern crate pest_derive;
extern crate test;

pub mod ast;
pub mod env;
pub mod error;
pub mod eval;
pub mod parser;
pub mod types;

#[cfg(test)]
mod tests {
    use super::*;
    use error::Error;
    use std::assert_matches::assert_matches;
    use std::{fs, path::PathBuf};
    use test::Bencher;

    static NO_EXEC: [&'static str; 4] = ["merge.tig", "test6.tig", "test7.tig", "test18.tig"];

    fn test_src(file_name: &str, src: &str) -> Result<(), Error> {
        let ast = parser::parse(src)?;
        types::check(&ast)?;
        if !NO_EXEC.contains(&file_name) {
            eval::eval(&ast)?;
        }
        Ok(())
    }

    fn test_sample(file_name: &str) -> Result<(), Error> {
        let src = fs::read_to_string(["samples", file_name].iter().collect::<PathBuf>()).unwrap();
        test_src(file_name, &src)
    }

    #[rustfmt::skip]
    #[test]
    fn test_samples() {
        assert_matches!(test_sample("merge.tig"), Ok(_));
        assert_matches!(test_sample("queens.tig"), Ok(_));
        assert_matches!(test_sample("test1.tig"), Ok(_));
        assert_matches!(test_sample("test2.tig"), Ok(_));
        assert_matches!(test_sample("test3.tig"), Ok(_));
        assert_matches!(test_sample("test4.tig"), Ok(_));
        assert_matches!(test_sample("test5.tig"), Ok(_));
        assert_matches!(test_sample("test6.tig"), Ok(_));
        assert_matches!(test_sample("test7.tig"), Ok(_));
        assert_matches!(test_sample("test8.tig"), Ok(_));
        assert_matches!(test_sample("test9.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test10.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test11.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test12.tig"), Ok(_));
        assert_matches!(test_sample("test13.tig"), Err(Error::UnsupportedOperandType { .. }));
        assert_matches!(test_sample("test14.tig"), Err(Error::UnsupportedOperandType { .. }));
        assert_matches!(test_sample("test15.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test16.tig"), Err(Error::RecursiveType(_)));
        assert_matches!(test_sample("test17.tig"), Ok(_));
        assert_matches!(test_sample("test18.tig"), Ok(_));
        assert_matches!(test_sample("test19.tig"), Err(Error::NotDefined(_)));
        assert_matches!(test_sample("test20.tig"), Err(Error::NotDefined(_)));
        assert_matches!(test_sample("test21.tig"), Err(Error::UnsupportedOperandType { .. }));
        assert_matches!(test_sample("test22.tig"), Err(Error::NoSuchField(_)));
        assert_matches!(test_sample("test23.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test24.tig"), Err(Error::NotArray(_)));
        assert_matches!(test_sample("test25.tig"), Err(Error::NotRecord(_)));
        assert_matches!(test_sample("test26.tig"), Err(Error::UnsupportedOperandType { .. }));
        assert_matches!(test_sample("test27.tig"), Ok(_));
        assert_matches!(test_sample("test28.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test29.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test30.tig"), Ok(_));
        assert_matches!(test_sample("test31.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test32.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test33.tig"), Err(Error::NotDefined(_)));
        assert_matches!(test_sample("test34.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test35.tig"), Err(Error::MismatchedArgumentNum { .. }));
        assert_matches!(test_sample("test36.tig"), Err(Error::MismatchedArgumentNum { .. }));
        assert_matches!(test_sample("test37.tig"), Ok(_));
        assert_matches!(test_sample("test38.tig"), Ok(_));
        assert_matches!(test_sample("test39.tig"), Ok(_));
        assert_matches!(test_sample("test40.tig"), Err(Error::MismatchedTypes { .. }));
        assert_matches!(test_sample("test41.tig"), Ok(_));
        assert_matches!(test_sample("test42.tig"), Ok(_));
        assert_matches!(test_sample("test43.tig"), Err(Error::UnknownType(_)));
        assert_matches!(test_sample("test44.tig"), Ok(_));
        assert_matches!(test_sample("test45.tig"), Err(Error::UnknownType(_)));
        assert_matches!(test_sample("test46.tig"), Ok(_));
        assert_matches!(test_sample("test47.tig"), Ok(_));
        assert_matches!(test_sample("test48.tig"), Ok(_));
        assert_matches!(test_sample("test49.tig"), Err(Error::ParseError(_)));
    }

    #[bench]
    fn bench_samples(b: &mut Bencher) -> anyhow::Result<()> {
        let samples: Vec<_> = fs::read_dir("samples")?.into_iter().try_collect()?;
        let samples: Vec<_> = samples
            .iter()
            .map(|sample| sample.file_name().into_string().unwrap())
            .zip(
                samples
                    .iter()
                    .map(|sample| fs::read_to_string(sample.path()))
                    .try_collect::<Vec<_>>()?,
            )
            .collect();
        b.iter(|| {
            for (file_name, src) in &samples {
                _ = test_src(file_name, src);
            }
        });
        Ok(())
    }
}
