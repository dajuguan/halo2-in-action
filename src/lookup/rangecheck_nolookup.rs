use std::marker::PhantomData;

// Problem to prove:  a in [0, RANGE]
use halo2_proofs:: {
    plonk::*, arithmetic::Field, poly::{Rotation}, pasta::group::ff::PrimeField, 
    circuit::{Layouter, Value, AssignedCell, SimpleFloorPlanner},
};

/// Circuit design:
/// | adv   | q_range| 
/// |-------|--------|
/// |   a   |    1   |  

struct ACell<F:PrimeField> (AssignedCell<Assigned<F>,F>);
#[derive(Debug, Clone)]
struct RangeConfig<F:PrimeField, const RANGE: usize>{
    value: Column<Advice>,
    q_range: Selector,
    _maker: PhantomData<F>
}

impl <F:PrimeField, const RANGE: usize> RangeConfig<F, RANGE>{
    fn configure(meta: &mut ConstraintSystem<F>,value: Column<Advice>) -> Self {
        let q_range = meta.selector();
        meta.create_gate("range check", |meta|{
            let q_range = meta.query_selector(q_range);
            let v = meta.query_advice(value, Rotation::cur());
            let res = |range: usize, v: Expression<F>| {
                assert!(range > 0);
                (1..range).fold(v.clone(), |acc, i| {
                    acc * (Expression::Constant(F::from(i as u64)) - v.clone())
                })
            };
            Constraints::with_selector(q_range, [res(RANGE,v)])
        });
        RangeConfig {value, q_range, _maker: PhantomData}
    }
    
    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>
    ) -> Result<ACell<F>,Error> {
        layouter.assign_region(|| "value to check", |mut region|{ //instantiate a new region, so it's not ref
            self.q_range.enable(&mut region, 0)?;
            region.assign_advice(||"value", self.value, 0, || value)
            .map(ACell)
        })
    }
}


#[derive(Debug, Default)]
struct MyCircuit<F:PrimeField, const RANGE: usize>{
    value: Value<Assigned<F>>
}

impl <F:PrimeField, const RANGE: usize> Circuit<F> for MyCircuit<F, RANGE> {
    type Config = RangeConfig<F,RANGE>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        MyCircuit::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = meta.advice_column();
        RangeConfig::configure(meta, advice)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        config.assign(layouter.namespace(|| "range check"), self.value)?;
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use halo2_proofs::{pasta::Fp, dev::MockProver};

    use super::*;
    
    #[test]
    fn test_rangecheck() {
        let value = Fp::from(6);
        let circuit = MyCircuit::<Fp,16>{value: Value::known(value).into()};
        let k = 5;

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let value = Fp::from(17);
        let circuit = MyCircuit::<Fp,16>{value: Value::known(value).into()};
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
}