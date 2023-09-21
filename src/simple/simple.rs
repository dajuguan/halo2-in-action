use std::marker::PhantomData;

/// Prove know  prove knowledge of two private inputs a and b
/// s.t: a^2 * b^2 = c

use halo2_proofs::{
    arithmetic::Field,
    plonk::{Advice, Column, Instance, Selector, ConstraintSystem, Fixed, Error, Circuit}, 
    circuit::{Chip, AssignedCell, Layouter, Value,SimpleFloorPlanner}, 
    poly::Rotation
};

/// Circuit design:
/// | ins   | a0    | a1    | s_mul |
/// |-------|-------|-------|-------|
/// |       |    a  |       |       |
/// |       |    b  |       |       |
/// |       | const |       |       |
/// |       |   ab  |   b   |   1   |
/// |       |   ab  |       |   0   |
/// |       |   ab  |   ab  |   1   |
/// |       | absq  |       |   0   |
/// |       |  absq | absq  |   1   |
/// |       |  c    |       |   0   |


#[derive(Debug, Clone)]
struct FieldConfig {
    advice: [Column<Advice>;2],
    instance: Column<Instance>,
    s_mul: Selector,
}

#[derive(Debug, Clone)]
struct FieldChip<F:Field> {
    config: FieldConfig,
    _marker: PhantomData<F>
}


impl <F:Field> FieldChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
       FieldChip { config, _marker: PhantomData } 
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>;2],
        instance: Column<Instance>,
        constant: Column<Fixed>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        meta.enable_constant(constant);
        for c in &advice {
            meta.enable_equality(*c);
        }
        let s_mul = meta.selector();
        /* Gate design:
            | a0 | a1 | s_mul|
            |----|----|------|
            |lhs |rhs |s_mul |
            |out |    |      |  
        */
        meta.create_gate("mul_gate", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);
            vec![s_mul * (lhs*rhs - out)]
        });

        FieldConfig {
            advice,
            instance,
            s_mul
        }

    }

}

impl <F:Field> Chip<F> for FieldChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[derive(Clone)]
struct Number<F:Field>(AssignedCell<F,F>);



impl <F:Field>  FieldChip<F> {
    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>
    ) -> Result<Number<F>, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load private", 
        |mut region| {
            region.assign_advice(
                || "private input", 
                config.advice[0], 
                0, 
                || value
            ).map(Number)
        })
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F
    ) -> Result<Number<F>, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load constant", 
        |mut region| {
            region.assign_advice_from_constant(
                || "private input", 
                config.advice[0], 
                0, 
                constant
            ).map(Number)
        })
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Number<F>,
        b: Number<F>,
    ) -> Result<Number<F>, Error> {
        let config = self.config();

        layouter.assign_region(
            || "mul", 
        |mut region| {
            config.s_mul.enable(&mut region, 0)?;
            a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
            b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

            let value = a.0.value().copied() * b.0.value().copied();
            region.assign_advice(|| "out=lhs*rhs", config.advice[0], 1, || value)
            .map(Number)
        })
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Number<F>,
        row: usize
    )  -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }

}

#[derive(Default)]
struct MyCircuit<F:Field> {
    constant: F,
    a: Value<F>,
    b: Value<F>
}

impl <F:Field> Circuit<F> for MyCircuit<F> {
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(),meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();
        FieldChip::configure(meta, advice, instance, constant)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let field_chip = FieldChip::<F>::construct(config);
        let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?;
        let b = field_chip.load_private(layouter.namespace(|| "load b"), self.b)?;
        let constant = field_chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        let ab = field_chip.mul(layouter.namespace(|| "a*b"), a, b)?;
        let absq = field_chip.mul(layouter.namespace(|| "ab*ab"), ab.clone(), ab)?;
        let c = field_chip.mul(layouter.namespace(|| "absq*constant"), absq, constant)?;

        //expose public
        field_chip.expose_public(layouter.namespace(|| "expose c"), c, 0)

    }
}



#[cfg(test)]
mod tests {
    use halo2_proofs::{dev::MockProver, pasta::Fp};
    use super::*;

    #[cfg(feature = "dev-graph")]
    #[test]
    fn test_simple() {
        // ANCHOR: test-circuit
        // The number of rows in our circuit cannot exceed 2^k. Since our example
        // circuit is very small, we can pick a very small value here.
        let k = 5;
    
        // Prepare the private and public inputs to the circuit!
        let constant = Fp::from(2);
        let a = Fp::from(2);
        let b = Fp::from(3);
        let c = constant * a.square() * b.square();
        println!("c=:{:?}",c);
    
        // Instantiate the circuit with the private inputs.
        let circuit = MyCircuit {
            constant,
            a: Value::known(a),
            b: Value::known(b),
        };

        // Create the area you want to draw on.
        // Use SVGBackend if you want to render to .svg instead.
        use plotters::prelude::*;
        let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Example Circuit Layout", ("sans-serif", 60))
            .unwrap();

        halo2_proofs::dev::CircuitLayout::default()
            // You can optionally render only a section of the circuit.
            // .view_width(0..2)
            // .view_height(0..16)
            // You can hide labels, which can be useful with smaller areas.
            .show_labels(true)
            // Render the circuit onto your area!
            // The first argument is the size parameter for the circuit.
            .render(5, &circuit, &root)
            .unwrap();
    
        // Arrange the public input. We expose the multiplication result in row 0
        // of the instance column, so we position it there in our public inputs.
        let mut public_inputs = vec![c];
    
        // Given the correct public input, our circuit will verify.
        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    
        // If we try some other public input, the proof will fail!
        public_inputs[0] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err());
        // ANCHOR_END: test-circuit
    }
}