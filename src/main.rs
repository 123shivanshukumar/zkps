#![allow(unused_variables)]
use ark_poly::{univariate::DensePolynomial, multivariate::{SparsePolynomial, SparseTerm, Term}, DenseMVPolynomial, DenseUVPolynomial, Polynomial}; // polynomial libraries 
//use ark_std::cfg_into_iter; // for iterating into the polynomial coeff-term wise 
use ark_ff:: {Field,Zero}; // for generating field elements 
use rand::random;
use ark_test_curves::fp128::Fq;
pub struct Prover<F, P>
    {
         g: P, // define a multivariate Polynomial Prover has 
         f: P, // second polynomial
         c: F, // constant elt  
         prod: P,         
    }

impl<F> Prover<F, SparsePolynomial<F, SparseTerm>>
    where
        F: Field + From<i32>,
    {
        // constructor
        pub fn new(f: &SparsePolynomial<F, SparseTerm>, g: &SparsePolynomial<F, SparseTerm>)-> Self{
            let mut inst = Self{
                g : g.clone(),
                f : f.clone(),
                c : F::zero(),
                prod : SparsePolynomial::zero(), // intialise prod to zero
            };

            inst.prod = inst.prod_evaluation();
            inst.c = inst.sum_evaluation(&inst.prod); // set the sum 
            inst
        }
        
        pub fn commit_pair(&self)->(SparsePolynomial<F, SparseTerm>, SparsePolynomial<F, SparseTerm>){
            (self.f.clone(), self.g.clone()) // to make sure reference isnt passed 
        }
        fn prod_evaluation(&self) -> SparsePolynomial<F, SparseTerm>{// evaluate f*g, store in h
            let result: SparsePolynomial<F, SparseTerm> = SparsePolynomial::zero();

            if (self.f).is_zero() || (self.g).is_zero() {
                result
            } else {
                let mut result_terms = Vec::new();
                for (coeff1, term1) in (self.f).terms().iter() {
                    for (coeff2, term2) in (self.g).terms().iter() {
                        // Multiply coefficients
                        
                        let new_coeff = *coeff1 * *coeff2;
                        
                        let mut term1_vec = Vec::new();
                        let mut term2_vec = Vec::new();

                        for (var_idx  , exp) in term1.iter(){
                            term1_vec.push((*var_idx,*exp));
                        }
                        for (var_idx, exp) in term2.iter(){
                            term2_vec.push((*var_idx,*exp));
                        }

                        term1_vec.extend(term2_vec);
                        result_terms.push((new_coeff, SparseTerm::new(term1_vec)));

                    }
                }

    
                SparsePolynomial::from_coefficients_slice(self.f.num_vars(), &result_terms)
            }
        }
        

        fn sum_evaluation(&self,g: &SparsePolynomial<F, SparseTerm>) -> F{ // evaluate \Sum over {0,1}^v for h
            // h is given rest follows from previous implementations

            //let prod = self.prod_evaluation();

            let v = g.num_vars();
            let mut sum = F::zero(); // intialise sum to Field 0

            for i in 0..(1<<v){
                // convert i to boolean vector in the Field
                let mut point: Vec<F> = vec![F::zero(); v]; // intialise point to a vector of 0s

                for j in 0..v{
                    if (1<<j)&i != 0 {
                        point[j] = F::from(1);
                    }
                    else{
                        point[j] = F::from(0);
                    }
                    
                }
                sum = sum.add(&g.evaluate(&point)); // can evaluate mvp over a vector of field elements 
            }
            sum
        }

        // constructing univariate polynomial for intermediate rounds
        pub fn construct_univariate(
            g: &SparsePolynomial<F, SparseTerm>,
            r_i: &[F], // random challenge till round i 
            round: usize,
        )-> DensePolynomial<F> // construct dense univ polynomial for this
        {
            let mut coefficients = vec![F::zero(); g.degree() + 1];
        let v = g.num_vars();

        // number of inputs to generate, we substract round because it's the nb of already known
        // inputs at the round; at round 1 we will have r_i.len() = 1
        for i in 0..2i32.pow((v - round - 1) as u32) {
            let mut inputs: Vec<F> = vec![];
            // adding inputs from previous rounds
            inputs.extend(r_i);
            // adding round variable
            inputs.push(F::zero());
            // generating inputs for the rest of the variables
            let mut counter = i;
            for _ in 0..(v - round - 1) {
                if counter % 2 == 0 {
                    inputs.push(0.into());
                } else {
                    inputs.push(1.into());
                }
                counter /= 2;
            }

            //computing polynomial coef from evaluation
            for (c, t) in g.terms.clone().into_iter() {
                let mut c_acc = F::one();
                let mut which = 0;

                for (&var, pow) in t.vars().iter().zip(t.powers()) {
                    if var == round {
                        which = pow;
                    } else {
                        c_acc *= inputs[var].pow([pow as u64]);
                    }
                }
                coefficients[which] += c * c_acc;
            }
        }

        DensePolynomial::from_coefficients_vec(coefficients)
    }
    }
    

pub struct Verifier<F>
{
    data:F,
}
impl <F> Verifier<F>
where 
    F:Field + From<i32>,
{

    pub fn new() -> Self{
        Self{ // initialise 
            data : F::zero(),
        }
    }
    pub fn send_random_challenge(&self) -> F{

        let r: u8 = random();

        F::from(r) // 
    }

    pub fn check_claim(&self, g_j: &DensePolynomial<F>, c_j: F) -> bool{
        
        let eval_zero = g_j.evaluate(&F::zero());
        let eval_one = g_j.evaluate(&F::one());

        if eval_one + eval_zero != c_j{
            return false; // reject
        }

        true
    }
    pub fn compute_product(&self, commit_f:SparsePolynomial<F, SparseTerm>, commit_g:SparsePolynomial<F, SparseTerm>, r:Vec<F>) -> F{ // commitments might not be F
        // open the commitments at point r_i -- compute product and return 
        commit_f.evaluate(&r)*commit_g.evaluate(&r)
    }
}

pub fn sum_check<F>(
    p: &Prover<F, SparsePolynomial<F, SparseTerm>>,
    v: &Verifier<F>,
)-> bool
where 
F: Field + From<i32>, 
{
    // verify the polynomial commitments 
    let nb_rounds = p.g.num_vars();
    let mut r: Vec<F> = Vec::new(); // vector of random challenges

    // product computation will be done during initialisation 
    let h_1 = Prover::construct_univariate(&p.prod, &r, 0); // check 
    // h represents the product

    if !v.check_claim(&h_1, p.c){ 
        panic!("claim fails at 0");
    }
    println!("claim passed 0");
    let mut r_i = v.send_random_challenge();
    r.push(r_i);

    let mut c_i = h_1.evaluate(&r_i);

    // for further rounds

    for round in 1.. nb_rounds-1{

        let h_i = Prover::construct_univariate(&p.prod, &r, round);
        if !v.check_claim(&h_i, c_i ){
            panic!("failed at {}", round);
        }
        // construct new random challenge for next round 
        r_i = v.send_random_challenge();
        r.push(r_i);
        c_i = h_i.evaluate(&r_i); // eval the univ poly at r_i
    }

    // value checking round 

    let h_v = Prover::construct_univariate(&p.prod, &r, nb_rounds - 1);
    if !v.check_claim(&h_v, c_i) {
        panic!("sumcheck failed at last round");
    }
    r_i = v.send_random_challenge();
    r.push(r_i);

    let (commit_f, commit_g) = p.commit_pair();
    let x = v.compute_product(commit_f, commit_g, r);// x is the value f(r)*g(r);


    // check if f(r)*g(r) as computed by the commitments is same as the value of h_v(r_i) claimed by the prover
    if x != h_v.evaluate(&r_i){
        panic!("sum check failed on evaluation");
    }
    true // accept the claim if didnt panic
}

fn main() {
    // g(x_0, x_1, x_2) = 2*x_0^3 + x_0*x_2 + x_1*x_2
    // f(x_0, x_1) = x1*x2^2
    let g = SparsePolynomial::from_coefficients_vec(
        3,
        vec![
            (Fq::from(2), SparseTerm::new(vec![(0, 3)])),
            (Fq::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
            (Fq::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
        ],
    );

    let f = SparsePolynomial::from_coefficients_vec(
        3, 
        vec![
            (Fq::from(1), SparseTerm::new(vec![(1, 1), (2, 2)])),
        ],
    );

    let p = Prover::new(&f,&g);
    let v = Verifier::new();

    println!("sumcheck start");
    let valid = sum_check(&p, &v);
    if !valid {
        panic!("protocol failed");
    }
    else{
        println!("sum check successful!");
    }
}

