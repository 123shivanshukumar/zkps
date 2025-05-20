// to check the f*g*eq using sum_check protocol
// trying to code end to end from scratch
use ark_poly::{univariate::DensePolynomial, multivariate::{SparsePolynomial, SparseTerm, Term}, DenseMVPolynomial, DenseUVPolynomial, Polynomial}; 
use ark_ff:: {Field}; // for generating field elements 
use rand::random;
use ark_test_curves::fp128::Fq; // to be used in main
pub struct Prover<F, P>
{
    f: P,
    g: P,
    rand: Vec<F>,
    ans: F,
    accum:F // accumulate round by round value of x_i*r_i + (1-x_i)*(1-r_i)
}
//P is SparsePolynomial<F, SparseTerm> --traits vs structs and how to use them
// this is so inconvinient  
impl <F> Prover<F,SparsePolynomial<F, SparseTerm> >
where 
F: Field + From<i32>,

{
    pub fn new(f:SparsePolynomial<F, SparseTerm>, g:SparsePolynomial<F, SparseTerm>)->Self{
        Self{
            f:f.clone(),
            g:g.clone(),
            ans:F::zero(),
            rand:Vec::new(),
            accum:F::one()
        }
    }
    pub fn receive_intial_rand(&mut self, r: Vec<F>){ // to set self to mut to change it 
        self.rand = r.clone();
        self.sum_evaluate(); // start sum evaluation after receiving random challenge
    }
    fn sum_evaluate(&mut self){
        // go over every element in the boolean hypercube and evaluate 
        let mu: usize = self.f.num_vars();
        
        // if the intial random vector `rand` sent by the Verifer is an element of the hypercube, then 
        // evaluate f and g over rand, multilply and this is the sum
        // else the sum is 0
        let mut sum = F::zero();
        let mut flag = false;

        for i in 0..mu{
            if self.rand[i] != F::zero() || self.rand[i] != F::one(){
                flag = true;
                break
            }
        }
        if flag{
            sum = self.f.evaluate(&self.rand);
        }
        self.ans = sum;
    }
    fn construct_univariate(
        &mut self,
        r: &[F], // random challenge till round i 
        round: usize,
    )-> DensePolynomial<F> // construct dense univ polynomial for this
    {
        
        let mut coefficients_prod = vec![F::zero(); self.f.degree() + self.g.degree() + 2]; // one extra to take eq
        let v = self.f.num_vars();

    // number of inputs to generate, we substract round because it's the nb of already known
    // inputs at the round; at round 1 we will have r_i.len() = 1
    for i in 0..2i32.pow((v - round - 1) as u32) {

        let mut coefficients_f = vec![F::zero(); self.f.degree() + 1];
        let mut coefficients_g = vec![F::zero(); self.g.degree() + 1];

        let mut eq_rem_const = F::one();
        let mut inputs: Vec<F> = vec![];
        // adding inputs from previous rounds
        inputs.extend(r);
        // adding round variable
        inputs.push(F::zero());
        // generating inputs for the rest of the variables
        let mut counter = i;
        for j in 0..(v - round - 1) {
            if counter % 2 == 0 {
                inputs.push(0.into());
                eq_rem_const *= F::one() - self.rand[j + round+1];
            } else {
                inputs.push(1.into());
                eq_rem_const *= self.rand[j + round+1];
            }
            counter /= 2;
        }
        eq_rem_const *= self.accum; // \Pi (r[t]*rand[t] + (1-r[t])*(1-rand[t])) for t = 0 to round - 1 

        let rand_i = self.rand[round];
        self.accum = self.accum*(rand_i*r[round] + (F::one() - r[round])*(F::one() - rand_i)); // include the product from this round

        
        let coefficients_eq = vec![eq_rem_const*(rand_i - F::one()),eq_rem_const*(F::from(2)*rand_i - F::one())];

        for (c, t) in self.f.terms.clone().into_iter() {
            let mut c_acc = F::one();
            let mut which = 0;

            for (&var, pow) in t.vars().iter().zip(t.powers()) {
                if var == round {
                    which = pow;
                } else {
                    c_acc *= inputs[var].pow([pow as u64]);
                }
            }
            coefficients_f[which] += c * c_acc;
        }
        //computing polynomial coef from evaluation
        for (c, t) in self.g.terms.clone().into_iter() {
            let mut c_acc = F::one();
            let mut which = 0;

            for (&var, pow) in t.vars().iter().zip(t.powers()) {
                if var == round {
                    which = pow;
                } else {
                    c_acc *= inputs[var].pow([pow as u64]);
                }
            }
            coefficients_g[which] += c * c_acc;
        }
        for _i in 0..coefficients_f.len(){
            for _j in  0..coefficients_g.len(){
                for _k in 0..coefficients_eq.len()
                {
                    coefficients_prod[_i+_j+_k] += coefficients_f[_i]*coefficients_g[_j]*coefficients_eq[_k];
                }
            }
        }

    }


    DensePolynomial::from_coefficients_vec(coefficients_prod)
    }
    
    pub fn commit_pair(&self)->(SparsePolynomial<F,SparseTerm>, SparsePolynomial<F,SparseTerm>){
        (self.f.clone(), self.g.clone())
    }

}
pub struct Verifier<F>
where 
F : Field + From<i32>
{   
    _data : F // dummy to keep Field + From<i32> alive
}
impl<F> Verifier<F>
where 
F : Field + From<i32>
{
    pub fn new()->Self{
        Self{
            _data: F::zero()
        }
    }
    pub fn send_random_challenge(&self)->F{
        let r:i32 = random();
        F::from(r)
    }
    pub fn send_random_vector_init(&self, num_vars:usize)->Vec<F>{
        let mut r = Vec::new();
        let mut r_i;
        for _i in 0..num_vars{ // unused variable _
            r_i = self.send_random_challenge();
            r.push(r_i);
        }
        r
    }
    
    pub fn check_claim(&self, h:&DensePolynomial<F>, c_i:F)->bool{
        let eval_zero = h.evaluate(&F::zero());
        let eval_one = h.evaluate(&F::one());
        
        if eval_one + eval_zero != c_i{
            return false
        }
        true
    }
    pub fn check_final_claim(&self, commit_f: SparsePolynomial<F,SparseTerm>, commit_g: SparsePolynomial<F,SparseTerm>,c: F, intial_rand:Vec<F>, r:Vec<F>)->bool
    {   
        // rand is the initial random vector for the protocol
        let mut eval = commit_f.evaluate(&r)*commit_g.evaluate(&r);
        let one = F::one();
        for i in 0..commit_f.num_vars(){
            eval = eval*(r[i]*intial_rand[i] + (one-r[i])*(one-intial_rand[i]));
        }
        return eval == c
    }
}

pub fn sum_check<F>(p: &mut Prover<F, SparsePolynomial<F,SparseTerm>>, v: &Verifier<F>)->bool
where 
F: Field + From<i32>,
{   
    let num_vars = p.f.num_vars();
    // assuming Prover and Verifier have been created in main
    let initial_rand = v.send_random_vector_init(num_vars);
    p.receive_intial_rand(initial_rand.clone()); // is sending P as mutable safe??
    
    // P evaluates sum \Sum f(x)*g(x)*eq(x,r) \forall x \in {0,1}^num_vars

    //sum check starts
  
    let mut r: Vec<F> = Vec::new(); // vector of random challenges
    
    // product computation will be done during initialisation 
    let f_1 = p.construct_univariate(&r, 0); // check 
        // h represents the product
    
    if !v.check_claim(&f_1, p.ans){ 
        panic!("claim fails at 0");
    }
        
    let mut r_i = v.send_random_challenge();
    r.push(r_i);
    
    let mut c_i = f_1.evaluate(&r_i);
    
        // for further rounds
    
    for round in 1.. num_vars-1{
    
        // constructing separately to avoid multiplication complexity
        let f_i = p.construct_univariate(&r, round);

        if !v.check_claim(&f_i, c_i){ 
            panic!("claim fails at 0");
        }
        // construct new random challenge for next round 
        r_i = v.send_random_challenge();
        r.push(r_i);
        c_i = f_i.evaluate(&r_i); // eval the univ poly at r_i
    }
    
        // value checking round 
    
    let f_v = p.construct_univariate( &r, num_vars - 1);

    r_i = v.send_random_challenge();
    r.push(r_i);
    
    let (commit_f, commit_g) = p.commit_pair();
    let c = f_v.evaluate(&r_i); // f_i(r_i)*g_i(r_i)*eq_i(r_i) 
    if !v.check_final_claim(commit_f, commit_g, c,initial_rand.clone(), r){ 
        panic!("claim fails at last round");
    }
    
    true // accept the claim if didnt panic
}
    

