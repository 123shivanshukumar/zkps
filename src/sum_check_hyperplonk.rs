// to check the f*g*eq using sum_check protocol
// trying to code end to end from scratch
use ark_ff:: {Field}; // for generating field elements 
use rand::random;

pub struct multivariate_polnomial<F>
where F: Field + From<i32>
{
    vars : usize,
    poly : Vec<F>
}
pub struct univariate_polynomial<F>
where F: Field + From<i32>
{
    poly: Vec<F>,
}
impl <F> univariate_polynomial<F>
where F: Field + From<i32>{
    fn from_coefficients_vec(coeffs: &Vec<F>) -> Self {
        Self{
            poly: coeffs,
        }
    }
    fn evaluate(r: &F)->F{
        // use Horner rule
        let mut sum = F::zero();
        for i in (0..poly.len()).rev(){
            sum = sum*r + poly[i];
        }
        sum;
    }
}
impl <F> multivariate_polnomial<F>
where F: Field + From<i32>
{
    pub fn num_vars(&self)->usize{
        vars
    }
    pub fn evaluate(&self, v : &Vec<F>)->F{
        let mut sum = F::zero();
        for i in 0..(1<<self.num_vars()){
            // go thru all the bits and see what to accumulate 
            let mut factor = self.poly[i];
            let mut var_number = 0;
            let mut j = i;

            while j > 0 {
                if j % 2 != 0{ // include this variable
                    factor *= v[var_number];
                }
                j = j >> 1;
            }
            sum += factor;
        }
    }
}
pub struct Prover<F,P>
{
    f: P,
    g: P, // to search for the coefficient of x_i1 .. x_ik set those bits and query the vector
    rand: Vec<F>,
    ans: F,
    accum:F // accumulate round by round value of x_i*r_i + (1-x_i)*(1-r_i)
}
//P is SparsePolynomial<F, SparseTerm> --traits vs structs and how to use them
// this is so inconvinient  


impl <F> Prover<F>
where 
F: Field + From<i32>,

{
    pub fn new(f:vec<F>, g:vec<F>)->Self{
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
            sum = f.evaluate(&self.rand);
        }
        self.ans = sum;
    }
    fn construct_univariate(
        &mut self,
        r: &[F], // random challenge till round i 
        round: usize,
    )-> univariate_polnomial<F>// construct dense univ polynomial for this
    {
        
        let mut coefficients_prod = vec![F::zero(); 4]; // one extra to take eq
        let v = self.f.num_vars();

    // number of inputs to generate, we substract round because it's the nb of already known
    // inputs at the round; at round 1 we will have r_i.len() = 1

    for i in 0..2i32.pow((v - round - 1) as u32) {

        let mut coefficients_f = vec![F::zero(); 2];
        let mut coefficients_g = vec![F::zero(); 2]; // known that multilinear

        let mut eq_rem_const = F::one();
        let mut inputs: Vec<F> = vec![];
        // adding inputs from previous rounds
        inputs.extend(r);
        // adding round variable
        inputs.push(F::one());
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

       
        // wherever the variable is present those become the x coefficient, wherver they become constant
        for i in 0..v{
            if & (1<<round) == 0{
                coefficients_f[0] += self.f.poly[i];
            }
            else{
                coefficients_f[1] += self.f.poly[i];
            }
        }
        // same for g
        for i in 0..v{
            if & (1<<round) == 0{
                coefficients_g[0] += self.g.poly[i];
            }
            else{
                coefficients_g[1] += self.g.poly[i];
            }
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


    univariate_polnomial<F>::from_coefficients_vec(coefficients_prod)
    }
    
    pub fn commit_pair(&self)->(multivariate_polnomial<F>, multivariate_polnomial<F>){
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
    
    pub fn check_claim(&self, h:&univariate_polnomial<F>, c_i:F)->bool{
        let eval_zero = h.evaluate(&F::zero());
        let eval_one = h.evaluate(&F::one());
        
        if eval_one + eval_zero != c_i{
            return false
        }
        true
    }
    pub fn check_final_claim(&self, commit_f: multivariate_polnomial<F>, commit_g: multivariate_polnomial<F>,c: F, intial_rand:Vec<F>, r:Vec<F>)->bool
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

pub fn sum_check<F>(p: &mut Prover<F, multivariate_polnomial<F>>, v: &Verifier<F>)->bool
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
            panic!("claim fails at {round}");
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
    
