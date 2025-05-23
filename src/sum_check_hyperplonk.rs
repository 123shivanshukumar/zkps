// to check the f*g*eq using sum_check protocol
// trying to code end to end from scratch
// for generating field elements 
use rand::random;
pub struct MultivariatePolynomial
{
    vars : usize,
    poly : Vec<i32>
}

pub struct UnivariatePolynomial
{
    poly: Vec<i32>,
}
impl UnivariatePolynomial
{
    pub fn new(poly:Vec<i32>)->Self{
        Self{
            poly:poly.clone(),
        }
    }
    pub fn from_coefficients_vec(coeffs: &Vec<i32>) -> Self {
        Self{
            poly: coeffs.clone(),
        }
    }
    pub fn evaluate(&self,r: &i32)->i32{
        // use Horner rule
        let mut sum = 0;
        for i in (0..self.poly.len()).rev(){
            sum = sum*(r) + self.poly[i];
        }
        sum.into()
    }
}
impl  MultivariatePolynomial
{
    pub fn new(n:usize, poly:Vec<i32>)->Self{
        Self{
            vars:n,
            poly:poly.clone(),
        }
    }
    pub fn num_vars(&self)->usize{
        self.vars
    }
    pub fn evaluate(&self, v : &Vec<i32>)->i32{
        let mut sum = 0;
        for i in 0..1<<self.num_vars(){
            // go thru all the bits and see what to accumulate 
            let mut factor = self.poly[i];
            let mut var_number = 0;
            let mut j = i;

            while j > 0 {
                if j % 2 != 0{ // include this variable
                    factor = factor*v[var_number];
                }
                j = j >> 1;
                var_number += 1;
            }
            sum = sum + factor;
        }
        sum
    }
}
pub struct Prover
{
    f: MultivariatePolynomial,
    g: MultivariatePolynomial, // to search for the coefficient of x_i1 .. x_ik set those bits and query the vector
    rand: Vec<i32>,
    ans: i32,
    accum:i32 // accumulate round by round value of x_i*r_i + (1-x_i)*(1-r_i)
}
//P is SparsePolynomial<i32, SparseTerm> --traits vs structs and how to use them
// this is so inconvinient  


impl Prover
where 
{
    pub fn new(n:usize, f:Vec<i32>, g:Vec<i32>)->Self{
        Self{
            f:MultivariatePolynomial { vars: n, poly: f.clone() },
            g:MultivariatePolynomial { vars: n, poly: g.clone() },
            ans:0.into(),
            rand:Vec::new(),
            accum:1.into()
        }
    }
    pub fn receive_intial_rand(&mut self, r: Vec<i32>){ // to set self to mut to change it 
        self.rand = r.clone();
        self.sum_evaluate(); // start sum evaluation after receiving random challenge
        
    }
    fn sum_evaluate(&mut self){
        // go over every element in the boolean hypercube and evaluate 
        let mu: usize = self.f.num_vars();
        
        // if the intial random vector `rand` sent by the Verifer is an element of the hypercube, then 
        // evaluate f and g over rand, multilply and this is the sum
        // else the sum is 0
        let mut sum = 0;
        for i in 0..(1<<mu){
            let mut inputs = vec![0;mu];
            let mut j = i;
            let mut counter = 0;
            let mut eq_rem_const = 1;
            while counter < mu{
                if j % 2 == 0 {
                    inputs[mu - counter - 1] = 0;
                    eq_rem_const *= 1 - self.rand[mu - counter - 1];
                } else {
                    inputs[mu - counter - 1] = 1;
                    eq_rem_const *= self.rand[mu - counter - 1];
                }
                counter += 1;
                j = j >> 1;
            }

            sum += self.f.evaluate(&inputs)*self.g.evaluate(&inputs)*eq_rem_const;
        }
        
        self.ans = sum;
    }
    fn construct_univariate(
        &mut self,
        r: &[i32], // random challenge till round i 
        round: usize,
    )-> UnivariatePolynomial// construct dense univ polynomial for this
    {
        
        let mut coefficients_prod = vec![0; 4]; // one extra to take eq
        let v = self.f.num_vars();

    // number of inputs to generate, we substract round because it's the nb of already known
    // inputs at the round; at round 1 we will have r_i.len() = 1

    for i in 0..1<<(v- round - 1) {

        let mut coefficients_f = vec![0; 2];
        let mut coefficients_g = vec![0; 2]; // known that multilinear

        let mut eq_rem_const = 1;
        let mut inputs: Vec<i32> = vec![];
        // adding inputs from previous rounds
        let rand_i = self.rand[round];
        if round > 0{ inputs.extend(r);}
            // adding round variable
            inputs.push(0);
            inputs.extend(vec![0;v-round-1]);
        // generating inputs for the rest of the variables
        let mut counter = i;
        for j in 0..(v - round - 1) {
            if counter % 2 == 0 {
                inputs[v - j - 1] = 0;
                eq_rem_const *= 1 - self.rand[v - j - 1];
            } else {
                inputs[v - j - 1] = 1;
                eq_rem_const *= self.rand[v - j - 1];
            }
            counter /= 2;
         // \Pi (r[t]*rand[t] + (1-r[t])*(1-rand[t])) for t = 0 to round - 1 

        }
        
       // println!("{eq_rem_const}"); // shud be 0
        if round > 0{self.accum = self.accum*(self.rand[round-1]*r[round - 1] + (1 - r[round - 1])*(1 - self.rand[round-1]));} // include the product from this round
        eq_rem_const *= self.accum; // multiply the self.accum from previous round
        let coefficients_eq = vec![eq_rem_const*(1-rand_i), eq_rem_const*(2*rand_i - 1)];
       
        // wherever the variable is present those become the x coefficient, wherver they become constant
        
        coefficients_f[0] = self.f.evaluate(&inputs);
        coefficients_g[0] = self.g.evaluate(&inputs);
        inputs[round] = 1;
        coefficients_f[1] = self.f.evaluate(&inputs) - coefficients_f[0];
        coefficients_g[1] = self.g.evaluate(&inputs) - coefficients_g[0];
      
        
        for _i in 0..2{
            for _j in  0..2{
                for _k in 0..2
                {
                    coefficients_prod[_i+_j+_k] += coefficients_f[_i]*coefficients_g[_j]*coefficients_eq[_k];
                }
            }
        }
    
    }


    UnivariatePolynomial::from_coefficients_vec(&coefficients_prod)
    }
    
    pub fn commit_pair(&self, mut commit_f: Vec<i32>, mut commit_g : Vec<i32> ){
        commit_f = self.f.poly.clone();
        commit_g = self.g.poly.clone();
    }

}
pub struct Verifier
where 
{   
    _data : i32 // dummy to keep i32ield + i32rom<i32> alive
}
impl Verifier
{
    pub fn new(data:i32)->Self{
        Self{
            _data: data
        }
    }
    pub fn send_random_challenge(&self)->i32{
        let r:i32 = random();
        r%10
    }
    pub fn send_random_vector_init(&self, num_vars:usize)->Vec<i32>{
        let mut r = Vec::new();
        let mut r_i;
        for _i in 0..num_vars{ // unused variable _
            r_i = self.send_random_challenge();
            r.push(r_i);
        }
        r
    }
    
    pub fn check_claim(&self, h:&UnivariatePolynomial, c_i:i32)->bool{
        let eval_zero = h.evaluate(&0);
        let eval_one = h.evaluate(&1);
        
        if eval_one + eval_zero != c_i{
            return false
        }
        true
    }
    pub fn check_final_claim(&self, commit_f: MultivariatePolynomial, commit_g: MultivariatePolynomial,c: i32, intial_rand:Vec<i32>, r:Vec<i32>)->bool
    {   
        // rand is the initial random vector for the protocol
        let mut eval = commit_f.evaluate(&r)*commit_g.evaluate(&r);
        let one = 1;
        for i in 0..commit_f.num_vars(){
            eval = eval*(r[i]*intial_rand[i] + (one-r[i])*(one-intial_rand[i]));
        }
        return eval == c
    }
}

pub fn sum_check(p: & mut Prover, v: &Verifier)->bool
{   
    let num_vars = p.f.num_vars();
    // assuming Prover and Verifier have been created in main
    let initial_rand = v.send_random_vector_init(num_vars);
    p.receive_intial_rand(initial_rand.clone()); // is sending P as mutable safe??
    
    // P evaluates sum \Sum f(x)*g(x)*eq(x,r) \forall x \in {0,1}^num_vars

    //sum check starts
  
    let mut r: Vec<i32> = Vec::new(); // vector of random challenges
    
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
    
    let ( commit_f,  commit_g) = (p.f.poly.clone(), p.g.poly.clone());
    let commit_f_poly = MultivariatePolynomial{vars:p.f.num_vars(), poly:commit_f };
    let commit_g_poly = MultivariatePolynomial{vars:p.g.num_vars(), poly:commit_g };
    
    let c = f_v.evaluate(&r_i); // f_i(r_i)*g_i(r_i)*eq_i(r_i) 
    if !v.check_final_claim(commit_f_poly, commit_g_poly, c,initial_rand.clone(), r){ 
        panic!("claim fails at last round");
    }
    
    true // accept the claim if didnt panic
}
    
