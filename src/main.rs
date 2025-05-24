use sum_check_hyperplonk::sum_check;
mod sum_check_hyperplonk;
fn main() {
    //considering 3 variables 
    let f = vec![1,0,2,0,1,1,0,2];
    let g = vec![0,2,1,2,0,3,1,4];


    let mut p = sum_check_hyperplonk::Prover::new(3,f, g);
    let v = sum_check_hyperplonk::Verifier::new(0);

    if sum_check(&mut p, &v){
        println!("all checks passed");
    }else{
        panic!("failed");
    }


}

