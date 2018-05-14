mod util;
use util::Binop;
use util::Relop;

mod generate_x86_64;
use generate_x86_64::generate_x86_64;

mod flatten_program;
use flatten_program::flatten_program;

mod expose_basic_blocks;
use expose_basic_blocks::expose_basic_blocks;


fn main() {

   // TODO: write a pass to optimize jumps

   let output1 : String = generate_x86_64(generate_x86_64::test1()); 

   println!("{}",output1); 
   
   let output2 : generate_x86_64::Program = flatten_program(flatten_program::test1()); 
   
   println!("{:?}",output2); 
   
   let output3 : String = generate_x86_64(flatten_program(flatten_program::test1())); 
   
   println!("{}",output3); 
   
   let output4 = expose_basic_blocks(expose_basic_blocks::test1()); 
   
   println!("{:?}",output4); 

   let output5 : String = generate_x86_64(flatten_program(expose_basic_blocks(expose_basic_blocks::test1()))); 
   
   println!("{}",output5); 

}
