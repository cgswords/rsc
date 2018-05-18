mod util;
//use util::Binop;
//use util::Relop;

mod generate_x86_64;
use generate_x86_64::generate_x86_64;

mod flatten_program;
use flatten_program::flatten_program;

mod expose_basic_blocks;
use expose_basic_blocks::expose_basic_blocks;

mod expose_memory_operands;
use expose_memory_operands::expose_memory_operands;

mod expose_frame_pointer;
use expose_frame_pointer::expose_frame_pointer;

mod expose_frame_variables;
use expose_frame_variables::expose_frame_variables;

mod finalize_locations;
use finalize_locations::finalize_locations;

mod discard_call_lives;
use discard_call_lives::discard_call_lives;

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

   let output6 = expose_memory_operands(expose_memory_operands::test1()); 
   
   println!("{:?}",output6); 

   let output7 : String = 
    generate_x86_64(
    flatten_program(
    expose_basic_blocks(
    expose_memory_operands(
      expose_memory_operands::test1())))); 
   
   println!("{}",output7); 

   let output8 = expose_frame_pointer(expose_frame_pointer::test1()); 
   
   println!("{:?}",output8); 

   let output9 : String = 
    generate_x86_64(
    flatten_program(
    expose_basic_blocks(
    expose_memory_operands(
    expose_frame_pointer(
      expose_frame_pointer::test1()))))); 
   
   println!("{}",output9);

   let output10 = expose_frame_variables(expose_frame_variables::test1()); 
   
   println!("{:?}",output10); 

   let output11 : String = 
    generate_x86_64(
    flatten_program(
    expose_basic_blocks(
    expose_memory_operands(
    expose_frame_pointer(
    expose_frame_variables(
      expose_frame_variables::test1())))))); 
   
   println!("{}",output11); 

   let output12 = finalize_locations(finalize_locations::test1()); 
   
   println!("{:?}",output12); 

   let output13 : String = 
    generate_x86_64(
    flatten_program(
    expose_basic_blocks(
    expose_memory_operands(
    expose_frame_pointer(
    expose_frame_variables(
    finalize_locations(
      finalize_locations::test1()))))))); 
   
   println!("{}",output13); 

   let output13 = discard_call_lives(discard_call_lives::test1()); 
   
   println!("{:?}",output13); 

   let output14 : String = 
    generate_x86_64(
    flatten_program(
    expose_basic_blocks(
    expose_memory_operands(
    expose_frame_pointer(
    expose_frame_variables(
    finalize_locations(
    discard_call_lives(
      discard_call_lives::test1())))))))); 
   
   println!("{}",output14); 
}
