extern crate string_interner;

#[macro_use(lazy_static,__lazy_static_create,__lazy_static_internal)]
extern crate lazy_static;

extern crate petgraph;

mod util;
mod interner;
mod alloc_lang;

use alloc_lang::everybody_home;

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

mod discard_allocation_info;
use discard_allocation_info::discard_allocation_info;

mod finalize_instruction_selection;
use finalize_instruction_selection::finalize_instruction_selection;

mod assign_frame_variables;
use assign_frame_variables::assign_frame_variables;

mod assign_registers;
use assign_registers::assign_registers;

mod uncover_register_conflicts;
use uncover_register_conflicts::uncover_register_conflicts;

mod select_instructions;
use select_instructions::select_instructions;

mod finalize_alloc_locations;
use finalize_alloc_locations::finalize_alloc_locations;

mod assign_frame_args;
use assign_frame_args::assign_frame_args;

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

   let output15 = discard_allocation_info(discard_allocation_info::test1()); 
   
   println!("{:?}",output15); 

   let output16 : String = 
    generate_x86_64(
    flatten_program(
    expose_basic_blocks(
    expose_memory_operands(
    expose_frame_pointer(
    expose_frame_variables(
    finalize_locations(
    discard_call_lives(
    discard_allocation_info(
      discard_allocation_info::test1()))))))))); 
   
   println!("{}",output16); 

   let output17 = finalize_instruction_selection(finalize_instruction_selection::test1()); 
   
   println!("{:?}",output17); 

   let output18 : String = 
    generate_x86_64(
    flatten_program(
    expose_basic_blocks(
    expose_memory_operands(
    expose_frame_pointer(
    expose_frame_variables(
    finalize_locations(
    discard_call_lives(
    discard_allocation_info(
    finalize_instruction_selection(
      finalize_instruction_selection::test1())))))))))); 
   
   println!("{}",output18);

   let output19 = assign_frame_variables(assign_frame_variables::test::test1());
   
   println!("{:?}",output19);
   
   let output20 = everybody_home(&assign_frame_variables(assign_frame_variables::test::test1()));
   
   println!("Everybody home [19]: {:?}",output20);

   let output21 = assign_registers(assign_registers::test::test1());
   
   println!("{:?}",output21);
   
   let output22 = everybody_home(&assign_registers(assign_registers::test::test1()));
   
   println!("Everybody home [21]: {:?}",output22);

   let output23 = uncover_register_conflicts(uncover_register_conflicts::test::test1());
   
   println!("{:?}",output23);
   
   let output24 = select_instructions(select_instructions::test::test1());
   
   println!("{:?}",output24);
   
   let output25 = finalize_alloc_locations(finalize_alloc_locations::test::test1());
   
   println!("{:?}",output25);

   fn reg_alloc(input : alloc_lang::Program) -> alloc_lang::Program {
     let exp = assign_registers(uncover_register_conflicts(select_instructions(finalize_alloc_locations(input))));
     if everybody_home(&exp) {
       return exp;
     }
     reg_alloc(assign_frame_variables(exp))
   }

   fn lower_compiler(input : alloc_lang::Program) -> String {
     generate_x86_64(
     flatten_program(
     expose_basic_blocks(
     expose_memory_operands(
     expose_frame_pointer(
     expose_frame_variables(
     finalize_locations(
     discard_call_lives(
     discard_allocation_info(
     finalize_instruction_selection(input))))))))))
   }

   let output26 : String = lower_compiler(reg_alloc(finalize_alloc_locations::test::test1()));
   println!("{}",output26);

   let output27 : String = lower_compiler(reg_alloc(select_instructions::test::test1()));
   println!("{}",output27);

   let output28 = assign_frame_args(assign_frame_args::test::test1());
   println!("{:?}",output28);
}
