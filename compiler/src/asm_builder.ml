(* open Asm_printer

module type AsmTarget = sig 

  val headers : asm

end

module AsmBuilder = struct 

  module Make (Target:AsmTarget) = struct
    
    let pp_headers = Target.headers

    let pp_func func = 
      let head = Target.pp_func_head func in 
      let pre = Target.pp_func_pre func in
      let body = Target.pp_func_body func in
      let post = Target.pp_func_post func in
      head @ pre @ body @ post

    let pp_prog asm_prog = 
      let headers = Target.headers in 
      let funcs = List.map pp_func asm_prog in 
      let data_segment = Target.pp_data_segment asm_prog in
      headers @ List.flatten funcs @ data_segment

  end

end *)