
open Prog
open Utils 
open PrintCommon
open Arch_decl 

type asm_element = 
| Header of string * string list
| Label of string
| Dwarf of string list (* Debug info in std dwarf format*)
| Instr of string * string list
| Comment of string
| Byte of string

let iwidth = 4

type asm = asm_element list

let pp_header fmt name params = 
  match params with 
  | [] -> Format.fprintf fmt "\t%s\n" name
  | _ ->  Format.fprintf fmt "\t%-*s\t%s\n" iwidth name (String.concat ", " params)

let pp_label fmt name =
  Format.fprintf fmt "%s:\n" name

let pp_instr fmt name params = 
  match params with 
  | [] -> Format.fprintf fmt "\t%s\n" name (* In case there is no params, we do not print a tab*)
  | _ ->  Format.fprintf fmt "\t%-*s\t%s\n" iwidth name (String.concat ", " params)

let pp_comment fmt comment = 
  Format.fprintf fmt "// %s\n" comment

let pp_byte fmt byte = 
  Format.fprintf fmt "\t.byte\t%s\n" byte

let pp_dwarf fmt (dwarf:string list) = 
  List.iter (Format.fprintf fmt "\t%s\n") dwarf

let pp_asm_element fmt asm_element = 
  match asm_element with
  | Header (name, params) -> 
    pp_header fmt name params
  | Label name ->
    pp_label fmt name
  | Dwarf locs ->
    pp_dwarf fmt locs
  | Instr (name, params) ->
    pp_instr fmt name params
  | Comment content ->
    pp_comment fmt content
  | Byte data ->
    pp_byte fmt data
  
let pp_asm fmt asm = 
  List.iter (pp_asm_element fmt) asm
