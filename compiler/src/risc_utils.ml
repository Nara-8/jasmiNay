open PrintCommon
open Arch_decl
open Utils
open Prog
open Var0
open Asm_utils
open PrintASM

let hash_to_string (to_string : 'a -> string) =
  let tbl = Hashtbl.create 17 in
  fun r ->
     try Hashtbl.find tbl r
     with Not_found ->
       let s = to_string r in
       Hashtbl.add tbl r s;
       s

let pp_imm imm_pre imm = Format.asprintf "%s%s" imm_pre (Z.to_string imm)

let pp_rip_address (p : Ssralg.GRing.ComRing.sort) : string =
  Format.asprintf "%s+%a" global_datas_label Z.pp_print (Conv.z_of_int32 p)

let pp_register arch = hash_to_string arch.toS_r.to_string

let pp_reg_address (arch:('a,'b,'c,'d,'e)arch_decl) (arch_name:string) pp_reg_address_aux addr =
  match addr.ad_base with
  | None ->
      failwith (Format.asprintf "TODO_%s: pp_reg_address" arch_name)
  | Some r ->
      let base = pp_register arch r in
      let disp = Conv.z_of_word (arch_pd arch) addr.ad_disp in
      let disp =
        if Z.equal disp Z.zero then None else Some (Z.to_string disp)
      in
      let off = Option.map (pp_register arch) addr.ad_offset in
      let scal = Conv.z_of_nat addr.ad_scale in
      let scal =
        if Z.equal scal Z.zero then None else Some (Z.to_string scal)
      in
      pp_reg_address_aux base disp off scal

let pp_address arch arch_name pp_reg_address_aux addr =
  match addr with
  | Areg ra -> pp_reg_address arch arch_name pp_reg_address_aux ra
  | Arip r -> pp_rip_address r 

let string_of_glob occurrences x =
  Hash.modify_def (-1) x.v_name Stdlib.Int.succ occurrences;
  let count =  Hash.find occurrences x.v_name in
  (* Adding the number of occurrences to the label to avoid names conflict *)
  let suffix = if count > 0 then Format.asprintf "$%d" count else "" in
  Format.asprintf "G$%s%s" (escape x.v_name) suffix


let format_glob_data globs names = 
    (* Creating a Hashtable to count occurrences of a label name*)
    let occurrences = Hash.create 42 in
    let names =
      List.map (fun ((x, _), p) -> (Conv.var_of_cvar x, Conv.z_of_cz p)) names
    in
    List.flatten
      (List.mapi
          (fun i b ->
            let b = Byte (Z.to_string (Conv.z_of_int8 b)) in
            match List.find (fun (_, p) -> Z.equal (Z.of_int i) p) names with
            | exception Not_found -> [ b ]
            | x, _ -> [ Label (string_of_glob occurrences x); b ])
          globs)


let pp_asm_arg arch arch_name pp_reg_address_aux  imm_pre (arg: ('a,Arch_utils.empty,Arch_utils.empty,'d,'e) asm_arg) =
  match arg with
  | Condt _ -> None
  | Imm (ws, w) -> Some (pp_imm imm_pre (Conv.z_of_word ws w))
  | Reg r -> Some (pp_register arch r)
  | Regx _ -> .
  | Addr addr -> Some (pp_address arch arch_name pp_reg_address_aux addr)
  | XReg _ -> .
