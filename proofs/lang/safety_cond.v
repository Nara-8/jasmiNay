(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Export psem_safety.
Require Import expr.

Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
(* Open Scope vm_scope. *)

Section PEXP_SC.
Context {pd: PointerData}.

Definition emin_signed sz := Pconst (wmin_signed sz).
Definition emax_signed sz := Pconst (wmax_signed sz).
Definition ezero := Pconst 0.
Definition emax_unsigned sz := Pconst (wmax_unsigned sz).

(* Definition eint_of_wint sg sz e := Papp1 (Owi1 sg (WIint_of_word sz)) e. *)

Definition eint_of_word (sg:signedness) sz e := Papp1 (Oint_of_word sz) e.

Definition emuli e1 e2 := Papp2 (Omul Op_int) e1 e2.
Definition eaddi e1 e2 := Papp2 (Oadd Op_int) e1 e2.

Definition sc_lt e1 e2 := Papp2 (Olt Cmp_int) e1 e2.
Definition sc_le e1 e2 := Papp2 (Ole Cmp_int) e1 e2.
Definition sc_eq e1 e2 := Papp2 (Oeq Op_int) e1 e2.
Definition sc_not sc := Papp1 Onot sc.
Definition sc_neq e1 e2 := Papp2 (Oneq Op_int) e1 e2.
Definition sc_and sc1 sc2 :=  Papp2 Oand sc1 sc2.

Definition sc_in_range lo hi e := sc_and (sc_le lo e) (sc_le e hi).
Definition sc_uint_range sz e := sc_in_range ezero (emax_unsigned sz) e.
Definition sc_sint_range sz e := sc_in_range (emin_signed sz) (emax_signed sz) e.

(* This was commented. *)
Definition sc_wi_range sg sz e := signed (sc_uint_range sz) (sc_sint_range sz) sg e.

Definition sc_op1 (op1 : sop1) (e : pexpr) : seq pexpr :=
  [::].
  (* match op1 with
  | Owi1 sg o =>
    match o with
    | WIword_of_int sz => [:: sc_wi_range sg sz e]
    | WIint_of_word sz => [::]
    | WIword_of_wint sz => [::]
    | WIwint_of_word sz => [::]
    | WIword_ext szo szi => [::]
    | WIneg sz =>
        signed  [::sc_eq (eint_of_wint sg sz e) ezero ]
                [::sc_neq (eint_of_wint sg sz e) (emin_signed sz)] sg
    end
  | _ => [::]
  end. *)
(* 
Definition sc_wi_range_op2 sg sz op e1 e2 :=
  sc_wi_range sg sz (Papp2 op (eint_of_wint sg sz e1) (eint_of_wint sg sz e2)). *)

Definition sc_divmod sg sz e1 e2 :=
 let sc := if sg is Unsigned then [::]
           else [:: sc_not (sc_and (sc_eq e1 (emin_signed sz)) (sc_eq e2 (Pconst (-1)))) ] in
 [::sc_neq e2 ezero & sc].

(* Definition sc_wiop2 sg sz o e1 e2 :=
  match o with
  | WIadd => [:: sc_wi_range_op2 sg sz (Oadd Op_int) e1 e2]
  | WImul => [:: sc_wi_range_op2 sg sz (Omul Op_int) e1 e2]
  | WIsub => [:: sc_wi_range_op2 sg sz (Osub Op_int) e1 e2]
  | WIdiv => sc_divmod sg sz (eint_of_wint sg sz e1) (eint_of_wint sg sz e2)
  | WImod => sc_divmod sg sz (eint_of_wint sg sz e1) (eint_of_wint sg sz e2)
  | WIshl => [:: sc_wi_range sg sz (Papp2 (Olsl Op_int) (eint_of_wint sg sz e1) (eint_of_wint Unsigned U8 e2)) ]
  | WIshr => [::]
  | WIeq | WIneq | WIlt | WIle | WIgt | WIge  => [::]
  end. *)

Definition sc_op2 (o : sop2) e1 e2 :=
  match o with
  (* | Owi2 sg sz o => sc_wiop2 sg sz o e1 e2 *)
  | Odiv (Cmp_w sg sz) => sc_divmod sg sz (eint_of_word sg sz e1) (eint_of_word sg sz e2)
  | Omod (Cmp_w sg sz) => sc_divmod sg sz (eint_of_word sg sz e1) (eint_of_word sg sz e2)
  | _ => [::]
  end.

Definition sc_var_init (x:var_i) :=
  if is_sarr (vtype x) then [::]
  else [:: Pis_var_init x].

Definition sc_gvar_init x :=
  if is_lvar x then sc_var_init (gv x)
  else [::].

Definition eeq e1 e2 := Papp2 (Oeq Op_int) e1 e2.

Definition emod e1 e2 := Papp2 (Omod Cmp_int) e1 e2.

Definition ewsize sz := Pconst(wsize_size sz).

Definition eaddptr e1 e2 := Papp2 (Oadd (Op_w Uptr)) e1 e2.

Definition eis_aligned e sz :=
  let sc_align := emod e (ewsize sz) in
  eeq sc_align (Pconst 0).

Definition sc_is_aligned_if al aa sz e :=
  if (al == Unaligned) || (aa == AAscale) then [::]
  else 
  [:: eis_aligned e sz].

Definition emk_scale aa sz e :=
  if aa == AAdirect then e
  else emuli e (Pconst (wsize_size sz)).

Definition sc_in_bound ty aa sz elen e :=
  match ty with
  | sarr len =>
    let i := emk_scale aa sz e in
    [:: eand (sc_le ezero i) (sc_le (eaddi i elen) (Pconst len))]
  | _ => [::] (* assert false *)
  end.

Definition sc_arr_init (x:gvar) aa sz e :=
  if is_lvar x then
    let lo := emk_scale aa sz e in
   [:: Pis_arr_init x.(gv) lo (Pconst (wsize_size sz))]
  else [::].

Definition sc_arr_get (x:gvar) al aa sz e :=
  sc_is_aligned_if al aa sz e ++
  sc_in_bound (vtype (gv x)) aa sz (Pconst (wsize_size sz)) e ++
  sc_arr_init x aa sz e .

Definition sc_arr_set (x:var_i) al aa sz e :=
  sc_is_aligned_if al aa sz e ++
  sc_in_bound (vtype x) aa sz (Pconst (wsize_size sz)) e.

Definition sc_is_aligned_if_m al sz e :=
  if (al == Unaligned) then [::]
  else
  [:: eis_aligned (eint_of_word Unsigned Uptr e) sz].

Definition i_to_ptr i := Papp1 (Oword_of_int Uptr) (Pconst i).

Definition sc_mem_valid (e: pexpr) sz :=
  [:: Pis_mem_init e (wsize_size sz)].

Fixpoint sc_e (e : pexpr) : seq pexpr :=
  match e with
  | Pconst _ | Pbool _  | Parr_init _ => [::]
  | Pvar x => sc_gvar_init x
  | Pget al aa ws x e =>
    let sce := sc_e e in
    let sc_arr := sc_arr_get x al aa ws e in
    sce ++ sc_arr

  | Psub aa ws len x e =>
    let sce := sc_e e in
    let sc_arr := sc_in_bound (vtype (gv x)) aa ws (Pconst (arr_size ws len)) e in
    sce ++ sc_arr

  | Pload al ws x e =>
    let scx := sc_var_init x in
    let sce := sc_e e in
    let plo := eaddptr (Plvar x) e in
    let sca := sc_is_aligned_if_m al ws plo in
    let sc_load := sc_mem_valid plo ws in
    scx ++ sce ++ sca ++ sc_load

  | Papp1 op e1 =>
    let sce1 := sc_e e1 in
    let sco := sc_op1 op e1 in
    sce1 ++ sco

  | Papp2 op e1 e2 =>
    let sce1 := sc_e e1 in
    let sce2 := sc_e e2 in
    let sco := sc_op2 op e1 e2 in
    sce1 ++ sce2 ++ sco

  | PappN op es =>
    let scs := map sc_e es in
    flatten scs

  | Pif ty e e1 e2 =>
    let sce := sc_e e in
    let sce1 := sc_e e1 in
    let sce2 := sc_e e2 in
    sce ++ sce1 ++ sce2
  | Pbig idx op var e1 e2 e3  =>
    let scidx := sc_e idx in
    let sce1 := sc_e e1 in
    let sce2 := sc_e e2 in
    let sce3 := sc_e e3 in
    scidx ++ sce1 ++ sce2 ++ sce3 
  | Pis_var_init _ | Pis_arr_init _ _ _ | Pis_mem_init _ _ => [::e]
  end.

Definition sc_lval (lv : lval) : seq pexpr :=
  match lv with
  | Lnone _ _ => [::]
  | Lvar x => [::]
  | Lmem al ws x e =>
    let scx := sc_var_init x in
    let sce := sc_e e in
    let plo:= eaddptr (Plvar x) e in
    let sca := sc_is_aligned_if_m al ws plo in
    let sc_load := sc_mem_valid plo ws in
    scx ++ sce ++ sca ++ sc_load
  | Laset al aa ws x e =>
    let sce := sc_e e in
    let sc_arr := sc_arr_set x al aa ws e in
    sce ++ sc_arr
  | Lasub aa ws len x e =>
    let sce := sc_e e in
    let sc_arr := sc_in_bound (vtype x) aa ws (Pconst (arr_size ws len)) e in
    sce ++ sc_arr
  end.
End PEXP_SC.

Section CMD_SC.
Context {pd: PointerData} `{asmop: asmOp} (*  {A: Tabstract} {pT: progT} *)
  (fresh_var_ident: v_kind -> instr_info -> string -> stype -> Ident.ident).

Definition e_to_assert (e:pexpr) t : instr_r := Cassert t Cas e.

Definition instrr_to_instr (ii: instr_info) (ir: instr_r) : instr := MkI ii ir.

Definition sc_e_to_instr (sc_e : pexprs) (ii : instr_info): seq instr :=
  map (fun e => instrr_to_instr ii (e_to_assert e Assert)) sc_e.

Fixpoint sc_instr (i : instr) : cmd :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn lv _ _ e =>
    let sc_lv := sc_lval lv in
    let sc_e := sc_e e in
    sc_e_to_instr (sc_lv ++ sc_e) ii ++ [::i]
  | Copn lvs _ o es  => (*FIXME - Add safety conditions for o*)  
    let sc_lvs := conc_map sc_lval lvs in
    let sc_es := conc_map sc_e es in
    sc_e_to_instr (sc_lvs ++ sc_es) ii ++ [::i]
  | Csyscall lvs _ es
  | Ccall lvs _ es =>
    let sc_lvs := conc_map sc_lval lvs in
    let sc_es := conc_map sc_e es in
    sc_e_to_instr (sc_lvs ++ sc_es) ii ++ [::i]
  | Cif e c1 c2 =>
    let sc_e := sc_e e in
    let sc_c1 := conc_map sc_instr c1 in
    let sc_c2 := conc_map sc_instr c2 in
    let i := instrr_to_instr ii (Cif e sc_c1 sc_c2) in
    sc_e_to_instr (sc_e) ii ++ [::i]
  | Cfor x (d,e1,e2) c =>
    let sc_c := conc_map sc_instr c in    
    let sc_e := sc_e e1 ++ sc_e e2 in
    let i := instrr_to_instr ii (Cfor x (d,e1,e2) sc_c) in
    sc_e_to_instr (sc_e) ii ++ [::i]
  | Cwhile a c1 e c2 => 
    let sc_e := sc_e_to_instr (sc_e e) ii in
    let sc_c1 := conc_map sc_instr c1 ++ sc_e in
    let sc_c2 := conc_map sc_instr c2 in
    let i := instrr_to_instr ii (Cwhile a sc_c1 e sc_c2) in
    [::i]
  | Cassert _ _ e => [::i]
  end.

Definition sc_cmd (c : cmd) : cmd := conc_map sc_instr c.

Definition create_new_var (x:var_i) :=
  let x_info := x.(v_info) in
  let x := x.(v_var) in
  let x_type := x.(vtype) in
  let x_var := x.(vname) in
  let x := fresh_var_ident (Ident.id_kind x_var) dummy_instr_info (Ident.id_name x_var) x_type in
  let x := {| vtype := x_type; vname := x; |} in
  {|v_var:= x ; v_info:= x_info|}.

Definition generate_new_vars (x:seq var_i) : seq var_i :=
  map create_new_var x.

Definition create_new_var_range (name:string):=
  let x := fresh_var_ident (Reg (Normal, Direct)) dummy_instr_info name sint in
  let x := {| vtype := sint; vname := x; |} in
  {|v_var:= x ; v_info:= dummy_var_info|}.

Definition generate_assume_postc (x:var_i) (x':var_i): option pexpr :=
  match x.(v_var).(vtype) with
    | sarr n => 
      let i := create_new_var_range "k" in
      let ie := Plvar i in
      let body := Pif sbool ((Pis_arr_init x ie 1)) (Pis_arr_init x ie 1) (Pbool(true)) in
      Some (Pbig (Pbool true) Oand i body (Pconst 0) (Pconst n))    
    | _ => None
  end.

Fixpoint get_index (x:var_i) (l:seq var_i) i :=
  match l with
    | nil => None
    | h :: t => if var_beq x.(v_var) h.(v_var) then Some i
                  else get_index x t (S i)
  end.

Definition create_post_condition_array (f:_ufundef) : option fun_contract  :=
  let: (iparams,ires,pre,post) := 
    match f.(f_contra) with
    | None => 
      let iparams := generate_new_vars(f.(f_params)) in
      let ires := generate_new_vars(f.(f_res)) in
      (iparams, ires, [::], [::])
    | Some c => (c.(f_iparams), c.(f_ires), c.(f_pre), c.(f_post))
    end
  in
  let (postc_arrays,_) := foldl (fun acc x =>
    let: (acc,i') := acc in
    match get_index x f.(f_params) 0 with
      | None => (acc,S i')
      | Some i =>
        let x' := nth x ires i' in
        let x := nth x iparams i in
        let e := generate_assume_postc x x' in
        match e with
          | Some e => (acc ++ [::(Cas,e)], S i')
          | None => (acc, S i')
        end
    end
  ) ([::],Nat.zero) f.(f_res) in
  if Nat.eqb (List.length postc_arrays) Nat.zero then
    f.(f_contra) 
  else
    Some {|
      f_iparams := iparams;
      f_ires    := ires;
      f_pre := pre;
      f_post := post ++ postc_arrays
    |}.

Definition sc_func (f:_ufundef): _ufundef :=
  let sc_body := sc_cmd f.(f_body) in
  let es := conc_map (fun e => sc_var_init e) f.(f_res) in
  let sc_res := sc_e_to_instr es dummy_instr_info  in (*FIXME - Fix instruction info*)
  let sc_body := sc_body ++ sc_res in
  let new_contra := create_post_condition_array f in
  {|
    f_info   := f.(f_info) ;
    f_contra := new_contra ;
    f_tyin   := f.(f_tyin) ;
    f_params := f.(f_params) ;
    f_body   := sc_body ;
    f_tyout  := f.(f_tyout) ;
    f_res    := f.(f_res) ;
    f_extra  := f.(f_extra) ;
  |}.

Definition sc_prog (p:_uprog) : _uprog :=
  let sc_funcs := map (fun f => 
    match f with
     |(fn,fd) => (fn,(sc_func fd))
    end) p.(p_funcs) in
  {| p_globs := p.(p_globs) ;
     p_funcs := sc_funcs ;
     p_extra := p.(p_extra) ;
  |}.  
  
End CMD_SC.

Section ETYPE.
Local Existing Instance nosubword.
Context
  {A: Tabstract}
  {pabstract: Prabstract}
  {asm_op syscall_state: Type}
  {ep: EstateParams syscall_state}
  {spp: SemPexprParams}
  (* {pT: progT} (prog: prog) {dc: DirectCall} {sip: SemInstrParams asm_op syscall_state} *)
  (gd: glob_decls)
  (s: estate).


Definition gvtype (x:gvar) :=
  Let _ := assert (is_lvar x || is_ok (get_global gd (gv x))) tt in
  ok (vtype (gv x)).

Fixpoint etype (e : pexpr) : result unit stype :=
  match e with
  | Pconst _ => ok sint
  | Pbool _ => ok sbool
  | Parr_init len => ok (sarr len)
  | Pvar x => gvtype x
  | Pget al aa ws x e =>
    Let tx := gvtype x in
    Let te := etype e in
    Let _ := assert [&& is_sarr tx & subtype sint te] tt in
    ok (sword ws )
  | Psub aa ws len x e =>
    Let tx := gvtype x in
    Let te := etype e in
    Let _ := assert [&& is_sarr tx & subtype sint te] tt in
    ok (sarr (Z.to_pos (arr_size ws len)))
  | Pload al ws x e =>
    let tx := (vtype x) in
    Let te := etype e in
    Let _ := assert [&& subtype (sword Uptr) tx & subtype (sword Uptr) te] tt in
    ok (sword ws)
  | Papp1 op e1 =>
    Let te := etype e1 in
    let (tin, tout) := type_of_op1 op in
    Let _ := assert (subtype tin te) tt in
    ok tout
  | Papp2 op e1 e2 =>
    Let te1 := etype e1 in
    Let te2 := etype e2 in
    let: ((tin1, tin2), tout) := type_of_op2 op in
    Let _ := assert [&& subtype tin1 te1 & subtype tin2 te2] tt in
    ok tout
  | PappN op es =>
    Let tes := mapM etype es in
    let (tins, tout) := type_of_opNA op in (* Admit: Check if missing other cases (opN & opA) *)
    Let _ := assert (all2 subtype tins tes) tt in
    ok tout
  | Pif ty e e1 e2 =>
    Let te := etype e in
    Let te1 := etype e1 in
    Let te2 := etype e2 in
    Let _ := assert [&& subtype sbool te, subtype ty te1 & subtype ty te2] tt in
    ok ty
  | Pbig e op2 x e1 e2 e3 => (* Admit: TODO *)
    Let te := etype e in
    Let te1 := etype e1 in                                       
    Let te2 := etype e2 in
    Let te3 := etype e3 in
    let: ((tin1, tin2), tout) := type_of_op2 op2 in
    Let _ := assert [&& subtype tin1 te1 & subtype tin2 te2] tt in
    ok tout
  | Pis_var_init x =>
     ok sbool
  | Pis_arr_init x e1 e2 =>
    Let te1 := etype e1 in                                       
    Let te2 := etype e2 in
    ok sbool
  | Pis_mem_init e1 e2 =>
    Let te1 := etype e1 in                                       
    Let te2 := etype e2 in
    ok sbool
  end.

(*Needed for Pis_arr_init. TODO: Fix Definitions in psem_defs.v *)
Definition on_arr_var A (v:exec value) (f:forall n, WArray.array n -> exec A) :=
  Let v := v  in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.
Notation "'Let' ( n , t ) ':=' wdb ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var wdb s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).
(*-----*)

Definition sem_sc_err (sc : pexpr) :=
  match sc with
  | Pis_var_init x => ok (is_defined (evm s).[x])
      
  | Pis_mem_init lo hi =>
    Let wlo := sem_pexpr true gd s lo >>= to_word Uptr in
    Let whi := sem_pexpr true gd s hi >>= to_word Uptr in
    let lo := wunsigned wlo in
    let hi := wunsigned whi in
    let n := if (lo <=? hi) then (hi - lo + 1)
      else (wbase Uptr - lo) + hi + 1 in
      ok (all (fun i => is_ok (get (emem s) (wlo + wrepr Uptr i)%R)) (ziota 0 n))

    | Pis_arr_init x lo hi =>           
    Let (n, t) := true, s.[x] in
    Let lo := sem_pexpr true gd s lo >>= to_int in
    Let hi := sem_pexpr true gd s hi >>= to_int in
    ok (all (fun i => WArray.is_init t i) (ziota lo (hi - lo + 1)))

  | _ => ok false
  end.

Definition sem_scs_err := mapM sem_sc_err.

Definition sem_sc sc :=
  match sem_sc_err sc with
  | Ok b => b
  | _ => false
  end.

Definition sem_scs scs :=
  match sem_scs_err scs with
  | Ok bs => all id bs
  | _ => false
  end.

Fixpoint valid_scs (scs : seq pexpr) :=
  match scs with
  | [::] => True
  | sc :: scs => is_ok (sem_sc_err sc) /\ (sem_sc sc -> valid_scs scs)
  end.

(* Scs lemmas *)
Lemma scs_err_cat sc1 sc2 :
  is_ok (sem_scs_err (sc1 ++ sc2)) = is_ok (sem_scs_err sc1) && is_ok (sem_scs_err sc2).
Proof.
  rewrite /sem_scs_err mapM_cat.
  case: (mapM _ sc1) => //= b1.
  case: (mapM _ sc2) => //= b2.
Qed.

Lemma sem_scs_cat sc1 sc2 :
  sem_scs (sc1 ++ sc2) = (sem_scs sc1) && (sem_scs sc2).
Proof.
  rewrite /sem_scs /sem_scs_err mapM_cat.
  case: (mapM _ sc1) => //= b1.
  case: (mapM _ sc2) => //= b2.
  + by rewrite all_cat.
  by rewrite andbF.
Qed.

Lemma sem_scs_cons sc scs :  sem_scs (sc :: scs) = sem_sc sc && sem_scs scs.
Proof.
  rewrite /sem_scs /sem_sc /=.
  case: sem_sc_err => //= b; case: sem_scs_err => //=.
  by rewrite andbF.
Qed.

Lemma valid_scs_cat scs1 scs2 :
  valid_scs scs1 ->
  (sem_scs scs1 -> valid_scs scs2) ->
  valid_scs (scs1 ++ scs2).
Proof.
  elim: scs1 => [|sc1 scs1 hrec] /=.
  + by move=> _ /(_ (erefl true)).
  move=> [h1 h2] h; split => // hsc1.
  apply hrec.
  + by apply h2.
  by move=> hscs1; apply h; rewrite sem_scs_cons hsc1 hscs1.
Qed.

Lemma valid_scs_cat' scs1 scs2 :
  valid_scs scs1 ->
  valid_scs scs2 ->
  valid_scs (scs1 ++ scs2).
Proof. by move=> h1 h2; apply valid_scs_cat. Qed.

(* Safety Lemma: Pexp *)
Let P e :=
  forall ty, etype e = ok ty ->
  let sc := sc_e e in
  (sem_scs sc -> exists (v:sem_t ty), sem_pexpr true gd s e = ok (to_val v)).

Let Q es :=
  forall tys, mapM etype es = ok tys ->
  let sc := flatten (map sc_e es) in
  (sem_scs sc ->
   List.Forall2 (fun e ty => exists (v:sem_t ty), sem_pexpr true gd s e = ok (to_val v)) es tys).

(* Aux Lemmas Pexp *)
Opaque wsize_size.

Lemma is_def_type_of v :
  is_defined v →
  ∃ v' : sem_t (type_of_val v), v = (to_val v').
Proof. case: v => //=; eauto. Qed.

Lemma vtypeP x :
  valid_scs (sc_var_init x)
  ∧ (sem_scs (sc_var_init x) → ∃ v : sem_t (vtype x), get_var true (evm s) x = ok (to_val v)).
Proof.
  rewrite /get_var /sc_var_init.
  case: ifP.
  + move=> /is_sarrP [len h]; rewrite h; split => // _.
    by have := Vm.getP (evm s) x; rewrite h => /compat_valEl [? ->] /=; eauto.
  rewrite /sem_scs /= andbT => _; split => // hd /=.
  have := Vm.getP (evm s) x; rewrite /compat_val /= /compat_type /= hd.
  move=> /eqP <- /=.
  have [v -> ] := is_def_type_of _ hd.
  rewrite type_of_to_val; eauto.
Qed.

Lemma gvtypeP x ty :
  gvtype x = ok ty →
  [/\ ty = vtype (gv x)
    , valid_scs (sc_gvar_init x)
    & sem_scs (sc_gvar_init x) → ∃ v : sem_t ty, get_gvar true gd (evm s) x = ok (to_val v)].
Proof.
  rewrite /gvtype /sc_gvar_init /get_gvar; t_xrbindP => + <-.
  case: is_lvar => [_ | /= hget].
  + have [??] := vtypeP (gv x); split => //.
  split => // _.
  case heq: get_global hget => [v| //] _.
  rewrite -(type_of_get_global heq).
  Print get_global_defined.
  have [v' -> ] := is_def_type_of v (get_global_defined heq).
  rewrite type_of_to_val; eauto.
Qed.

Lemma  gvar_init_arr x len :
  vtype (gv x) = sarr len ->
  sem_scs (sc_gvar_init x).
Proof. by move=> h; rewrite /sc_gvar_init /sc_var_init h; case: ifP. Qed.

Lemma sc_is_aligned_ifP (i : sem_t sint) al aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs (sc_is_aligned_if al aa sz e) ->
  is_aligned_if (Pointer := WArray.PointerZ) al (i * mk_scale aa sz) sz.
Proof.
  rewrite /sc_is_aligned_if /is_aligned_if => hi.
  case: al => //=.
  case: aa => //=.
  by move=> _; apply WArray.is_align_scale.
Qed.

Lemma in_ziotaP i n m : reflect (n <= i < n + m)%Z (i \in ziota n m).
Proof.
  rewrite in_ziota.
  case: (ZleP n i) => /=.
  + case: (ZltP i (n + m)); constructor; Lia.lia.
  move=> ?; constructor; Lia.lia.
Qed.

Lemma sc_in_boundP len (i ilen : sem_t sint) aa sz (elen e : pexpr) :
  sem_pexpr true gd s elen = ok (to_val ilen) ->
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs (sc_in_bound (sarr len) aa sz elen e) ->
  (0 <= i * mk_scale aa sz /\ i * mk_scale aa sz + ilen <= len)%Z.
Proof. by[]. Qed.

Lemma sc_in_boundP_all len (t : sem_t (sarr len)) (i : sem_t sint) aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs (sc_in_bound (sarr len) aa sz (Pconst (wsize_size sz)) e) ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof. by[]. Qed.

Axiom ziota_add : forall p n, ziota p n = map (fun j => p + j) (ziota 0 n).

(* FIXME : this require a check *)
Axiom get_global_arr_init :
   forall x len (t:WArray.array len) ,
   get_global gd x = ok (Varr t) →
   all (λ j : Z, WArray.is_init t j) (ziota 0 len).

Lemma sc_arr_initP len (t : sem_t (sarr len)) (i : sem_t sint) x aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  get_gvar true gd (evm s) x = ok (to_val t) ->
  sem_scs (sc_arr_init x aa sz e) ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)) ->
  all (fun j => WArray.is_init t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof.
  rewrite /sc_arr_init /get_gvar /sem_scs /emk_scale /emuli /= => hi.
  case: ifP => /= hloc.
  + move=> -> /= + _.
Admitted.

Axiom subtype_of_val :
  forall ty1 ty2 (v : sem_t ty2),
    subtype ty1 ty2 ->
    exists2 v', of_val ty1 (to_val v) = ok v' & value_uincl (to_val v') (to_val v).

(* ASK: Idk why this was removed from word.v*)
Definition in_uint_range (sz : wsize) z :=
  assert (Z.leb 0 z && Z.leb z (wmax_unsigned sz)) (ErrArith).

Definition in_sint_range (sz : wsize) z :=
  assert (Z.leb (wmin_signed sz) z && Z.leb z (wmax_signed sz)) (ErrArith).

Definition signed {A:Type} (fu fs:A) s :=
  match s with
  | Unsigned => fu
  | Signed => fs
  end.

Definition in_wi_range (s : signedness) (sz : wsize) z :=
   signed in_uint_range in_sint_range s sz z.

Definition wint_of_int (s : signedness) (sz : wsize) (z : Z) :=
  Let _ := in_wi_range s sz z in
  ok (wrepr sz z).

Definition int_of_word (s : signedness) (sz : wsize) (w : word sz) :=
  signed wunsigned wsigned s w.
(* --- *)

Lemma sc_wi_rangeP (i : sem_t sint) sg sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs [:: sc_wi_range sg sz e] ->
  wint_of_int sg sz (Vint i) = ok (wrepr sz i).
Proof.
  rewrite /sem_scs/sc_wi_range /= /wint_of_int.
  by case: sg => /=.
Qed.

Lemma of_val_int i : of_val sint (Vint i) = ok i.
Proof. done. Qed.

Opaque of_val value_uincl subtype.

Lemma sc_divmodP_w ety1 ety2 e1 e2 sg (ve1 : sem_t ety1) (ve2 : sem_t ety2) w o:
  sem_pexpr true gd s e1 = ok (to_val ve1) ->
  sem_pexpr true gd s e2 = ok (to_val ve2) ->
  subtype (sword w) ety1 ->
  ∀ ve1' : word w,
  of_val (sword w) (to_val ve1) = ok ve1' ->
  value_uincl (Vword ve1') (to_val ve1) ->
  subtype (sword w) ety2 ->
  ∀ ve2' : word w,
  of_val (sword w) (to_val ve2) = ok ve2' ->
  value_uincl (Vword ve2') (to_val ve2) ->
  sem_scs (sc_divmod sg w (eint_of_word sg w e1) (eint_of_word sg w e2)) ->
  ∃ v : word w,
  Let r := mk_sem_divmod o ve1' ve2' in ok (Vword r) = ok (Vword v).
Proof.
  rewrite /sem_scs /sc_divmod /=.
  move=> he1 he2 /subtypeEl [sz1 [? hle1]]; subst ety1.
  move=> ve1' hof1 /value_uinclE [sz1'] [w1] [] /Vword_inj [?]; subst sz1' => /= ? hu1; subst w1.
  move=> /subtypeEl [sz2 [? hle2]]; subst ety2.
  move=> ve2' hof2 /value_uinclE [sz2'] [w2] [] /Vword_inj [?]; subst sz2' => /= ? hu2; subst w2.
  by rewrite /mk_sem_divmod; case: sg.
Qed.

Lemma wmax_signed_pos ws : (0 < wmax_signed ws)%Z.
Proof. by case: ws. Qed.

(* Removed from sem_type.v *)
Fixpoint sem_prod_ok {T: Type} (tin : seq stype) : sem_prod tin T -> sem_prod tin (exec T) :=
  match tin return sem_prod tin T -> sem_prod tin (exec T) with
  | [::] => fun o => ok o
  | t :: ts => fun o v => @sem_prod_ok T ts (o v)
  end.
Arguments sem_prod_ok {T}%type_scope tin%seq_scope _.

Fixpoint sem_forall {T: Type} (P: T -> Prop) (tin : seq stype) : sem_prod tin T -> Prop :=
  match tin return sem_prod tin T -> Prop with
  | [::] => P
  | t :: ts => fun o => forall v, @sem_forall T P ts (o v)
  end.
Arguments sem_forall {T}%type_scope P%function_scope tin%seq_scope _.

Lemma sem_prod_ok_ok {T: Type} (tin : seq stype) (o : sem_prod tin T) :
  sem_forall (fun et => exists t, et = ok t) tin (sem_prod_ok tin o).
Proof. elim: tin o => /= [o | a l hrec o v]; eauto. Qed.
(* --- *)

Lemma eq_sem_opNA_opN op : sem_opNA (OopN op) = sem_opN op.
Proof. by[]. Qed.

End ETYPE.
(*
Lemma etypeP_aux : (forall e, P e) /\ (forall es, Q es).
Proof.
  apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP => //.
  + by move=> _ <- _; constructor.
  + move=> e he es hes ? te /he{}he tes /hes {}hes <-.
    by rewrite sem_scs_cat => /andP[]/he{}he /hes{}hes; constructor.
  1-2: by move=> z ? <- _; exists z.
  + by move=> len _ <-; exists (WArray.empty len).
  + by move=> x ty /gvtypeP[???].

  (* Array access *)
  + move=> al aa sz x e he sty tx /gvtypeP [htx' okx hx] te /he{}he /andP[]/is_sarrP [len htx] /eqP ? <-.
    subst tx te.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and4P [hsce hal hbound hinit].
    have /hx := gvar_init_arr _ _ htx.
    rewrite htx => -[t ht]; have [i hi] := he hsce.
    rewrite ht /= hi /= /WArray.get /read /=.
    have -> /= := sc_is_aligned_ifP _ _ _ _ _ hi hal.
    move: hbound; rewrite htx => /(sc_in_boundP_all _ t _ _ _ _ hi) hbound.
    have {}hinit := sc_arr_initP _ _ _ _ _ _ _ hi ht hinit hbound.
    have : exists l, mapM (λ k : Z, WArray.get8 t (add (i * mk_scale aa sz) k)) (ziota 0 (wsize_size sz)) = ok l;
     last first.
    + by move=> [l -> /=]; eauto.
    elim: (ziota 0 (wsize_size sz)) hbound hinit => //=; eauto.
    move=> j js hrec /andP [h1 h2] /andP [h3 h4].
    rewrite {2}/WArray.get8 WArray.addE h1 /= h3 /=.
    by have [l -> /=] := hrec h2 h4; eauto.

  (* Subarray access *)
  + move=> aa sz len' x e he ? tx /gvtypeP [htx' okx hx] te /he{}he /andP []/is_sarrP [len htx] /eqP ? <-.
    subst tx te.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /andP [hsce hbound].
    have /hx := gvar_init_arr x len htx.
    rewrite htx => -[t ht]; have [i hi] := he hsce.
    rewrite ht /= hi /=.
    have helen : sem_pexpr true gd s (Pconst (arr_size sz len')) = ok (to_val (t:=sint) (arr_size sz len')) by done.
    move: hbound; rewrite htx => /(sc_in_boundP _ _ (arr_size sz len') _ _ (arr_size sz len') _ helen hi) []/ZleP h1 /ZleP h2.
    by rewrite /WArray.get_sub h1 h2 /=; eauto.

  (* Memory read *)
  + move=> al sz x e he ty te /he{}he /andP [hsubx hsube] <-.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and4P [hscx /he[ve{}he] hal hinit].
    have [_ /(_ hscx) [vx hvx]]:= vtypeP x.
    have [vx' hofx _]:= subtype_of_val (sword Uptr) (vtype x) vx hsubx.
    move/of_val_typeE: (hofx) => [wsx] [wx] [htox htrx].
    have [ve' hofe _]:= subtype_of_val (sword Uptr) te ve hsube.
    move/of_val_typeE: (hofe) => [wse] [we] [htoe htre].
    rewrite hvx he /= htox htoe /= htrx htre /=.
    rewrite /read /=.
    have -> /= : is_aligned_if al (vx' + ve')%R sz.
    + move: hal; rewrite /sc_is_aligned_if_m /sem_scs; case: al => //=.
    suff : [elaborate exists l, mapM (λ k : Z, get (emem s) (add (vx' + ve')%R k)) (ziota 0 (wsize_size sz)) = ok l].
    + by move=> [l -> /=]; eauto.
    move: hinit; rewrite /sem_scs /=.
    by rewrite /get_gvar /= hvx he /= /sem_sop2 /sem_sop1 /= hofx hofe /= truncate_word_u.

  (* Unary operator *)
  + move=> op e he ty ety; case heq: type_of_op1 => [tin tout].
    move=> /he{}he; t_xrbindP => hsub <-.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /andP [hsce hop].
    have [ve {}he /=] := he hsce; rewrite he /=.
    have [??]: tin = (type_of_op1 op).1 /\ tout = (type_of_op1 op).2 by rewrite heq.
    subst; rewrite /sem_sop1.
    have [ve' hve' huincl] := subtype_of_val (type_of_op1 op).1 ety ve hsub.
    rewrite hve' /= => {heq}.
    case: op hsub ve' hve' huincl hop => /=; try by eauto.

  (* Binary operator *)
  + move=> op e1 he1 e2 he2 ty ety1 /he1{}he1 ety2 /he2{}he2.
    case heq: type_of_op2 => [[tin1 tin2] tout].
    t_xrbindP => /andP[hsub1 hsub2] <-.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and3P [hsce1 hsce2 hop].
    have [ve1 {}he1 /=] := he1 hsce1; rewrite he1 /=.
    have [ve2 {}he2 /=] := he2 hsce2; rewrite he2 /=.
    have [???]: [/\ tin1 = (type_of_op2 op).1.1
                 , tin2 = (type_of_op2 op).1.2
                 & tout = (type_of_op2 op).2] by rewrite heq.
    subst; rewrite /sem_sop2.
    have [ve1' hve1' huincl1] := subtype_of_val _ _ ve1 hsub1.
    have [ve2' hve2' huincl2] := subtype_of_val _ _ ve2 hsub2.
    rewrite hve1' hve2' /= => {heq}.
    case: op hsub1 ve1' hve1' huincl1 hsub2 ve2' hve2' huincl2 hop => /=;
      try ((by eauto) || (by case => /=; eauto)).
    case => //=. move=> _ ve1' _ _ _ ve2' _ _ _. by exists (ve1' / ve2').
    move=> sg [] w hsub1 ve1' hof1 hu1 hsub2 ve2'; apply: sc_divmodP_w; eauto.
    case => //=. move=> _ ve1' _ _ _ ve2' _ _ _. by exists (ve1' mod ve2').
    move=> sg [] w hsub1 ve1' hof1 hu1 hsub2 ve2'; apply: sc_divmodP_w; eauto.
   
  (* N-ary opertors *)
 + admit.

  (* Conditional expression *)
 + move=> t e he e1 he1 e2 he2 ty te /he{}he te1 /he1{}he1 te2 /he2{}he2.
   move=> /and3P[] /subtypeEl ? hsub1 hsub2 ?; subst te t.
   rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and3P[].
   move=> {}/he [ve ->] /= {}/he1 [v1 ->] /= {}/he2 [v2 ->] /=.
   rewrite /truncate_val.
   have [v1' -> _]:= subtype_of_val ty te1 v1 hsub1.
   have [v2' -> _ /=]:= subtype_of_val ty te2 v2 hsub2.
   case: ve; eauto.

  (* Big expression *)
  admit.

  (* Init expressions *)
 + move=> x ty <-; rewrite /sem_scs /sem_scs_err /sem_sc_err //=.
   exists true; move: h0. by case (is_defined (evm s).[x]).
 + move=> x e1 he1 e2 he2 ? ty1 ety1 ty2 ety2 <-.
   rewrite /sem_scs /sem_scs_err /sem_sc_err //=. move=> H.
   exists true. specialize (he1 ty1 ety1).
 + admit.
Admitted.

Lemma etypeP : forall e, P e.
Proof. by case etypeP_aux. Qed.

Let Pv e :=
  forall ty, etype e = ok ty ->
  let sc := sc_e e in
  valid_scs sc.

Let Qv es :=
  forall tys, mapM etype es = ok tys ->
  let sc := flatten (map sc_e es) in
  valid_scs sc.

Lemma sc_wi_rangeP_safe sg sz e (ve : sem_t sint) :
  sem_pexpr true gd s e = ok (to_val ve) ->
  is_ok (sem_sc_err (sc_wi_range sg sz e)).
Proof.
  by move=> he; rewrite /sc_wi_range /sc_uint_range /sc_sint_range; case: sg.
Qed.

Lemma etypePv_aux : (forall e, Pv e) /\ (forall es, Qv es).
Proof.
  apply: pexprs_ind_pair; subst Pv Qv; split => //=; t_xrbindP => //.
  + by move=> e he es hes ? te {}/he he tes {}/hes/=hes _; apply valid_scs_cat.
  + by move=> x ty /= /gvtypeP[???].
  (* Array access *)
  + move=> al aa sz x e he ty tx /gvtypeP [htx' okx hx] te hte.
    have {}he := he _ hte.
    move=> /andP[]/is_sarrP [len htx] /subtypeEl ??; subst tx te ty.
    apply valid_scs_cat => // {}he.
    have [? {}he /=] := etypeP e _ hte he.
    rewrite /sc_arr_get; apply valid_scs_cat'; last apply valid_scs_cat'.
    + by rewrite /sc_is_aligned_if ; case: ifP.
    + by rewrite /sc_in_bound htx /sc_le /emk_scale /emuli /eaddi /ezero /=; split. 
    have /hx := gvar_init_arr x len htx.
    rewrite /get_gvar /sc_arr_init; case: ifP => //= _.
    rewrite htx => -[vx] ->; rewrite /emk_scale /emuli /eaddi /=.
    by case: ifP => //= _; rewrite he /sem_sop2 /= !of_val_to_val.

  (* Subarray access *)
  + move=> aa sz len' x e he ty tx /gvtypeP [htx' okx hx] te hte.
    have {}he := he _ hte.
    move=> /andP []/is_sarrP [len htx] /subtypeEl ??; subst tx te ty.
    apply valid_scs_cat => // {}he.
    have [? {}he /=] := etypeP e _ hte he.
    by rewrite /sc_in_bound htx /sc_le /emk_scale /emuli /eaddi /=; split.

  (* Memory read *)
  + move=> al sz x e he ty te hte /andP [hsubx hsube] ?; have {}he := he _ hte.
    have [hvx hx]:= vtypeP x.
    apply valid_scs_cat => // {}/hx [vx hx].
    have [vx' hofx _]:= subtype_of_val _ _ vx hsubx.
    move/of_val_typeE: (hofx) => [wsx] [wx] [htox htrx].
    apply valid_scs_cat => //.
    move=> /(etypeP e te hte) [ve {}he].
    have [ve' hofe _]:= subtype_of_val _ _ ve hsube.
    move/of_val_typeE: (hofe) => [wse] [we] [htoe htre]. 
    apply valid_scs_cat' => /=.
    - rewrite /sc_is_aligned_if_m; case: ifP => //=.
    - rewrite /get_gvar /= hx he /= /sem_sop2 /sem_sop1 /= hofx hofe /= truncate_word_u /=.
    admit.

  (* Unary operator *)
  + move=> op e he ty ety; case heq: type_of_op1 => [tin tout].
    move=> hte; t_xrbindP => hsub ?; subst ty.
    have {}he := he _ hte; apply valid_scs_cat => // /(etypeP hte) [ve {}he].

  (* Binary operator *)
  + move=> op e1 he1 e2 he2 ty ety1 hte1 ety2 hte2.
    case heq: type_of_op2 => [[tin1 tin2] tout].
    t_xrbindP => /andP[hsub1 hsub2] ?; subst ty.
    have [???]: [/\ tin1 = (type_of_op2 op).1.1
                 , tin2 = (type_of_op2 op).1.2
                 & tout = (type_of_op2 op).2] by rewrite heq.
    have {}he1 := he1 _ hte1; apply valid_scs_cat => // /(etypeP _ _ hte1) [ve1 {}he1].
    have {}he2 := he2 _ hte2; apply valid_scs_cat => // /(etypeP _ _ hte2) [ve2 {}he2].
    subst => {heq}.
    have [ve1' hve1' huincl1] := subtype_of_val _ _ ve1 hsub1.
    have [ve2' hve2' huincl2] := subtype_of_val _ _ ve2 hsub2.
    case: op hsub1 ve1' hve1' huincl1 hsub2 ve2' hve2' huincl2 => //=.
    by case. by case.
Admitted.

Lemma etypePv : forall e, Pv e.
Proof. by case etypePv_aux. Qed.

(* LVALUES *)
Definition ltype (l : lval) : result unit stype := (*TODO: Re-check this with Pl proof*)
  match l with
  | Lnone vinf sty => ok sty
  | Lvar vi => ok (vtype vi)
  | Lmem al ws x e =>
     let tx := vtype x in
     Let te := etype e in
     Let _ := assert [&& subtype (sword Uptr) tx & subtype (sword Uptr) te] tt in
     ok (sword ws)
  | Laset al aa ws x e =>
    let tx := vtype x in
    Let te := etype e in
    Let _ := assert [&& is_sarr tx & subtype sint te] tt in
    ok (sword ws)
  | Lasub aa ws len x e =>
    let tx := vtype x in
    Let te := etype e in
    Let _ := assert [&& is_sarr tx & subtype sint te] tt in
    ok (sarr (Z.to_pos (arr_size ws len)))
  end.
Definition ltypes := mapM ltype.

Lemma DB_to_val ty (v : sem_t ty) wdb : DB wdb (to_val v).
Proof. by case: ty v; rewrite /DB /= orbT. Qed.

Lemma compat_val_to_val ty (v : sem_t ty) : compat_val ty (to_val v).
Proof. by case: ty v => *; rewrite /compat_val /= eq_refl. Qed.

Let Pl l :=
  forall ty, ltype l = ok ty ->
  let: sc := sc_lval l in
  (sem_scs sc ->
   forall (v:sem_t ty), exists (s':estate), write_lval true gd l (to_val v) s = ok s').

Lemma ltypePl : forall l, Pl l.
Proof.
  subst Pl => /=. clear Q P Pv Qv.
  move=> [vi tynone ty | x ty | al ws x e ty | al aa ws x e ty | aa ws pos x e ty] /=.
  + (* Lnone *)
    move=> [->] _ v; exists s.
    by rewrite /write_none DB_to_val /= compat_val_truncatable // compat_val_to_val.
  + (* Lvar *)
    move=> [<-] _ v; rewrite /write_var /set_var DB_to_val /= compat_val_truncatable.
    by exists (with_vm s (evm s).[x <- to_val (t:=vtype x) v]).
    by apply compat_val_to_val.
  + (* Lmem *)
    t_xrbindP => z etyok /andP[sub1 sub2] <-. repeat rewrite sem_scs_cat.
    move=> /andP[varinit /andP[sce /andP[isalign memval]]] semt.
    rewrite /write.
  + (* Laset *)
  + (* Lasub *)
Admitted.

Let Plv l :=
  forall ty, ltype l = ok ty ->
  let sc := sc_lval l in
  valid_scs sc.

Lemma ltypePlv : forall l, Plv l.
Proof.
  rewrite /Plv /ltype => l ty H.
  case l as [vinf sty | vi | al ws x e | al aa ws x e | aa ws len x e] eqn:leq => //.
  move: H. t_xrbindP.
  (*Lmem*)
  have [hvx hx]:= vtypeP x.
  move=> ty2 etyok /andP[sub1 sub2] wordty.
  apply valid_scs_cat => // {}/hx [vx hx].
  
  case (etype e) as [ety|] eqn:eok.

  case (subtype (sword Uptr) (vtype x)) eqn:hsubx;
  case (subtype (sword Uptr) ety) eqn:hsube.
  
  have [vx' hofx _]:= subtype_of_val _ _ vx hsubx.
  move/of_val_typeE: (hofx) => [wsx] [wx] [htox htrx].

  have Hsce:= etypePv _ _ eok.
  apply valid_scs_cat => //.
  move=> /(etypeP _ _ eok) [ve {}he].  

  have [ve' hofe _]:= subtype_of_val _ _ ve hsube.
  move/of_val_typeE: (hofe) => [wse] [we] [htoe htre].
  apply valid_scs_cat' => //=.
  + rewrite /sc_is_aligned_if_m; case: ifP => //=.
    rewrite /get_gvar /= hx he /= /sem_sop2 /sem_sop1 /= hofx hofe /= truncate_word_u /=.
    admit. admit. admit. admit. admit.
    
  (*Laset*)  
Admitted.


Section CTYPE.
Context `{asmop: asmOp}.

Section ctype_aux.
Variable itype : instr -> result unit unit.
Fixpoint ctype_aux (c : cmd) : result unit unit :=
  match c with
  | [::] => ok tt
  | i :: cs =>
    Let _ := itype i in
    Let _ := ctype_aux cs in
    ok tt
  end.
End ctype_aux.

Fixpoint itype (i : instr) : result unit unit :=
  match i with
  | MkI ii ir => irtype ir
  end
with irtype (ir : instr_r) : result unit unit :=
  match ir with
  | Cassgn x tag ty e =>
      Let tx := ltype x in
      Let t := etype e in
      Let _ := assert (subtype ty t) tt in
      Let _ := assert (subtype tx ty) tt in
      ok tt
  | Copn xs t op es =>
      Let _ := ltypes xs in (* lvals compatible with the return type of op *)
      Let _ := mapM etype es in
      Error tt (* Never safe *)
  | Csyscall xs o es =>
      Let _ := ltypes xs in
      Let _ := mapM etype es in
      Error tt (* Never safe *)
  | Cif e c1 c2 =>
      Let t := etype e in
      Let _ := assert (is_sbool t) tt in
      Let _ := ctype_aux itype c1 in
      Let _ := ctype_aux itype c2 in            
      ok tt
  | Cfor i (d, lo, hi) c =>
      let _ := vtype i in
      Let _ := etype lo in
      Let _ := etype hi in
      Let _ := ctype_aux itype c in
      ok tt
  | Cwhile a c e c' => (* non termination? *)
      Let t := etype e in
      Let _ := assert (is_sbool t) tt in
      Let _ := ctype_aux itype c in
      Let _ := ctype_aux itype c' in
      ok tt
  | Ccall xs fn es => (* TODO: check that fn is safe *)
      Let _ := ltypes xs in
      Let _ := mapM etype es in
      Error tt (* until we check that fn is safe *)
  | Cassert ak ap e =>
      Let _ := etype e in
      ok tt
  end.

(* Auxiliary Lemmas
 --------------------------- *)
Lemma ctype_aux_inversion i c :
  ctype_aux itype (i :: c) = ok tt ->
  itype i = ok tt
  /\ ctype_aux itype c = ok tt.
Proof.
  move=> //= H.
  case: (itype i) H => [Hi|] H; [|discriminate].
  case: (ctype_aux itype c) H => [Hc|] H; [|discriminate].
  split.
  move: H; case: Hi; by [].
  move: H; case: Hc; by [].
Qed.

Lemma subtype_truncate_val_directly : (* ToDo? *)
  forall ty1 ty2 (v: value),
    subtype ty1 ty2 ->
    truncate_val ty2 v = ok v.
Proof.
  move=> ty1 ty2 v. Transparent subtype of_val.
  rewrite /subtype /truncate_val /of_val /to_val /sem_t.
  case ty1; case ty2; case v; move=>//=.
Admitted.


(* ----------- Instruction Validation ----------- *)

Let Piv i :=
  itype i = ok tt ->
  let sc := sc_i i in
  valid_scs sc.

Let Pcv c :=
  ctype c = ok tt ->
  let sc := sc_c c in
  valid_scs sc.


Lemma Pmkv ir ii: Prv ir -> Piv (MkI ii ir).
Proof.
  by move=> HPr.
Qed.

Lemma Pnilv : Pcv [::].
Proof.
  by [].
Qed.

Lemma Pconsv i c:  Piv i -> Pcv c -> Pcv (i::c).
Proof.
  rewrite /Pcv /Piv /ctype => Hiv Hcv Hok.
  have aux := ctype_aux_inversion Hok.
  case: aux => Hi Hc. move: (Hiv Hi) (Hcv Hc).
  apply valid_scs_cat'.
Qed.

Lemma Pasgnv l tag ty e : Prv (Cassgn l tag ty e).
Proof.
  subst Prv; rewrite /irtype.
  case (etype e) as [ety|] eqn: eok;
  case (ltype l) as [lty|] eqn: lok =>//=.
  have Hev := etypePv eok. have Hlv := ltypePlv lok.
  by move=> _; apply valid_scs_cat.
Qed.

Lemma Popnv xs t o es: Prv (Copn xs t o es).
Proof.
  by rewrite /irtype.
Qed.

Lemma Psyscallv xs o es: Prv (Csyscall xs o es).
Proof.
  by rewrite /irtype.
Qed.

Lemma Pifv e c1 c2: Pcv c1 -> Pcv c2 -> Prv (Cif e c1 c2).
Proof.
  rewrite /Pcv /Prv /ctype /irtype => Hc1 Hc2.
  case (etype e) as [ety|] eqn: eok =>//=;
  case ety eqn:eeq;
  case (ctype_aux itype c1) as [c1ty|] eqn:c1ok =>//=;
  case (ctype_aux itype c2) as [c2ty|] eqn:c2ok =>//=;
  try case c1ty eqn:c1eq; try case c2ty eqn:c2eq.
  have Hev := etypePv eok.
  move: (Hc1 Logic.eq_refl) (Hc2 Logic.eq_refl) => H1 H2.  
  by repeat (move=> _; apply valid_scs_cat).
  by rewrite c1ok c2ok.
  by rewrite c1ok.
  by rewrite c1ok.
Qed.

Lemma Pforv v dir lo hi c: Pcv c -> Prv (Cfor v (dir,lo,hi) c).
Proof.
  rewrite /Pcv /Prv /ctype /irtype => Hc.
  case (etype lo) as [loty|] eqn: look;
  case (etype hi) as [hity|] eqn: hiok;
  case (ctype_aux itype c) as [cty|] eqn:cok =>//=;
  try case cty eqn:ceq.
  have [hvx hx]:= vtypeP v;
  have Hlov := etypePv look; have Hhiv := etypePv hiok.
  move: (Hc Logic.eq_refl) => H.
  by repeat (move=> _; apply valid_scs_cat).
  by rewrite cok.
Qed.

Lemma Pwhilev a c e ei c': Pcv c -> Pcv c' -> Prv (Cwhile a c e ei c').
Proof.
  rewrite /Pcv /Prv /ctype /irtype =>  Hc Hc'.
  case (etype e) as [ety|] eqn: eok =>//=; case ety eqn:eeq;
  case (ctype_aux itype c) as [cty|] eqn:cok =>//=;
  case (ctype_aux itype c') as [c'ty|] eqn:c'ok =>//=;
  try case cty eqn:ceq; try case c'ty eqn:c'eq.
  have Hev:= etypePv eok.
  move: (Hc Logic.eq_refl) (Hc' Logic.eq_refl) => H1 H2.
  by repeat (move=> _; apply valid_scs_cat =>//=).
  by rewrite cok c'ok.
  by rewrite cok.
  by rewrite cok.
Qed.

Lemma Pcallv xs f es: Prv (Ccall xs f es).
Proof.
  rewrite /Prv /irtype.
  by case (mapM etype es) as [esty|] eqn: estyok;
  case (ltypes xs) as [lsty|] eqn: lstyok.
Qed.


(* ----------- Instruction Safety ----------- *)
Context
  {sCP: semCallParams}.
Variable ev : extra_val_t.

Let Pr ir :=
      forall ii, Pi (MkI ii ir).
   
Let Pi i :=
      itype i = ok tt ->
      let sc := sc_instr i in
      (sem_scs sc -> forall s, exists s', sem_I prog ev s i s').

Let Pc c :=
      ctype c = ok tt ->
      let sc := sc_c c in
      (sem_scs sc -> forall s, exists s', sem prog ev s c s').

Lemma Pmk ir ii: Pr ir -> Pi (MkI ii ir).
Proof.
  rewrite /Pr /Pi; move=> HPr Hitype s1 Hsemscs;
  specialize (HPr Hitype s1 Hsemscs) as [s2 Hs'];
  exists s2; by apply: EmkI.
Qed.

Lemma Pnil : Pc [::].
Proof.
  rewrite /Pc => Hctype Hsc s1; exists s1; by apply Eskip.
  Qed.

Lemma Pcons i c:  Pi i -> Pc c -> Pc (i::c).
Proof.
  rewrite /Pi /Pc. clear Pr Pi Pc. move=> HPi HPc Hctype Hsemscs s1.
  move: Hsemscs Hctype. rewrite /ctype.
  rewrite sem_scs_cat. move/andP => [Hsemsci Hsemscc].
  pose proof ctype_aux_inversion as aux. specialize (aux i c).
  move=> /aux [Hityok Hctyok].
  specialize (HPi Hityok Hsemsci s1) as [s2 H1].
  specialize (HPc Hctyok Hsemscc s2) as [s3 H2].
  exists s3. move: H1 H2; apply Eseq.
Qed.  
  
Lemma Pasgn l tag ty e: Pr (Cassgn l tag ty e).
Proof.
  rewrite /Pr. clear Pr Pi Pc.
  case (etype e) as [ety|] eqn:Hetyok.
  case: (ltype l) => [lty|] //=.
  case (assert (subtype ety ty) tt) => [asser|] //=. move=>_ {asser}.
  case (sc_l l). rewrite cat0s => H2.
  move=> s1. pose proof etypeP as HPaux.
  specialize (HPaux e ety Hetyok H2) as [semt_esty Hsem1].
  
  (* Should be able to solve like this:
  Exists (write_lval true gd lv v' s0). apply sem_Ind_mkI. sem_Ind_assgn.
  apply Eassgn. *)
Admitted.
  
Lemma Popn xs t o es: Pr (Copn xs t o es).
Proof.
  by subst Pr; rewrite /irtype;
  case (ltypes xs) as [lty|] eqn:ltyok;
  case (mapM etype es) as [esty|] eqn:estyok;
  try case lty eqn:ltyeq =>//=;
  try case esty eqn:esyeq =>//=.
Qed.

Lemma Psyscall xs o es: Pr (Csyscall xs o es).
Proof.
  by subst Pr; rewrite /irtype;
  case (ltypes xs) as [lty|] eqn:ltyok;
  case (mapM etype es) as [esty|] eqn:estyok;
  try case lty eqn:ltyeq =>//=;
  try case esty eqn:esyeq =>//=.
Qed.

Lemma Pif e c1 c2: Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
Proof.
  rewrite /Pc /Pr /ctype /sc_c. clear Pr Pi Pc.

  (* Induction on e. This line could be done later *)
  case (etype e) as [ety|] eqn:Hetyok => //=.

  (* Destruct H2 first *)
  move=> HPc1 HPc2 H1 + s1. (**)
  rewrite !sem_scs_cat;
  move/andP => [Hsemsce Hsem_aux];
               move/andP: Hsem_aux => [Hsemsc1 Hsemsc2].
  (* Use it on H1 *)
  move: H1. rewrite /assert; rewrite /is_sbool.
  rewrite Hetyok => //=.
  case ety eqn:etyeq => //=; rewrite <- etyeq in Hetyok.
  
  (* Getting Paux *)
  pose proof etypeP as HPaux.
  specialize (HPaux e ety Hetyok Hsemsce) as [v HPaux].
  
  (* TRYING: c1 *)
  case (ctype_aux itype c1) as [c1ty|] eqn:Hc1tyok.
  case c1ty eqn:c1tyis. subst (* Careful *).
  have okttrefl : ok tt = ok tt by [reflexivity]; specialize (okttrefl unit) (* Weird *). 
  specialize (HPc1 okttrefl Hsemsc1 s1) as [s2 HPc1].
  move=> _; exists s2.

  (* Final step of C1 *)
  move: HPaux HPc1.
  move: v; rewrite /sem_t => //=. move=> v; case: v.
  (* FAILS: gd and s are not the same. s should be s1.*)
  (* p_globs function to fix gd? *)

  (* TRYING: c2 *) (* TODO *)
  case (ctype_aux itype c2) as [c2ty|] eqn:Hc2tyok.
  case c2ty eqn:c2tyis; subst.  
Admitted.

Lemma Pfor v dir lo hi c: Pc c -> Pr (Cfor v (dir,lo,hi) c).
Proof.
Admitted.

Lemma Pwhile a c e ei c': Pc c -> Pc c' -> Pr (Cwhile a c e ei c').
Proof.
Admitted.

Lemma Pcall xs f es: Pr (Ccall xs f es).
Proof.
Admitted.

*)
